import Langlands.Representation.Geometric.GeometricLemmaStatement
import Langlands.Representation.Geometric.StandardIntersectionsProof
import Langlands.Representation.Parabolic.RefinedJacquetTensor
import Langlands.Representation.Parabolic.RefinedInductionTensorProof
import Langlands.Representation.Tensor.ProductFiltration
import Langlands.Representation.Classification.SegmentSocleJacquetStatement
import Langlands.Representation.Classification.SegmentQuotientJacquetSingleBlock
import Langlands.Representation.Classification.LanglandsData
import Langlands.Representation.Induction.SingleBlock
import Langlands.Group.GL.OneBlockShape
import Langlands.Representation.CuspidalSupport.LeviSplitContraction
import Langlands.Representation.Classification.SegmentEdgeJacquetReduction

/-!
# The identity geometric piece of two overlapping segment socles
-/

noncomputable section

namespace Langlands.Classification.QuotientHom

open GeneralLinear Geometric CategoryTheory

universe uF uV

section Tensor

variable {G : Type*} [Monoid G] {U V W : Type*} [AddCommGroup U] [Module ℂ U]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- Pulling back along pointwise equal homomorphisms gives the same action. -/
def compEquivOfEq {H : Type*} [Monoid H] (ρ : Representation ℂ G V) {f g : H →* G}
    (h : ∀ x, f x = g x) : Representation.Equiv (ρ.comp f) (ρ.comp g) :=
  Representation.Equiv.mk (LinearEquiv.refl ℂ V) (fun x => by
    ext v
    simp [h x])

/-- Associativity of the tensor product of three actions of one group. -/
def tprodAssocEquiv (ρ : Representation ℂ G U) (σ : Representation ℂ G V)
    (τ : Representation ℂ G W) :
    (Representation.tprod (Representation.tprod ρ σ) τ).Equiv
      (Representation.tprod ρ (Representation.tprod σ τ)) :=
  Representation.Equiv.mk (TensorProduct.assoc ℂ U V W) (fun g => by
    apply TensorProduct.ext_threefold
    intro u v w
    simp [Representation.tprod_apply])

/-- An external tensor product over two factors is the tensor product of the two
factor actions pulled back along the coordinate projections. -/
def externalTwoEquiv {H : Fin 2 → Type*} [∀ i, Group (H i)] {X : Fin 2 → Type*}
    [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    (ρ : ∀ i, Representation ℂ (H i) (X i)) :
    (FiniteTensor.external ρ).Equiv
      (Representation.tprod ((ρ 0).comp (Pi.evalMonoidHom H 0))
        ((ρ 1).comp (Pi.evalMonoidHom H 1))) :=
  Representation.Equiv.mk
    ((FiniteTensor.headTailLinearEquiv ℂ X).trans
      (TensorProduct.congr (LinearEquiv.refl ℂ (X 0))
        (PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun j : Fin 1 => X j.succ) 0)))
    (fun g => by
      ext v
      simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
        LinearEquiv.coe_coe, LinearEquiv.trans_apply, FiniteTensor.external_tprod,
        FiniteTensor.headTailLinearEquiv_tprod, TensorProduct.congr_tmul,
        LinearEquiv.refl_apply, PiTensorProduct.subsingletonEquiv_apply_tprod,
        Representation.tprod_apply, TensorProduct.map_tmul, MonoidHom.coe_comp,
        Function.comp_apply, Pi.evalMonoidHom_apply]
      rfl)

end Tensor

section Entries

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The entries of an inner block of a refined Levi element are entries of its
ambient matrix. -/
theorem refinedLevi_entry (B : BlockShape n) (S : BlockRefinement B)
    (x : refinedLevi R B S) (i : Fin B.length) (t : Fin (S i).length)
    (a b : Fin ((S i).size t)) :
    (refinedLeviEquiv R B S).symm x i t a b =
      B.leviEmbedding R x.val
        (B.index i ((S i).index t a)) (B.index i ((S i).index t b)) := by
  conv_rhs => rw [← (refinedLeviEquiv R B S).apply_symm_apply x]
  change _ = B.leviEmbedding R (fun i => (S i).leviEmbedding R
    ((refinedLeviEquiv R B S).symm x i)) _ _
  rw [BlockShape.leviEmbedding_apply_same, BlockShape.leviEmbedding_apply_same]

/-- The outer blocks of a refined Levi element are entries of its ambient matrix. -/
theorem refinedLevi_outer_entry (B : BlockShape n) (S : BlockRefinement B)
    (x : refinedLevi R B S) (i : Fin B.length) (a b : Fin (B.size i)) :
    (S i).leviEmbedding R ((refinedLeviEquiv R B S).symm x i) a b =
      B.leviEmbedding R x.val (B.index i a) (B.index i b) := by
  conv_rhs => rw [← (refinedLeviEquiv R B S).apply_symm_apply x]
  change _ = B.leviEmbedding R (fun i => (S i).leviEmbedding R
    ((refinedLeviEquiv R B S).symm x i)) _ _
  rw [BlockShape.leviEmbedding_apply_same]

/-- Two refined Levi elements with the same ambient matrix have equal entries at
inner coordinates with the same ambient position. -/
theorem refinedLevi_entry_eq {B C : BlockShape n} {S : BlockRefinement B}
    {S' : BlockRefinement C} {x : refinedLevi R B S} {y : refinedLevi R C S'}
    (h : B.leviEmbedding R x.val = C.leviEmbedding R y.val)
    {i : Fin B.length} {t : Fin (S i).length} {i' : Fin C.length} {t' : Fin (S' i').length}
    {a b : Fin ((S i).size t)} {a' b' : Fin ((S' i').size t')}
    (ha : B.index i ((S i).index t a) = C.index i' ((S' i').index t' a'))
    (hb : B.index i ((S i).index t b) = C.index i' ((S' i').index t' b')) :
    (refinedLeviEquiv R B S).symm x i t a b = (refinedLeviEquiv R C S').symm y i' t' a' b' := by
  rw [refinedLevi_entry, refinedLevi_entry, h, ha, hb]

end Entries

section Transport

variable {F : Type uF} [CommRing F] {n : ℕ}

/-- Intersection transport at the identity permutation of a representation pulled
back to a monoid `P`, when the source and target coordinates agree on elements
with the same ambient matrix. -/
def intersectionTransportEquivOne (B C : BlockShape n) {P : Type*} [Monoid P]
    (ψB : sourceLevi F B C 1 →* P) (ψC : sourceLevi F C B 1⁻¹ →* P)
    (hψ : ∀ x y, B.leviEmbedding F x.val = C.leviEmbedding F y.val → ψB x = ψC y)
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (sourceLevi F B C 1) W) (ρ : Representation ℂ P V)
    (e : σ.Equiv (ρ.comp ψB)) :
    (intersectionTransport F B C 1 σ).Equiv (ρ.comp ψC) := by
  have key : ∀ m : sourceLevi F C B 1⁻¹,
      ψB ((intersectionLeviConjugation F B C 1).symm m) = ψC m := by
    intro m
    apply hψ
    rw [intersectionLeviConjugation_symm_embedding]
    simp only [map_one, inv_one, one_mul, mul_one]
  refine Representation.Equiv.mk e.toLinearEquiv ?_
  intro m
  apply LinearMap.ext
  intro v
  have he := LinearMap.congr_fun
    (e.isIntertwining' ((intersectionLeviConjugation F B C 1).symm m)) v
  change e (σ ((intersectionLeviConjugation F B C 1).symm m) v) = ρ (ψC m) (e v)
  change e (σ ((intersectionLeviConjugation F B C 1).symm m) v) =
    ρ (ψB ((intersectionLeviConjugation F B C 1).symm m)) (e v) at he
  rw [key] at he
  exact he

end Transport

end Langlands.Classification.QuotientHom
