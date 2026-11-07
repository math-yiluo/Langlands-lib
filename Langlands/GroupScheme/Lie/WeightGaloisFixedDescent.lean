import Langlands.GroupScheme.Lie.GaloisFixedDescent
import Langlands.GroupScheme.Torus.WeightBaseChangeComparison
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! # Effective Galois descent of actual adjoint weight spaces -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

section WeightReflection

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

local notation "G_L" => CategoryTheory.Functor.obj (GroupScheme.baseChange (algebraBaseMap k L)) G

local instance : IsAffineHom (G_L).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k L))
  infer_instance

/-- The scalar-extended original weight span reflects membership of each
original vector. The quotient by that original weight space detects it. -/
theorem schemeScalarExtension_mem_extendedWeightSpace_iff
    (i : S.toGrp ⟶ G) (a : characterLattice S) (x : Additive (lieKernel G k)) :
    Lie.schemeScalarExtension (K := L) G (1 ⊗ₜ[k] x) ∈
        extendedWeightSpace (K := L) i a ↔ x ∈ weightSpace i a := by
  let W := weightSpace i a
  let e := Lie.schemeScalarExtension (K := L) G
  let q := W.mkQ
  let F := (q.baseChange L).comp e.symm.toLinearMap
  have hkill : extendedWeightSpace (K := L) i a ≤ LinearMap.ker F := by
    apply Submodule.span_le.mpr
    rintro _ ⟨z, hz, rfl⟩
    change q.baseChange L (e.symm (e (1 ⊗ₜ[k] z))) = 0
    rw [LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul]
    have hzq : q z = 0 := (Submodule.Quotient.mk_eq_zero W).mpr hz
    rw [hzq, TensorProduct.tmul_zero]
  constructor
  · intro hx
    have h := hkill hx
    change q.baseChange L (e.symm (e (1 ⊗ₜ[k] x))) = 0 at h
    rw [LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul] at h
    apply (Submodule.Quotient.mk_eq_zero W).mp
    change q x = 0
    simpa only [Module.FaithfullyFlat.one_tmul_eq_zero_iff] using h
  · intro hx
    exact Submodule.subset_span ⟨x, hx, rfl⟩

/-- Scalar extension preserves and reflects an original character's actual
weight-vector membership when the original acting torus is split. -/
theorem schemeScalarExtension_mem_weightSpace_iff
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G) (a : characterLattice S)
    (x : Additive (lieKernel G k)) :
    Lie.schemeScalarExtension (K := L) G (1 ⊗ₜ[k] x) ∈
      weightSpace ((GroupScheme.baseChange (algebraBaseMap k L)).map i)
        (characterLattice.baseChange (algebraBaseMap k L) S a) ↔
      x ∈ weightSpace i a := by
  rw [weightSpace_baseChange_eq_extendedWeightSpace hS i a]
  exact schemeScalarExtension_mem_extendedWeightSpace_iff i a x

end WeightReflection

namespace Lie

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (i : S.toGrp ⟶ G) (a : characterLattice S)

local notation "G_L" => CategoryTheory.Functor.obj (GroupScheme.baseChange (algebraBaseMap k L)) G
local notation "S_L" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k L)) S
local notation "i_L" => CategoryTheory.Functor.map (GroupScheme.baseChange (algebraBaseMap k L)) i
local notation "a_L" => characterLattice.baseChange (algebraBaseMap k L) S a

local instance : IsAffineHom (G_L).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k L))
  infer_instance

/-- The original character's actual base-changed weight vectors which are
fixed by the canonical ambient semilinear Galois action. -/
def baseChangeFixedWeightSpace : AddSubgroup (weightSpace (T := S_L) i_L a_L) where
  carrier := {x | ∀ σ : L ≃ₐ[k] L, baseChangeGaloisEquiv k L G σ x.val = x.val}
  zero_mem' := fun σ => (baseChangeGaloisEquiv k L G σ).map_zero
  add_mem' := by
    intro x y hx hy σ
    change baseChangeGaloisEquiv k L G σ (x.val + y.val) = x.val + y.val
    rw [(baseChangeGaloisEquiv k L G σ).map_add, hx σ, hy σ]
  neg_mem' := by
    intro x hx σ
    exact ((baseChangeGaloisEquiv k L G σ).map_neg x.val).trans (congrArg Neg.neg (hx σ))

variable [LocallyOfFiniteType G.X.hom] [IsGalois k L]

/-- Effective Galois descent restricts to every actual character weight space
of a split original torus, including the zero character. -/
def weightSpaceGaloisFixedEquiv (hS : IsSplitTorus S.toGrp) :
    weightSpace i a ≃+ baseChangeFixedWeightSpace k L i a := by
  let e := baseChangeFixedLieEquiv k L G
  have he (x : Additive (lieKernel G k)) :
      (e x).val = schemeScalarExtension (K := L) G (1 ⊗ₜ[k] x) := by
    rw [schemeScalarExtension_tmul, one_smul]
    rfl
  let f : weightSpace i a →+ baseChangeFixedWeightSpace k L i a :=
    { toFun := fun x => ⟨⟨(e x.val).val, by
        rw [he]
        exact weightSpace_baseChange_mem G i a x.property⟩, (e x.val).property⟩
      map_zero' := by
        apply Subtype.ext
        apply Subtype.ext
        change (e (0 : Additive (lieKernel G k))).val = 0
        exact congrArg (fun z : baseChangeFixedLie k L G => z.val) e.map_zero
      map_add' := by
        intro x y
        apply Subtype.ext
        apply Subtype.ext
        change (e (x.val + y.val)).val = (e x.val).val + (e y.val).val
        exact congrArg (fun z : baseChangeFixedLie k L G => z.val) (e.map_add x.val y.val) }
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      apply Subtype.ext
      apply e.injective
      apply Subtype.ext
      exact congrArg (fun z : baseChangeFixedWeightSpace k L i a => z.val.val) h
    · intro y
      let z : baseChangeFixedLie k L G := ⟨y.val.val, y.property⟩
      let x := e.symm z
      have hx : x ∈ weightSpace i a := by
        apply (schemeScalarExtension_mem_weightSpace_iff (L := L) hS i a x).mp
        rw [← he]
        have hxz : (e x).val = z.val := congrArg Subtype.val (e.apply_symm_apply z)
        rw [hxz]
        exact y.val.property
      refine ⟨⟨x, hx⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      change (e x).val = z.val
      exact congrArg (fun w : baseChangeFixedLie k L G => w.val) (e.apply_symm_apply z)
  exact AddEquiv.ofBijective f hf

@[simp]
theorem weightSpaceGaloisFixedEquiv_val (hS : IsSplitTorus S.toGrp)
    (x : weightSpace i a) :
    (weightSpaceGaloisFixedEquiv k L i a hS x).val.val =
      (baseChangeFixedLieEquiv k L G x.val).val := rfl

end Lie

end Langlands.GroupScheme
