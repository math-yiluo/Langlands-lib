import Langlands.GroupScheme.CentralIsogeny.Uniqueness
import Langlands.GroupScheme.CentralIsogeny.CommonRefinementConstruction
import Langlands.GroupScheme.Reductive.CommutingMultiplication

/-! # Commuting lifts through homomorphisms with finite kernel -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- A pointed morphism from a smooth connected affine group to a finite group scheme
is the constant identity morphism, over an arbitrary field. -/
theorem finiteTargetOverHom_eq_one
    (C F : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth C.X.hom] [IsAffineHom C.X.hom] [ConnectedSpace C.X.left]
    [IsFinite F.X.hom] (d : C.X ⟶ F.X)
    (hd : η[C.X] ≫ d = η[F.X]) : d = 1 := by
  let e := toAlgebraicClosure k
  let B := GroupScheme.baseChange e
  let P := Over.pullback e
  have hff : Flat e ∧ Surjective e :=
    (flat_and_surjective_SpecMap_iff
      (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  let : Flat e := hff.1
  let : Surjective e := hff.2
  let : P.Faithful := inferInstance
  let : Smooth (B.obj C).X.hom :=
    MorphismProperty.pullback_snd C.X.hom e inferInstance
  let : ConnectedSpace (B.obj C).X.left :=
    C.connectedSpace_baseChange_of_smooth_affine e
  let : IsReduced (B.obj C).X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      (AlgebraicClosure k) (B.obj C).X.left (B.obj C).X.hom
  let : IsFinite (B.obj F).X.hom :=
    MorphismProperty.pullback_snd F.X.hom e inferInstance
  have hd' : η[(B.obj C).X] ≫ P.map d = η[(B.obj F).X] := by
    change (Functor.LaxMonoidal.ε P ≫ P.map η[C.X]) ≫ P.map d =
      Functor.LaxMonoidal.ε P ≫ P.map η[F.X]
    rw [Category.assoc, ← P.map_comp, hd]
  have heq := finiteTargetOverHom_eq_one_algClosed (B.obj C) (B.obj F) (P.map d) hd'
  apply P.map_injective
  simpa only [Functor.map_one] using heq

variable {C D H G : GroupScheme (Spec (CommRingCat.of k))}

/-- Two homomorphisms with smooth connected affine sources commute on all tests
if their composites through a finite-kernel homomorphism commute. -/
theorem commute_of_finiteKernel
    (q : H ⟶ G) [IsFinite (kernel q).X.hom]
    (a : C ⟶ H) (b : D ⟶ H)
    (hC : IsConnectedReductive C) (hD : IsConnectedReductive D)
    (hc : ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ C.X) (y : T ⟶ D.X),
      Commute (x ≫ (a ≫ q).hom.hom) (y ≫ (b ≫ q).hom.hom)) :
    ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ C.X) (y : T ⟶ D.X),
      Commute (x ≫ a.hom.hom) (y ≫ b.hom.hom) := by
  have hcomp : commutatorMap a b ≫ q.hom.hom = 1 := by
    rw [← Category.id_comp (commutatorMap a b), commutatorMap_points]
    simp only [Category.id_comp, MonObj.mul_comp, GrpObj.inv_comp, Category.assoc,
      ← Grp.comp_hom_hom]
    have hh := (hc (C.X ⊗ D.X) (fst C.X D.X) (snd C.X D.X)).eq
    rw [hh]
    group
  let d : (C ⊗ D).X ⟶ (kernel q).X :=
    (kernelPointsEquiv q (C ⊗ D).X).symm ⟨commutatorMap a b, hcomp⟩
  have hd : d ≫ (kernelι q).hom.hom = commutatorMap a b :=
    congrArg Subtype.val ((kernelPointsEquiv q (C ⊗ D).X).apply_symm_apply _)
  have hd1 : η[(C ⊗ D).X] ≫ d = η[(kernel q).X] := by
    apply (cancel_mono (kernelι q).hom.hom).mp
    rw [Category.assoc, hd, IsMonHom.one_hom (kernelι q).hom.hom,
      commutatorMap_points]
    have hf : η[(C ⊗ D).X] ≫ fst C.X D.X = η[C.X] :=
      IsMonHom.one_hom (fst C D).hom.hom
    have hs : η[(C ⊗ D).X] ≫ snd C.X D.X = η[D.X] :=
      IsMonHom.one_hom (snd C D).hom.hom
    rw [hf, hs, IsMonHom.one_hom a.hom.hom, IsMonHom.one_hom b.hom.hom]
    simp only [MonObj.one_eq_one, mul_one, inv_one]
  obtain ⟨haff, -, -, hint⟩ := smoothConnectedAffineGeometry.2 k C D
    hC.smooth hC.isAffineHom hC.connectedSpace hD.smooth hD.isAffineHom hD.connectedSpace
  let : Smooth (C ⊗ D).X.hom := CommonRefinement.smooth_tensor hC.smooth hD.smooth
  let : IsAffineHom (C ⊗ D).X.hom := haff
  let : GeometricallyIntegral (C ⊗ D).X.hom := hint
  let : IsIntegral (C ⊗ D).X.left :=
    GeometricallyIntegral.isIntegral_of_subsingleton (C ⊗ D).X.hom
  have hdone : d = 1 := finiteTargetOverHom_eq_one (C ⊗ D) (kernel q) d hd1
  have hmap : commutatorMap a b = 1 := by
    rw [← hd, hdone, MonObj.one_comp]
  intro T x y
  have he : (x ≫ a.hom.hom) * (y ≫ b.hom.hom) *
      (x ≫ a.hom.hom)⁻¹ * (y ≫ b.hom.hom)⁻¹ = 1 := by
    rw [← commutatorMap_lift, hmap, MonObj.comp_one]
  apply (commute_iff_eq _ _).2
  exact (mul_inv_eq_iff_eq_mul).mp (mul_inv_eq_one.mp he)

/-- Combine the two lifted maps into an actual product homomorphism using only
commutation after a homomorphism with finite kernel. -/
def finiteKernelCommutingProduct
    (q : H ⟶ G) [IsFinite (kernel q).X.hom]
    (a : C ⟶ H) (b : D ⟶ H)
    (hC : IsConnectedReductive C) (hD : IsConnectedReductive D)
    (hc : ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ C.X) (y : T ⟶ D.X),
      Commute (x ≫ (a ≫ q).hom.hom) (y ≫ (b ≫ q).hom.hom)) : C ⊗ D ⟶ H :=
  commutingSubgroupMultiplicationHom a b (commute_of_finiteKernel q a b hC hD hc)

/-- The constructed product homomorphism multiplies the two original lifted points. -/
theorem finiteKernelCommutingProduct_points
    (q : H ⟶ G) [IsFinite (kernel q).X.hom]
    (a : C ⟶ H) (b : D ⟶ H)
    (hC : IsConnectedReductive C) (hD : IsConnectedReductive D)
    (hc : ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ C.X) (y : T ⟶ D.X),
      Commute (x ≫ (a ≫ q).hom.hom) (y ≫ (b ≫ q).hom.hom))
    (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ C.X) (y : T ⟶ D.X) :
    lift x y ≫ (finiteKernelCommutingProduct q a b hC hD hc).hom.hom =
      (x ≫ a.hom.hom) * (y ≫ b.hom.hom) :=
  comp_subgroupMultiplication a b x y

end Langlands.GroupScheme
