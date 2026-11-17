import Langlands.AlgebraicGeometry.AffineMorphismFiniteTypeFactorization
import Langlands.AlgebraicGeometry.GenericRetractionAffineNeighbourhood

/-! # Affine neighbourhoods from affine stalk models -/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace Langlands.AlgebraicGeometry

/-- An injective homomorphism of commutative rings induces a dominant
morphism of affine schemes. -/
theorem isDominant_specMap_of_injective
    {A B : Type u} [CommRing A] [CommRing B]
    (j : A →+* B) (hj : Function.Injective j) :
    IsDominant (Spec.map (CommRingCat.ofHom j)) := by
  constructor
  change DenseRange (PrimeSpectrum.comap j)
  apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical j).mpr
  rw [(RingHom.injective_iff_ker_eq_bot j).mp hj]
  exact bot_le

/-- An affine model inside the function field, with compatible maps from
the local schemes at a specified set of points. -/
structure AffineStalkModel
    {R : Type u} [CommRing R] {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of R)) (E : Set X) where
  ring : CommRingCat.{u}
  algebra : Algebra R ring
  domain : IsDomain ring
  hom : Spec ring ⟶ X
  over_base : hom ≫ p =
    Spec.map (CommRingCat.ofHom (@algebraMap R ring _ _ algebra))
  generic : Spec X.functionField ⟶ Spec ring
  dominant_generic : IsDominant generic
  generic_hom : generic ≫ hom = X.fromSpecStalk (genericPoint X)
  local_maps : ∀ x ∈ E, ∃ φ : Spec (X.presheaf.stalk x) ⟶ Spec ring,
    φ ≫ Spec.map (CommRingCat.ofHom (@algebraMap R ring _ _ algebra)) =
      X.fromSpecStalk x ≫ p ∧
    Spec.map (X.presheaf.stalkSpecializes (genericPoint_specializes x)) ≫ φ = generic

set_option backward.isDefEq.respectTransparency false in
/-- Finite-type approximation of an affine stalk model constructs a common
affine neighbourhood of the specified finite set. -/
def affineNeighbourhoodOfAffineStalkModel
    {R : Type u} [CommRing R] {X : Scheme.{u}} [IsIntegral X] [X.IsSeparated]
    (p : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFinitePresentation p]
    (E : Set X) (hE : E.Finite) (M : AffineStalkModel p E) :
    {U : X.Opens // IsAffineOpen U ∧ E ⊆ U} := by
  letI := M.algebra
  letI := M.domain
  letI := M.dominant_generic
  let D := finiteTypeAffineFactorization p M.hom M.over_base ∅
  let b : Spec M.ring ⟶ Spec (CommRingCat.of D.subalgebra) :=
    Spec.map (CommRingCat.ofHom D.subalgebra.val.toRingHom)
  let q : Spec (CommRingCat.of D.subalgebra) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R D.subalgebra))
  have : IsDominant b :=
    isDominant_specMap_of_injective D.subalgebra.val.toRingHom Subtype.val_injective
  have : Algebra.FiniteType R D.subalgebra :=
    (D.subalgebra.fg_iff_finiteType).mp D.fg
  have : LocallyOfFiniteType q := by
    apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  have hbq : b ≫ q = Spec.map (CommRingCat.ofHom (algebraMap R M.ring)) := by
    dsimp [b, q]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hgeneric : (M.generic ≫ b) ≫ D.hom =
      X.fromSpecStalk (genericPoint X) := by
    rw [Category.assoc]
    exact (congrArg (M.generic ≫ ·) D.factorization).trans M.generic_hom
  apply affineNeighbourhoodOfGenericRetraction p q D.hom D.over_base
    (M.generic ≫ b) hgeneric E hE
  intro x hx
  obtain ⟨φ, hφ, hη⟩ := M.local_maps x hx
  refine ⟨φ ≫ b, ?_, ?_⟩
  · rw [Category.assoc, hbq]
    exact hφ
  · rw [← Category.assoc, hη]

end Langlands.AlgebraicGeometry
