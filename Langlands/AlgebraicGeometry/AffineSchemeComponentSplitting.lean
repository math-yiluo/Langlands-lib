import Langlands.AlgebraicGeometry.AffineFiniteSeparableComponentSplitting

/-! # Finite separable component splitting for arbitrary affine structure maps -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open TensorProduct

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

/-- Tensor spectra are the categorical scalar extension of the original spectrum. -/
def tensorSpecBaseChangeIso (K L A : Type u) [Field K] [Field L] [CommRing A]
    [Algebra K L] [Algebra K A] :
    Spec (.of (L ⊗[K] A)) ≅
      pullback (Spec.map (CommRingCat.ofHom (algebraMap K A)))
        (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
  (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct K L A)).flip.isoPullback

@[reassoc (attr := simp)]
theorem tensorSpecBaseChangeIso_hom_snd (K L A : Type u)
    [Field K] [Field L] [CommRing A] [Algebra K L] [Algebra K A] :
    (tensorSpecBaseChangeIso K L A).hom ≫
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap K A)))
          (Spec.map (CommRingCat.ofHom (algebraMap K L))) =
      Spec.map (CommRingCat.ofHom (algebraMap L (L ⊗[K] A))) := by
  exact (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct K L A)).flip.isoPullback_hom_snd

/-- A locally finite-type morphism between affine spectra admits a finite
separable intermediate field splitting its actual scalar-extended components. -/
theorem exists_finite_separable_components_of_SpecMap
    (K : Type u) [Field K] (A : CommRingCat.{u}) (φ : CommRingCat.of K ⟶ A)
    [LocallyOfFiniteType (Spec.map φ)] :
    ∃ E : IntermediateField K (SeparableClosure K), FiniteDimensional K E ∧
      ComponentsGeometricallyIrreducible
        (pullback.snd (Spec.map φ)
          (Spec.map (CommRingCat.ofHom (algebraMap K E)))) := by
  let : Algebra K A := φ.hom.toAlgebra
  have : Algebra.FiniteType K A :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := φ)).mp inferInstance
  obtain ⟨E, hE, hsplit⟩ := exists_finite_separable_tensor_components K A
  refine ⟨E, hE, ?_⟩
  exact hsplit.of_iso (tensorSpecBaseChangeIso K E A)
    (tensorSpecBaseChangeIso_hom_snd K E A)

/-- The categorical scalar extension of an arbitrary affine scheme has split
actual components after a finite separable intermediate extension. -/
theorem exists_finite_separable_components_of_isAffine
    (K : Type u) [Field K] {X : Scheme.{u}} [IsAffine X]
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] :
    ∃ E : IntermediateField K (SeparableClosure K), FiniteDimensional K E ∧
      ComponentsGeometricallyIrreducible
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap K E)))) := by
  let g := X.isoSpec.inv ≫ f
  obtain ⟨φ, hφ⟩ : ∃ φ, Spec.map φ = g := ⟨_, Spec.map_preimage _⟩
  have : LocallyOfFiniteType (Spec.map φ) := hφ.symm ▸ inferInstanceAs (LocallyOfFiniteType g)
  obtain ⟨E, hE, hsplit⟩ := exists_finite_separable_components_of_SpecMap K _ φ
  rw [hφ] at hsplit
  let e := Spec.map (CommRingCat.ofHom (algebraMap K E))
  have hbase : IsPullback (pullback.fst g e ≫ X.isoSpec.inv)
      (pullback.snd g e) f e := by
    apply (IsPullback.of_hasPullback g e).of_iso
      (Iso.refl _) X.isoSpec.symm (Iso.refl _) (Iso.refl _)
    · simp
    · simp
    · simp [g]
    · simp
  exact ⟨E, hE, hsplit.of_iso hbase.isoPullback hbase.isoPullback_hom_snd⟩

/-- A chosen finite intermediate splitting field for an affine structure map. -/
def affineSchemeComponentSplittingField (K : Type u) [Field K]
    {X : Scheme.{u}} [IsAffine X] (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] :
    IntermediateField K (SeparableClosure K) :=
  Classical.choose (exists_finite_separable_components_of_isAffine K f)

theorem finite_affineSchemeComponentSplittingField (K : Type u) [Field K]
    {X : Scheme.{u}} [IsAffine X] (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] :
    FiniteDimensional K (affineSchemeComponentSplittingField K f) :=
  (Classical.choose_spec (exists_finite_separable_components_of_isAffine K f)).1

theorem componentsGeometricallyIrreducible_affineSchemeComponentSplittingField
    (K : Type u) [Field K] {X : Scheme.{u}} [IsAffine X]
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] :
    ComponentsGeometricallyIrreducible
      (pullback.snd f (Spec.map (CommRingCat.ofHom
        (algebraMap K (affineSchemeComponentSplittingField K f))))) :=
  (Classical.choose_spec (exists_finite_separable_components_of_isAffine K f)).2

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
