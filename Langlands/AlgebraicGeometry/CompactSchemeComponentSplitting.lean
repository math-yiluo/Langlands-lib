import Langlands.AlgebraicGeometry.AffineSchemeComponentSplitting
import Langlands.AlgebraicGeometry.ComponentFieldBaseChange
import Langlands.AlgebraicGeometry.ComponentOpenCoverGeometry
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! # Common finite fields for affine covers and compact component splitting -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

/-- The outer square of successive field scalar extensions is cartesian. -/
theorem isPullback_fieldBaseChangeTower (K E L : Type u) [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) :
    IsPullback
      (pullback.fst
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap K E))))
          (Spec.map (CommRingCat.ofHom (algebraMap E L))) ≫
        pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K E))))
      (pullback.snd
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap K E))))
        (Spec.map (CommRingCat.ofHom (algebraMap E L))))
      f (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  have hcomp : Spec.map (CommRingCat.ofHom (algebraMap E L)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K E)) =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
    rw [← Spec.map_comp]
    congr 1
    ext k
    exact (IsScalarTower.algebraMap_apply K E L k).symm
  rw [← hcomp]
  exact (IsPullback.of_hasPullback
    (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap K E))))
    (Spec.map (CommRingCat.ofHom (algebraMap E L)))).paste_horiz
      (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (algebraMap K E))))

/-- Successive scalar extensions along a field tower agree with direct extension. -/
def fieldBaseChangeTowerIso (K E L : Type u) [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) :
    pullback
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap K E))))
        (Spec.map (CommRingCat.ofHom (algebraMap E L))) ≅
      pullback f (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
  (isPullback_fieldBaseChangeTower K E L f).isoPullback

@[reassoc (attr := simp)]
theorem fieldBaseChangeTowerIso_hom_snd (K E L : Type u) [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) :
    (fieldBaseChangeTowerIso K E L f).hom ≫
        pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap K L))) =
      pullback.snd
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap K E))))
        (Spec.map (CommRingCat.ofHom (algebraMap E L))) := by
  exact (isPullback_fieldBaseChangeTower K E L f).isoPullback_hom_snd

/-- The compositum of the chosen affine splitting fields of an open cover. -/
def affineCoverComponentSplittingField (K : Type u) [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (𝒰 : Scheme.OpenCover.{v} X) [∀ i, IsAffine (𝒰.X i)] :
    IntermediateField K (SeparableClosure K) :=
  ⨆ i, affineSchemeComponentSplittingField K (𝒰.f i ≫ f)

theorem affineSchemeComponentSplittingField_le_affineCoverComponentSplittingField
    (K : Type u) [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] (𝒰 : Scheme.OpenCover.{v} X)
    [∀ i, IsAffine (𝒰.X i)] (i : 𝒰.I₀) :
    affineSchemeComponentSplittingField K (𝒰.f i ≫ f) ≤
      affineCoverComponentSplittingField K f 𝒰 :=
  le_iSup (fun i => affineSchemeComponentSplittingField K (𝒰.f i ≫ f)) i

theorem finite_affineCoverComponentSplittingField (K : Type u) [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (𝒰 : Scheme.OpenCover.{v} X) [Finite 𝒰.I₀] [∀ i, IsAffine (𝒰.X i)] :
    FiniteDimensional K (affineCoverComponentSplittingField K f 𝒰) := by
  have (i : 𝒰.I₀) : FiniteDimensional K
      (affineSchemeComponentSplittingField K (𝒰.f i ≫ f)) :=
    finite_affineSchemeComponentSplittingField K (𝒰.f i ≫ f)
  exact IntermediateField.finiteDimensional_iSup_of_finite

theorem separable_affineCoverComponentSplittingField (K : Type u) [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (𝒰 : Scheme.OpenCover.{v} X) [∀ i, IsAffine (𝒰.X i)] :
    Algebra.IsSeparable K (affineCoverComponentSplittingField K f 𝒰) :=
  inferInstance

/-- A common finite intermediate field for the canonical finite affine subcover
of a compact scheme. -/
def compactSchemeComponentSplittingField (K : Type u) [Field K]
    {X : Scheme.{u}} [CompactSpace X] (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] :
    IntermediateField K (SeparableClosure K) :=
  affineCoverComponentSplittingField K f X.affineCover.finiteSubcover

theorem finite_compactSchemeComponentSplittingField (K : Type u) [Field K]
    {X : Scheme.{u}} [CompactSpace X] (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] :
    FiniteDimensional K (compactSchemeComponentSplittingField K f) :=
  finite_affineCoverComponentSplittingField K f X.affineCover.finiteSubcover

theorem separable_compactSchemeComponentSplittingField (K : Type u) [Field K]
    {X : Scheme.{u}} [CompactSpace X] (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] :
    Algebra.IsSeparable K (compactSchemeComponentSplittingField K f) :=
  inferInstance

private theorem finite_components_affine_scalarExtension (K E : Type u)
    [Field K] [Field E] [Algebra K E] {X : Scheme.{u}} [IsAffine X]
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] :
    Finite (irreducibleComponents
      (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K E))) : Scheme.{u})) := by
  have : IsLocallyNoetherian
      (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K E)))) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap K E))))
  have : IsNoetherian
      (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K E)))) := ⟨⟩
  exact (finite_irreducibleComponents_of_isNoetherian).to_subtype

/-- The common field splits every actual component of the scalar extension
of the covered scheme. -/
theorem componentsGeometricallyIrreducible_affineCoverComponentSplittingField
    (K : Type u) [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] (𝒰 : Scheme.OpenCover.{v} X)
    [∀ i, IsAffine (𝒰.X i)] :
    ComponentsGeometricallyIrreducible
      (pullback.snd f (Spec.map (CommRingCat.ofHom
        (algebraMap K (affineCoverComponentSplittingField K f 𝒰))))) := by
  apply ComponentsGeometricallyIrreducible.of_openCover_baseChange f
    (Spec.map (CommRingCat.ofHom
      (algebraMap K (affineCoverComponentSplittingField K f 𝒰)))) 𝒰
  intro i
  let E := affineCoverComponentSplittingField K f 𝒰
  let F := affineSchemeComponentSplittingField K (𝒰.f i ≫ f)
  let φ : F →ₐ[K] E := IntermediateField.inclusion
    (affineSchemeComponentSplittingField_le_affineCoverComponentSplittingField K f 𝒰 i)
  let : Algebra F E := φ.toRingHom.toAlgebra
  have : IsScalarTower K F E := IsScalarTower.of_algHom φ
  have : Finite (irreducibleComponents
      (pullback (𝒰.f i ≫ f)
        (Spec.map (CommRingCat.ofHom (algebraMap K F))) : Scheme.{u})) :=
    finite_components_affine_scalarExtension K F (𝒰.f i ≫ f)
  have h := (componentsGeometricallyIrreducible_affineSchemeComponentSplittingField
    K (𝒰.f i ≫ f)).baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap F E)))
  exact h.of_iso (fieldBaseChangeTowerIso K F E (𝒰.f i ≫ f))
    (fieldBaseChangeTowerIso_hom_snd K F E (𝒰.f i ≫ f))

/-- The chosen common finite field splits every actual component for a compact
locally finite-type scheme over a field. -/
theorem componentsGeometricallyIrreducible_compactSchemeComponentSplittingField
    (K : Type u) [Field K] {X : Scheme.{u}} [CompactSpace X]
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] :
    ComponentsGeometricallyIrreducible
      (pullback.snd f (Spec.map (CommRingCat.ofHom
        (algebraMap K (compactSchemeComponentSplittingField K f))))) :=
  componentsGeometricallyIrreducible_affineCoverComponentSplittingField K f
    X.affineCover.finiteSubcover

/-- Compact locally finite-type field schemes admit a common finite separable
splitting field for all their actual reduced maximal components. -/
theorem exists_finite_separable_components_of_compactSpace
    (K : Type u) [Field K] {X : Scheme.{u}} [CompactSpace X]
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L),
      FiniteDimensional K L ∧ Algebra.IsSeparable K L ∧
      ComponentsGeometricallyIrreducible
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap K L)))) :=
  ⟨compactSchemeComponentSplittingField K f, inferInstance, inferInstance,
    finite_compactSchemeComponentSplittingField K f,
    separable_compactSchemeComponentSplittingField K f,
    componentsGeometricallyIrreducible_compactSchemeComponentSplittingField K f⟩

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
