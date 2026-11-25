/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Standard.StandardSingleFlatCounitPresentation
public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
import WeilConjectures.Algebra.Homology.BaseDerivedExtensionResolution
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
/-- Existence of the universal derived scalar-extension pair for a bounded-above
termwise-flat stalk complex under the affine presentation hypothesis.
Source: Stacks Project, Tags 0DJ9, 06YB and 0D5S.
Apply the general K-projective scalar-extension construction to the stalk ring map
and retain its universal pair. This pair exists independently of the input complex;
its boundedness and flatness hypotheses are not needed here.
(blueprint: lem-pc-standard-single-flat-counit-localization-pair). -/
theorem standardSingleFlatCounit_localization_pair
    (h_affine : ∀ {Y₀ B₀ A₀ : Scheme.{u}} (p₀ : Y₀ ⟶ B₀)
      [QuasiCompact p₀] [QuasiSeparated p₀] [IsAffine B₀] [IsAffine A₀]
      (g₀ : A₀ ⟶ B₀), StandardSingleFlatCounitOnOpen p₀ g₀ ⊤)
    {Y B A : Scheme.{u}} (p : Y ⟶ B) [QuasiCompact p] [QuasiSeparated p]
    (M : Y.Modules) [M.IsQuasicoherent] (hM : M.IsFlatOver p) (g : A ⟶ B) (a : A) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    let R := B.presheaf.stalk (g a)
    let T := A.presheaf.stalk a
    letI := HasDerivedCategory.standard (ModuleCat.{u} R)
    letI := HasDerivedCategory.standard (ModuleCat.{u} T)
    ∀ (P : CochainComplex (ModuleCat.{u} R) ℤ),
      (∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P.X i)) →
      (∀ i : ℤ, Module.Flat R (P.X i)) →
      ∃ (LF : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} T))
        (ε : DerivedCategory.Qh ⋙ LF ⟶
          (ModuleCat.extendScalars (g.stalkMap a).hom).mapHomotopyCategory (.up ℤ) ⋙
            DerivedCategory.Qh),
        LF.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)) := by
  have _ := @h_affine
  have _ := hM
  dsimp
  intro P hPbound hPflat
  let := HasDerivedCategory.standard
    (ModuleCat.{u} (B.presheaf.stalk (g a)))
  let := HasDerivedCategory.standard
    (ModuleCat.{u} (A.presheaf.stalk a))
  let : Algebra (B.presheaf.stalk (g a)) (A.presheaf.stalk a) :=
    (g.stalkMap a).hom.toAlgebra
  obtain ⟨LF, ε, hLF, _⟩ := ModuleCat.exists_baseDerivedExtension_resolution
    (B.presheaf.stalk (g a)) (A.presheaf.stalk a)
  exact ⟨LF, ε, hLF⟩
end AlgebraicGeometry
