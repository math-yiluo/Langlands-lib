/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedCompletionMatchingSections
public import WeilConjectures.RingTheory.FormalGlueingData

/-!
# Concrete section modules for affine chart transitions

## References

* Stacks Project, Tags 0BLH and 05EL, item (1)
* Stacks Project, Tag 0BLH, first two proof paragraphs
* Stacks Project, Tag 0BLH, first proof paragraph
* Stacks Project, Tag 0BLH, structural actions on affine charts
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData

/-- The localization acts through its canonical sections on D(f), followed by pullback.
No object is selected from an existence theorem. -/
noncomputable abbrev chartSectionModule {A : Type u} [CommRing A]
    {Y : Scheme.{u}} (h : Y ⟶ Spec (.of A)) (f : A) :
    ModuleCat.{u} (Localization.Away f) :=
  letI : Algebra A Γ(Spec (.of A), PrimeSpectrum.basicOpen f) :=
    inferInstanceAs (Algebra A ((Spec.structureSheaf A).obj.obj
      (Opposite.op (PrimeSpectrum.basicOpen f))))
  letI : IsLocalization.Away f Γ(Spec (.of A), PrimeSpectrum.basicOpen f) :=
    inferInstanceAs (IsLocalization.Away f ((Spec.structureSheaf A).obj.obj
      (Opposite.op (PrimeSpectrum.basicOpen f))))
  letI : Module (Localization.Away f) Γ(Y, h ⁻¹ᵁ PrimeSpectrum.basicOpen f) :=
    Module.compHom _ ((h.app (PrimeSpectrum.basicOpen f)).hom.comp
      (IsLocalization.algEquiv (Submonoid.powers f) (Localization.Away f)
        Γ(Spec (.of A), PrimeSpectrum.basicOpen f)).toRingEquiv.toRingHom)
  ModuleCat.of (Localization.Away f) Γ(Y, h ⁻¹ᵁ PrimeSpectrum.basicOpen f)

/-- Global completed sections with their structural action. -/
noncomputable abbrev completedSectionModule {C : Type u} [CommRing C]
    {E : Scheme.{u}} (s : E ⟶ Spec (.of C)) : ModuleCat.{u} C :=
  letI : Module C Γ(E, ⊤) :=
    Module.compHom _ ((ΓSpecIso (.of C)).inv ≫ s.appTop).hom
  ModuleCat.of C Γ(E, ⊤)

noncomputable section

set_option backward.isDefEq.respectTransparency false in
/-- The chosen localization action restricts to the structural action of A on sections. -/
theorem chartSectionModule_smul {A : Type u} [CommRing A] {Y : Scheme.{u}}
    (h : Y ⟶ Spec (.of A)) (f a : A)
    (m : Γ(Y, h ⁻¹ᵁ PrimeSpectrum.basicOpen f)) :
    (a • (show FormalGlueing.piece f (chartSectionModule h f) from m) :
      Γ(Y, h ⁻¹ᵁ PrimeSpectrum.basicOpen f)) = ((ΓSpecIso (.of A)).inv ≫ h.appTop ≫
      Y.presheaf.map (homOfLE (le_top : h ⁻¹ᵁ PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom a *
        (m : Γ(Y, h ⁻¹ᵁ PrimeSpectrum.basicOpen f)) := by
  let : Algebra A Γ(Spec (.of A), PrimeSpectrum.basicOpen f) :=
    inferInstanceAs (Algebra A ((Spec.structureSheaf A).obj.obj
      (Opposite.op (PrimeSpectrum.basicOpen f))))
  let : IsLocalization.Away f Γ(Spec (.of A), PrimeSpectrum.basicOpen f) :=
    inferInstanceAs (IsLocalization.Away f ((Spec.structureSheaf A).obj.obj
      (Opposite.op (PrimeSpectrum.basicOpen f))))
  change (h.app (PrimeSpectrum.basicOpen f)).hom
    ((IsLocalization.algEquiv (Submonoid.powers f) (Localization.Away f)
      Γ(Spec (.of A), PrimeSpectrum.basicOpen f)) (algebraMap A _ a)) *
      (m : Γ(Y, h ⁻¹ᵁ PrimeSpectrum.basicOpen f)) = _
  rw [AlgEquiv.commutes]
  change (((ΓSpecIso (.of A)).inv ≫
    (Spec (.of A)).presheaf.map (homOfLE le_top).op ≫
      h.app (PrimeSpectrum.basicOpen f)).hom a) * (m : Γ(Y, h ⁻¹ᵁ PrimeSpectrum.basicOpen f)) = _
  rw [h.naturality]
  rfl

end

end AlgebraicGeometry.Scheme.CompletionGluingData
