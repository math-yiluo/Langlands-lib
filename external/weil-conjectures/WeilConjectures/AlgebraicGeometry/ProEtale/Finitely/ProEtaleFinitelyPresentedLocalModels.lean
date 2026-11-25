/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
import Mathlib.Algebra.Module.FinitePresentation

/-! # Finitely presented local constant models on the pro-etale site

## References

* Stacks Project, Tags 09AJ and 093U
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- On every site object there is a covering sieve with finitely presented constant
module models on its members. This is the local clause of affine constructibility,
without choosing a scheme stratification. -/
def IsFinitelyPresentedLocallyConstantProEtaleModule {X : Scheme.{u}} {R : Type u} [CommRing R]
    (F : proEtaleRingModules X (proEtaleConstantRing X R)) : Prop :=
  ∀ V : X.ProEt, ∃ T : Sieve V, T ∈ ProEt.topology X V ∧
    ∀ (W : X.ProEt) (f : W ⟶ V), T f →
      ∃ M : ModuleCat.{u + 1} (ULift.{u + 1, u} R),
        Module.FinitePresentation (ULift.{u + 1, u} R) M ∧
          Nonempty (F.over W ≅ proEtaleConstantModuleSheafOver X R W M)

theorem IsFinitelyPresentedLocallyConstantProEtaleModule_of_iso
    {X : Scheme.{u}} {R : Type u} [CommRing R]
    {F G : proEtaleRingModules X (proEtaleConstantRing X R)} (e : F ≅ G)
    (hF : IsFinitelyPresentedLocallyConstantProEtaleModule F) :
    IsFinitelyPresentedLocallyConstantProEtaleModule G := by
  intro V
  obtain ⟨T, hT, h⟩ := hF V
  refine ⟨T, hT, fun W f hf ↦ ?_⟩
  obtain ⟨M, hM, ⟨i⟩⟩ := h W f hf
  exact ⟨M, hM, ⟨(SheafOfModules.overFunctor _ W).mapIso e.symm ≪≫ i⟩⟩

theorem IsFinitelyPresentedLocallyConstantProEtaleModule_of_isZero
    {X : Scheme.{u}} {R : Type u} [CommRing R]
    {F : proEtaleRingModules X (proEtaleConstantRing X R)} (hF : IsZero F) :
    IsFinitelyPresentedLocallyConstantProEtaleModule F := by
  intro V
  refine ⟨⊤, (ProEt.topology X).top_mem V, fun W f _ ↦ ?_⟩
  let Z := ModuleCat.of (ULift.{u + 1, u} R) PUnit.{u + 2}
  refine ⟨Z, inferInstance, ⟨?_⟩⟩
  have := (proEtaleConstantRingUnit_over_locallyBijective X R W).1
  have := (proEtaleConstantRingUnit_over_locallyBijective X R W).2
  have hP : IsZero (proEtaleConstantModulePresheaf (Over W) R Z) := by
    rw [IsZero.iff_id_eq_zero]
    apply PresheafOfModules.hom_ext
    intro U
    ext x
    change (x : PUnit.{u + 2}) = 0
    exact @Subsingleton.elim PUnit.{u + 2} inferInstance x 0
  have hz : IsZero (proEtaleConstantModuleSheafOver X R W Z) :=
    (PresheafOfModules.sheafification _).map_isZero hP
  have : (SheafOfModules.overFunctor.{u + 1}
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (proEtaleConstantRing X R)) W).Additive := ⟨fun {_ _} f g ↦ by rfl⟩
  exact ((SheafOfModules.overFunctor _ W).map_isZero hF).iso hz

end AlgebraicGeometry.Scheme
