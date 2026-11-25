/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Projection.ProjectionCompactification
import WeilConjectures.AlgebraicGeometry.RingedRestrictionExchange.RingedOrdinaryOpenExchange

/-! # Ordinary inverse image preserves extension-by-zero support

## References

* Stacks Project, Tags 03DI, 04J0 and 09AE, ringed localization and extension by zero
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme

private theorem completeCoefficientIso {I : Sort*} {C : Type*} [Category C]
    (F : I → C) {i k : I} (h : i = k) {A B : C}
    (e : F i ≅ B) (p : F k ≅ A) :
    ∃ c : A ≅ B, HEq e (p ≪≫ c) := by
  subst k
  exact ⟨p.symm ≪≫ e, by simp⟩

/-- Inverse image of an ordinary extended module lies in the essential image of
extension from the pulled-back open. Only the three displayed coefficient
identifications are required; no module-pullback compositor is part of the statement. -/
theorem proEtaleRingPullback_openSupport {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (sq : IsPullback a j' j g)
    (RX : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (RU : Sheaf (ProEt.topology U) CommRingCat.{u + 1})
    (RX' : Sheaf (ProEt.topology X') CommRingCat.{u + 1})
    (RU' : Sheaf (ProEt.topology U') CommRingCat.{u + 1})
    (cj : (proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj RX ≅ RU)
    (cg : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj RX ≅ RX')
    (cj' : (proEtaleSheafInverseImage j' CommRingCat.{u + 1}).obj RX' ≅ RU')
    (M : proEtaleRingModules U RU) :
    (proEtaleRingOpenExtension j' RX' RU' cj').essImage
      ((proEtaleRingModulePullback g RX RX' cg).obj
        ((proEtaleRingOpenExtension j RX RU cj).obj M)) := by
  let cs : ChosenCartesianSquare j' a g j :=
    { toCommSq := sq.flip.toCommSq
      isoPullback := sq.flip.isoPullback
      hom_fst := sq.flip.isoPullback_hom_fst
      hom_snd := sq.flip.isoPullback_hom_snd }
  obtain ⟨ca, hc⟩ := completeCoefficientIso
    (fun f : U' ⟶ X ↦ (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj RX)
    sq.w.symm (proEtaleRingCompositeCoefficients j' g RX RX' RU' cg cj')
    ((proEtaleRingInverseImageComp a j).app RX ≪≫
      (proEtaleSheafInverseImage a CommRingCat.{u + 1}).mapIso cj)
  let r : StrictTowerRingedSquare cs :=
    { RY := RX
      RX := RX'
      RY' := RU
      RX' := RU'
      cf := cg
      cg := cj
      cg' := cj'
      cf' := ca
      coherent := by simpa only [proEtaleRingCompositeCoefficients, Iso.trans_assoc] using hc }
  have := RingedRestrictionExchange.ordinary_open_isIso r
  let β := asIso (RingedRestrictionExchange.ordinary r)
  let adj₁ := (Adjunction.ofIsRightAdjoint
    (proEtaleRingModulePullback j RX RU cj)).comp
      (proEtaleRingModuleAdjunction g RX RX' cg)
  let adj₂ := (proEtaleRingModuleAdjunction a RU RU' ca).comp
    (Adjunction.ofIsRightAdjoint (proEtaleRingModulePullback j' RX' RU' cj'))
  let e := (adj₁.ofNatIsoRight β).leftAdjointUniq adj₂
  exact ⟨(proEtaleRingModulePullback a RU RU' ca).obj M, ⟨(e.app M).symm⟩⟩

end AlgebraicGeometry.Scheme
