/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsCanonicalAdjunctionSupplement
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.EssentialImage
import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenClosed
import Mathlib.Algebra.Homology.ExactSequence
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement

/-!
# Essential image of closed direct image on pro-etale module sheaves

## References

* Stacks Project, Pro-etale Cohomology, Tag 09AH
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
private noncomputable def coefficientDirectImageIso
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S) :
    (proEtaleScalarEquivalence X ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c)).functor ⋙
        proEtaleRingedDirectImage f R ≅ proEtaleRingModuleDirectImage f R S c := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · apply (SheafOfModules.fullyFaithfulForget _).preimageIso
    exact PresheafOfModules.isoMk (fun W ↦ Iso.refl _) (by intros; rfl)
  · intro M N a
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro W
    rfl

set_option backward.isDefEq.respectTransparency false in
private theorem pullback_isZero_iff_inverseImage
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (M : proEtaleRingModules Y R) :
    IsZero ((proEtaleRingModulePullback f R S c).obj M) ↔
      IsZero ((proEtaleModuleInverseImage f R).obj M) := by
  let rc := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c
  let e := proEtaleScalarEquivalence X rc
  let adj := proEtaleRingExtensionAdjunction f R S c
  let t := adj.leftAdjointUniq e.symm.toAdjunction
  constructor
  · intro h
    have hz : IsZero (e.inverse.obj ((proEtaleModuleInverseImage f R).obj M)) :=
      h.of_iso (t.app _).symm
    exact (e.functor.map_isZero hz).of_iso (e.counitIso.app _).symm
  · intro h
    exact (e.inverse.map_isZero h).of_iso (t.app _)

/-- Closed direct image has precisely the module sheaves with zero open restriction as
its essential image. On these sheaves the canonical module adjunction unit is invertible.
The arbitrary commutative coefficient sheaves and their inverse-image identifications are
fixed explicitly; the unit is that of the tensor-unit-normalized adjunction. -/
theorem proEtaleRingModule_closed_essImage_iff_and_unit_isIso
    {X Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hU : Set.range j = (Set.range i)ᶜ)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (Ri : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (Rj : Sheaf (ProEt.topology U) CommRingCat.{u + 1})
    (ci : (proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R ≅ Ri)
    (cj : (proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj R ≅ Rj)
    (F : proEtaleRingModules X R) :
    ((proEtaleRingModuleDirectImage i R Ri ci).essImage F ↔
      IsZero ((proEtaleRingModulePullback j R Rj cj).obj F)) ∧
    (IsZero ((proEtaleRingModulePullback j R Rj cj).obj F) →
      IsIso ((proEtaleRingModuleAdjunction i R Ri ci).unit.app F)) := by
  let V := ProEt.mk j
  have : IsOpenImmersion V.hom := ‹IsOpenImmersion j›
  have : QuasiCompact V.hom := ‹QuasiCompact j›
  obtain ⟨q, ⟨e⟩, ai, aj, hc, _, hz, _, _, _, _, _, hs, _⟩ :=
    proEtale_ringed_open_closed i V hU R
  let ei := proEtaleScalarEquivalence Z ((sheafCompose (ProEt.topology Z)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso ci)
  let d := coefficientDirectImageIso i R Ri ci
  have : IsIso ai.counit := by
    have := hc
    exact NatIso.isIso_of_isIso_app _
  have : (proEtaleRingedDirectImage i R).Full := ai.fullyFaithfulROfIsIsoCounit.full
  have : (proEtaleRingedDirectImage i R).Faithful := ai.fullyFaithfulROfIsIsoCounit.faithful
  have : (proEtaleRingModuleDirectImage i R Ri ci).Full := Functor.Full.of_iso d
  have : (proEtaleRingModuleDirectImage i R Ri ci).Faithful := Functor.Faithful.of_iso d
  have hres (M : proEtaleRingModules X R) :
      IsZero ((proEtaleRingModulePullback j R Rj cj).obj M) ↔
        IsZero ((SheafOfModules.overFunctor.{u + 1}
          (proEtaleModuleCoefficients R) V).obj M) := by
    rw [pullback_isZero_iff_inverseImage]
    constructor
    · intro h
      exact (q.functor.map_isZero h).of_iso (e.app M).symm
    · intro h
      have hq := h.of_iso (e.app M)
      exact (q.inverse.map_isZero hq).of_iso (q.unitIso.app _)
  have hiff : (proEtaleRingModuleDirectImage i R Ri ci).essImage F ↔
      IsZero ((proEtaleRingModulePullback j R Rj cj).obj F) := by
    constructor
    · rintro ⟨G, ⟨g⟩⟩
      apply (hres F).2
      exact (hz (ei.functor.obj G)).of_iso
        ((SheafOfModules.overFunctor.{u + 1} (proEtaleModuleCoefficients R) V).mapIso
          ((d.app G ≪≫ g).symm))
    · intro h
      have ho := (hres F).1 h
      have : (proEtaleRingedExtensionByZero V R).IsLeftAdjoint := aj.isLeftAdjoint
      have hleft := (proEtaleRingedExtensionByZero V R).map_isZero ho
      let T := ComposableArrows.mk₂ (aj.counit.app F) (ai.unit.app F)
      have hT : T.Exact := (hs F).2.2
      have he := (T.exact₂_iff hT.toIsComplex).1 hT
      have : Mono (ai.unit.app F) := he.mono_g (hleft.eq_of_src _ _)
      have : Epi (ai.unit.app F) := (hs F).2.1
      have : IsIso (ai.unit.app F) := isIso_of_mono_of_epi _
      refine ⟨ei.inverse.obj ((proEtaleModuleInverseImage i R).obj F), ⟨?_⟩⟩
      exact (d.app _).symm ≪≫
        (proEtaleRingedDirectImage i R).mapIso (ei.counitIso.app _) ≪≫
          (asIso (ai.unit.app F)).symm
  refine ⟨hiff, fun h ↦ ?_⟩
  exact (proEtaleRingModuleAdjunction i R Ri ci).isIso_unit_app_iff_mem_essImage.2
    (hiff.2 h)

end AlgebraicGeometry.Scheme
