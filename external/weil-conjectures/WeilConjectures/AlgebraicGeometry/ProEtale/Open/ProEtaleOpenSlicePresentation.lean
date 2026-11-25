/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Projection.ProjectionCompactification
public import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent

import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenComparison

/-! # The slice presentation of extension by zero on the small pro-etale site

## References

* Stacks Project, Tags 09BN, 00XZ, 03DI and 03DJ
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme

/-- Actual extension by zero is an equivalence followed by literal slice extension.
There is no quasi-compactness hypothesis and the coefficient ring sheaves are arbitrary. -/
theorem proEtaleOpen_slicePresentation {U V : Scheme.{u}} (j : U ⟶ V)
    [IsOpenImmersion j]
    (RV : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (RU : Sheaf (ProEt.topology U) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj RV ≅ RU) :
    ∃ e : proEtaleRingModules U RU ≌
        SheafOfModules.{u + 1} (((sheafCompose (ProEt.topology V)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RV).over (ProEt.mk j)),
      Nonempty (proEtaleRingOpenExtension j RV RU c ≅ e.functor ⋙
        SheafOfModules.localizedModuleExtension.{u} RV (ProEt.mk j)) := by
  let W := ProEt.mk j
  have : IsOpenImmersion W.hom := inferInstanceAs (IsOpenImmersion j)
  obtain ⟨q, ⟨hq⟩⟩ := proEtale_ringed_open_comparison W RV
  let L := SheafOfModules.localizedModuleExtension.{u} RV W
  let a := SheafOfModules.localizedModuleAdjunctionIndependent.{u} RV W
  let ef : proEtaleModuleInverseImage j RV ≅
      SheafOfModules.localizedModuleRestriction.{u} RV W ⋙ q.inverse :=
    (Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft _ q.unitIso ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight hq q.inverse
  let af : q.functor ⋙ L ⊣ proEtaleModuleInverseImage j RV :=
    (q.toAdjunction.comp a).ofNatIsoRight ef.symm
  let rc := (sheafCompose (ProEt.topology U)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c
  let e := proEtaleScalarEquivalence U rc
  let ae := proEtaleRingExtensionAdjunction
    j RV RU c
  let ei := ae.leftAdjointUniq e.symm.toAdjunction
  let ae' : e.functor ⊣ proEtaleRingExtension j RV RU c :=
    e.toAdjunction.ofNatIsoRight ei.symm
  let ap : (e.trans q).functor ⋙ L ⊣
      proEtaleRingModulePullback j RV RU c := ae'.comp af
  exact ⟨e.trans q, ⟨(Adjunction.ofIsRightAdjoint
    (proEtaleRingModulePullback j RV RU c)).leftAdjointUniq ap⟩⟩

end AlgebraicGeometry.Scheme
