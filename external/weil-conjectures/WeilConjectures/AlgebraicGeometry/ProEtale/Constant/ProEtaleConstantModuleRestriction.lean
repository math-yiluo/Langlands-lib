/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheafOfUniverses
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization

/-! # Restriction of localized constant module sheaves

## References

* Stacks Project, Sites Tag 00XR and Modules on Sites Tag 04IY
-/

@[expose] public section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A local constant model remains the same model on every smaller slice. -/
theorem proEtaleConstantModule_restrict (X : Scheme.{t}) (Λ : Type u) [CommRing Λ]
    (F : SheafOfModules.{max u (t + 1)}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
          ((constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).obj
            (CommRingCat.of (ULift.{t + 1, u} Λ)))))
    (U W : X.ProEt) (a : W ⟶ U)
    (M : ModuleCat.{max u (t + 1)} (ULift.{t + 1, u} Λ))
    (e : Nonempty (F.over U ≅ proEtaleConstantModuleSheafOverOfUniverses X Λ U M)) :
    Nonempty (F.over W ≅ proEtaleConstantModuleSheafOverOfUniverses X Λ W M) := by
  let J := ProEt.topology X
  let R := (sheafCompose J
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
      ((constantSheaf J CommRingCat.{max u (t + 1)}).obj
        (CommRingCat.of (ULift.{t + 1, u} Λ)))
  let α := Functor.whiskerRight (toSheafify J
    ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{t + 1, u} Λ))))
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})
  let αU := Functor.whiskerLeft (Over.forget U).op α
  let αW := Functor.whiskerLeft (Over.forget W).op α
  let L := Over.map a
  let : EssentiallySmall.{max u (t + 1)} (Over U) := essentiallySmallSelf _
  let : EssentiallySmall.{max u (t + 1)} (Over W) := essentiallySmallSelf _
  let : HasSheafify (J.over U) AddCommGrpCat.{max u (t + 1)} :=
    hasSheafifyEssentiallySmallSite _ _
  let : HasSheafify (J.over W) AddCommGrpCat.{max u (t + 1)} :=
    hasSheafifyEssentiallySmallSite _ _
  let : (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u (t + 1)} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  let : (J.over W).WEqualsLocallyBijective AddCommGrpCat.{max u (t + 1)} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  have := (proEtaleConstantRingUnit_over_locallyBijectiveOfUniverses X Λ U).1
  have := (proEtaleConstantRingUnit_over_locallyBijectiveOfUniverses X Λ U).2
  have := (proEtaleConstantRingUnit_over_locallyBijectiveOfUniverses X Λ W).1
  have := (proEtaleConstantRingUnit_over_locallyBijectiveOfUniverses X Λ W).2
  let P := proEtaleConstantModulePresheafOfUniverses (Over U) Λ M
  let Q := proEtaleConstantModulePresheafOfUniverses (Over W) Λ M
  let η := (PresheafOfModules.sheafificationAdjunction
    (J := J.over U) (R := R.over U) αU).unit.app P
  let G := (SheafOfModules.overMap R a).obj
    (proEtaleConstantModuleSheafOverOfUniverses X Λ U M)
  let g : Q ⟶ (PresheafOfModules.restrictScalars αW).obj G.val :=
    { app T := η.app (L.op.obj T)
      naturality {T T'} f := by
        ext x
        exact PresheafOfModules.naturality_apply η (L.op.map f) x }
  let ψ : proEtaleConstantModuleSheafOverOfUniverses X Λ W M ⟶ G :=
    (PresheafOfModules.sheafificationHomEquiv (J := J.over W) (R := R.over W) αW).symm g
  have hg : (J.over W).W ((PresheafOfModules.toPresheaf _).map g) := by
    change (J.over W).W (Functor.whiskerLeft L.op (toSheafify (J.over U) P.presheaf))
    have : Presheaf.IsLocallyInjective (J.over W)
        (Functor.whiskerLeft L.op (toSheafify (J.over U) P.presheaf)) :=
      Presheaf.isLocallyInjective_whisker (J.over W) (J.over U) L _
    have : Presheaf.IsLocallySurjective (J.over W)
        (Functor.whiskerLeft L.op (toSheafify (J.over U) P.presheaf)) :=
      Presheaf.isLocallySurjective_whisker (J.over W) (J.over U) L _
    exact (J.over W).W_of_isLocallyBijective _
  have : IsIso ψ := by
    rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf _)]
    dsimp only [ψ]
    rw [PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm,
      Adjunction.homEquiv_counit]
    have : IsIso ((presheafToSheaf (J.over W) AddCommGrpCat.{max u (t + 1)}).map
        ((PresheafOfModules.toPresheaf _).map g)) := by
      rw [(J.over W).W_eq_inverseImage_isomorphisms] at hg
      exact hg
    exact IsIso.comp_isIso' this
      (isIso_sheafificationAdjunction_counit
        (J := J.over W) (D := AddCommGrpCat.{max u (t + 1)})
        ((SheafOfModules.toSheaf (R.over W)).obj G))
  obtain ⟨e⟩ := e
  exact ⟨((SheafOfModules.overFunctorMap R a).app F).symm ≪≫
    (SheafOfModules.overMap R a).mapIso e ≪≫ (asIso ψ).symm⟩

end AlgebraicGeometry.Scheme
