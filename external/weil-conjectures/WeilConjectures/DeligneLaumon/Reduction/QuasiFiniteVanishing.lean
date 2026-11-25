/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.AlgebraicGeometry.Morphisms.QuasiFiniteFactorization
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.WeilSheaf.FiniteLowerStar
public import WeilConjectures.WeilSheaf.LowerShriekFunctoriality

/-!
# Vanishing of direct images of Weil sheaves

The derived direct image `Rf₀*G` and the direct image with compact support `Rf₀!G` of a Weil
sheaf are concentrated in degrees `≥ 0`. For a finite morphism `p` the higher direct images
`Rʳp₀*G` vanish for `r > 0`, and so, by Zariski's main theorem, do the higher direct images with
compact support `Rʳf₀!G` along a separated quasi-finite morphism `f`. These statements do not
involve weights; they are used both by the weight reductions of
`WeilConjectures.DeligneLaumon.Reduction.FormalSteps` and by the computation of the local
Frobenius of quasi-finite direct images in
`WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk`.

## Main statements

- `AlgebraicGeometry.WeilSheaf.isZero_homologySheaf_derivedLowerStar_of_neg` and
  `AlgebraicGeometry.WeilSheaf.isZero_homologySheaf_derivedLowerShriek_of_neg`: vanishing in
  negative degrees.
- `AlgebraicGeometry.WeilSheaf.isZero_higherLowerStar_of_isFinite`: blueprint
  `lemma-finite-direct-images--2`.
- `AlgebraicGeometry.isZero_higherLowerShriek_of_quasiFinite`: blueprint
  `lemma-finite-quasi-finite-direct-images`, part 1.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

section UpperStar

variable {W X : Scheme.{u}} [W.Over (Spec (CommRingCat.of k₀))]
  [X.Over (Spec (CommRingCat.of k₀))] (h : W ⟶ X) [h.IsOver (Spec (CommRingCat.of k₀))]

/-- The pullback of a Weil sheaf placed in degree zero is the pullback of the sheaf, placed in
degree zero. -/
noncomputable def WeilComplex.upperStarToComplexIso (G : WeilSheaf k₀ l X) :
    (WeilComplex.upperStar h).obj (WeilSheaf.toComplex.obj G) ≅
      WeilSheaf.toComplex.obj ((WeilSheaf.upperStar h).obj G) :=
  ObjectProperty.isoMk _
    (((ProEtaleWeilSheaf.upperStar k₀ l h).mapDerivedCategorySingleFunctor 0).app G.obj)

end UpperStar

/-- The derived direct image `Rf₀*G` of a Weil sheaf is concentrated in degrees `≥ 0`: it is
computed by `f₀*` applied to an injective resolution of `G`. -/
theorem WeilSheaf.isZero_homologySheaf_derivedLowerStar_of_neg {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] [QuasiCompact f] [QuasiSeparated f]
    [LocallyOfFiniteType f] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] (G : WeilSheaf k₀ l X) {n : ℤ} (hn : n < 0) :
    IsZero ((WeilComplex.homologySheaf n).obj
      ((WeilComplex.derivedLowerStar f).obj (WeilSheaf.toComplex.obj G))) := by
  rw [WeilComplex.isZero_homologySheaf_obj_iff]
  have : ((WeilComplex.derivedLowerStar f).obj (WeilSheaf.toComplex.obj G)).obj.IsGE 0 :=
    (ProEtaleWeilSheaf.lowerStar k₀ l f).isGE_rightDerivedFunctor_obj_singleFunctor G.obj
  exact _root_.DerivedCategory.isZero_of_isGE _ 0 n hn

section LowerShriek

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] {f : X ⟶ Y} [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]

attribute [local instance] Compactification.over in
/-- The direct image with compact support `Rf₀!G` of a Weil sheaf is concentrated in degrees
`≥ 0`: it is `Rḡ_*` applied to the extension by zero of `G`, a sheaf. -/
theorem WeilSheaf.isZero_homologySheaf_derivedLowerShriek_of_neg (G : WeilSheaf k₀ l X) {n : ℤ}
    (hn : n < 0) :
    IsZero ((WeilComplex.homologySheaf n).obj
      ((WeilComplex.derivedLowerShriek k₀ l f).obj (WeilSheaf.toComplex.obj G))) := by
  rw [WeilComplex.isZero_homologySheaf_obj_iff]
  let c := HasCompactification.compactification f (hf := hasCompactification_of_over (k₀ := k₀) f)
  have e := (Functor.mapDerivedCategorySingleFunctor
    (ProEtaleWeilSheaf.extensionByZero k₀ l c.i) 0).app G.obj
  have h := (ProEtaleWeilSheaf.lowerStar k₀ l c.g).isGE_rightDerivedFunctor_obj_singleFunctor
    ((ProEtaleWeilSheaf.extensionByZero k₀ l c.i).obj G.obj)
  have : _root_.DerivedCategory.TStructure.t.IsGE
      ((ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor.obj
        ((ProEtaleWeilSheaf.extensionByZero k₀ l c.i ⋙ _root_.DerivedCategory.singleFunctor _ 0).obj
          G.obj)) 0 := h
  have h' := _root_.DerivedCategory.TStructure.t.isGE_of_iso
    ((ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor.mapIso e.symm) 0
  have h'' : ((WeilComplex.derivedLowerShriek k₀ l f).obj
      (WeilSheaf.toComplex.obj G)).obj.IsGE 0 := h'
  exact _root_.DerivedCategory.isZero_of_isGE _ 0 n hn

end LowerShriek

/-- **Finite direct images are exact** (blueprint: `lemma-finite-direct-images--2`,
with the passage to `ℚ̄_ℓ`-coefficients): for a finite morphism
`p : T ⟶ Y` of `k₀`-schemes, the higher direct images `Rʳp₀*G` of a Weil sheaf vanish for
`r > 0`: the pushforward `p₀*` is exact
(`AlgebraicGeometry.ProEtaleWeilSheaf.preservesFiniteColimits_lowerStar_of_isFinite`), hence is
its own right derived functor. -/
theorem WeilSheaf.isZero_higherLowerStar_of_isFinite {T Y : Scheme.{u}}
    [T.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] (p : T ⟶ Y)
    [IsFinite p] [p.IsOver (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] (G : WeilSheaf k₀ l T) (r : ℕ) (hr : 0 < r) :
    IsZero ((WeilSheaf.higherLowerStar p r).obj G) := by
  -- `Y` is locally noetherian, so the finite morphism `p` is of finite presentation and `p₀*`
  -- is exact (`ProEtaleWeilSheaf.preservesFiniteColimits_lowerStar_of_isFinite`).
  have : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (CommRingCat.of k₀))
  have := ProEtaleWeilSheaf.preservesFiniteColimits_lowerStar_of_isFinite k₀ l p
  change IsZero ((WeilComplex.homologySheaf r).obj
    ((WeilComplex.derivedLowerStar p).obj (WeilSheaf.toComplex.obj G)))
  rw [WeilComplex.isZero_homologySheaf_obj_iff]
  -- An exact functor is its own right derived functor, so `Rp₀*G` is `p₀*G` in degree `0`.
  let F := ProEtaleWeilSheaf.lowerStar k₀ l p
  let e : F.rightDerivedFunctor.obj ((_root_.DerivedCategory.singleFunctor _ 0).obj G.obj) ≅
      (_root_.DerivedCategory.singleFunctor _ 0).obj (F.obj G.obj) :=
    F.rightDerivedFunctorIsoMapDerivedCategory.app _ ≪≫
      (F.mapDerivedCategorySingleFunctor 0).app G.obj
  exact (_root_.DerivedCategory.isZero_of_isLE _ 0 r (by omega)).of_iso
    ((_root_.DerivedCategory.homologyFunctor _ r).mapIso e)

section QuasiFinite

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyQuasiFinite f] [LocallyOfFiniteType f] [QuasiCompact f]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]

/-- For a separated quasi-finite morphism `f : X ⟶ Y` of `k₀`-schemes the higher direct images
with compact support `Rʳf₀!` vanish for `r > 0` (blueprint:
`lemma-finite-quasi-finite-direct-images`, `lemma-finite-quasi-finite-direct-images`, part 1).

Zariski's main theorem factors `f` as a quasi-compact open immersion `j : X ⟶ T` followed by a
finite morphism `p : T ⟶ Y`, so that `Rf₀! ≅ Rp₀! ∘ Rj₀! ≅ Rp₀* ∘ j₀!`; the extension by zero
`j₀!` is exact and so is the finite direct image `p₀*`
(`AlgebraicGeometry.WeilSheaf.isZero_higherLowerStar_of_isFinite`). -/
theorem isZero_higherLowerShriek_of_quasiFinite (r : ℕ) (hr : 0 < r) (F : WeilSheaf k₀ l X) :
    IsZero ((WeilSheaf.higherLowerShriek k₀ l f r).obj F) := by
  have : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (CommRingCat.of k₀))
  have : QuasiSeparatedSpace Y :=
    quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (CommRingCat.of k₀))
  obtain ⟨T, j, p, hj, hjc, hp, hjp⟩ := f.exists_isOpenImmersion_isFinite_of_locallyQuasiFinite
  let : T.Over (Spec (CommRingCat.of k₀)) := ⟨p ≫ Y ↘ Spec (CommRingCat.of k₀)⟩
  have : p.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have : j.IsOver (Spec (CommRingCat.of k₀)) := ⟨by
    change j ≫ p ≫ Y ↘ Spec (CommRingCat.of k₀) = _
    rw [← Category.assoc, hjp, comp_over]⟩
  have : LocallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (LocallyOfFiniteType (p ≫ _))
  have : QuasiCompact (T ↘ Spec (CommRingCat.of k₀)) := inferInstanceAs (QuasiCompact (p ≫ _))
  have : QuasiSeparated (T ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (QuasiSeparated (p ≫ _))
  subst hjp
  obtain ⟨e⟩ := WeilComplex.nonempty_derivedLowerShriek_comp_iso (k₀ := k₀) (l := l) j p
  obtain ⟨e'⟩ := WeilComplex.nonempty_derivedLowerShriek_toComplex_iso_of_isOpenImmersion j F
  exact (WeilSheaf.isZero_higherLowerStar_of_isFinite p _ r hr).of_iso
    ((WeilComplex.homologySheaf r).mapIso (e.app (WeilSheaf.toComplex.obj F) ≪≫
      (WeilComplex.derivedLowerShriek k₀ l p).mapIso e' ≪≫
      WeilComplex.derivedLowerShriekObjIsoDerivedLowerStar p _))

end QuasiFinite

end AlgebraicGeometry
