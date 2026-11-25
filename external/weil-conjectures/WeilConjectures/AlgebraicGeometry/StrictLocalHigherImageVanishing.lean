/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.StalkFormula
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# Detecting higher-direct-image vanishing on strict-local pullbacks

Source: Stacks Project, Tag 03Q9; ILO, Exposé XIII, Proposition 2.3.4, printed p. 198.
This is the stalk-comparison part of the independent principal-open estimate needed by
`lem-per-qe-open-residue-spectral-strip`, not the affine Lefschetz estimate itself.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- A higher direct image vanishes exactly when the corresponding absolute cohomology
groups of all strict-local pullbacks vanish.

Source: Stacks Project, Tag 03Q9; ILO, Exposé XIII, Proposition 2.3.4, printed p. 198,
the equality of a higher-direct-image stalk with cohomology over the strict localization.

Proof: compare the ordinary right derived functor with `higherDirectImage`. At every
geometric point, the strict-henselization stalk formula identifies the underlying additive
group of that stalk with the displayed Ext group. A zero sheaf has zero stalks, proving
one direction. Conversely, subsingleton Ext groups make all geometric stalks zero. The
conservative family of algebraic-closure points then makes the identity of the higher
direct image equal to zero. Transport back through the derived-functor comparison.
This includes degree zero, an empty source or target, and arbitrary coefficient rings.

(blueprint: lem-per-qe-open-residue-strict-local-vanishing-criterion)
-/
theorem isZero_rightDerived_lowerStar_iff_strict_local_ext
    (B : Type (u + 1)) [CommRing B] {Y S : Scheme.{u}} (f : Y ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    (M : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B)) (q : ℕ) :
    IsZero (((lowerStar (ModuleCat.{u + 1} B) f).rightDerived q).obj M) ↔
      ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S),
        Subsingleton (Abelian.Ext.{u + 1}
          (SemiSimplicialObject.constSheaf.{u, u + 1}
            (pullback (Scheme.strictLocalizationToBase s) f).smallEtaleTopology B)
          ((upperStar (ModuleCat.{u + 1} B)
            (pullback.snd (Scheme.strictLocalizationToBase s) f)).obj M) q) := by
  have : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} B) :=
    hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  let F := lowerStar (ModuleCat.{u + 1} B) f
  let eD : (((lowerStar (ModuleCat.{u + 1} B) f).rightDerived q).obj M) ≅
      higherDirectImage B f q M :=
    (F.homologyRightDerivedFunctorPlusObjSingleFunctorIso M q).symm
  constructor
  · intro h Ω _ _ s
    have := (Scheme.pointSmallEtale s).sheafFiber_additive
      (A := ModuleCat.{u + 1} B)
    obtain ⟨e⟩ := nonempty_geometricStalk_higherDirectImage_addEquiv B f s M q
    have hz : IsZero ((Scheme.geometricStalkFunctor s (ModuleCat.{u + 1} B)).obj
        (higherDirectImage B f q M)) :=
      Functor.map_isZero (Scheme.geometricStalkFunctor s (ModuleCat.{u + 1} B))
      (h.of_iso eD.symm)
    let := ModuleCat.subsingleton_of_isZero hz
    exact e.symm.toEquiv.subsingleton
  · intro h
    have hz : IsZero (higherDirectImage B f q M) := by
      apply (IsZero.iff_id_eq_zero _).mpr
      apply Scheme.sheafHom_ext_of_sheafFiber_map_algClosurePoint
        (A := ModuleCat.{u + 1} B)
      intro x
      have := (Scheme.pointSmallEtale (S.algClosurePoint x)).sheafFiber_additive
        (A := ModuleCat.{u + 1} B)
      obtain ⟨e⟩ := nonempty_geometricStalk_higherDirectImage_addEquiv B f
        (S.algClosurePoint x) M q
      let := h _ (S.algClosurePoint x)
      let := e.toEquiv.subsingleton
      ext t
      exact Subsingleton.elim _ _
    exact hz.of_iso eD

end AlgebraicGeometry.Etale
