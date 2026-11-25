/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale
public import Mathlib.AlgebraicGeometry.Normalization

import WeilConjectures.RingTheory.SmoothNormalRing
import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat
import WeilConjectures.AlgebraicGeometry.Morphisms.RelativeNormalizationNormalStalks

/-!
# Normality of the localized relative normalization

## References

* Stacks Project, Tags 033C (smooth ascent of normality), 035L (relative normalization in a
  normal source), and 0307 (localization of integral closure)
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem normal_stalks_of_smooth_integral_base {X Y : Scheme.{u}} [IsIntegral Y]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (g : X ⟶ Y) [Smooth g] (x : X) :
    IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) := by
  obtain ⟨U, hU, V, hV, hx, hVU, hg⟩ := Smooth.exists_isStandardSmooth g x
  let : Nonempty U := ⟨⟨g x, hVU hx⟩⟩
  let : IsIntegrallyClosed Γ(Y, U) := isIntegrallyClosed_of_isIntegrallyClosed_stalk hY U
  have hnormal := (g.smooth_appLE hU hV hVU).isNormalRing (fun p hp ↦ by
    let : IsIntegrallyClosed (Localization.AtPrime p) :=
      isIntegrallyClosed_of_isLocalization _ p.primeCompl p.primeCompl_le_nonZeroDivisors
    exact ⟨inferInstance, inferInstance⟩)
  let : Algebra Γ(X, V) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  have := hV.isLocalization_stalk ⟨x, hx⟩
  let p := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  obtain ⟨hd, hi⟩ := hnormal p
  let : IsDomain (Localization.AtPrime p) := hd
  let : IsIntegrallyClosed (Localization.AtPrime p) := hi
  let e := IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p)
    (X.presheaf.stalk x)
  exact ⟨e.symm.injective.isDomain e.symm, IsIntegrallyClosed.of_equiv e.toRingEquiv⟩

private theorem normal_stalks_of_flat_preimmersion {X Y : Scheme.{u}}
    (g : X ⟶ Y) [Flat g] [IsPreimmersion g]
    (hY : ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧
      IsIntegrallyClosed (Y.presheaf.stalk y)) (x : X) :
    IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) := by
  obtain ⟨hd, hi⟩ := hY (g x)
  let : IsDomain (Y.presheaf.stalk (g x)) := hd
  let : IsIntegrallyClosed (Y.presheaf.stalk (g x)) := hi
  algebraize [(g.stalkMap x).hom]
  have : Module.FaithfullyFlat (Y.presheaf.stalk (g x)) (X.presheaf.stalk x) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap g x) (g.toLRSHom.prop x)
  have hf : RingHom.FaithfullyFlat (g.stalkMap x).hom :=
    ‹Module.FaithfullyFlat (Y.presheaf.stalk (g x)) (X.presheaf.stalk x)›
  let e := RingEquiv.ofBijective (g.stalkMap x).hom
    ⟨hf.injective,
      g.stalkMap_surjective x⟩
  exact ⟨e.symm.injective.isDomain e.symm, IsIntegrallyClosed.of_equiv e⟩

/-- The stalks of the relative normalization, base changed to the stalk of `S` at `s`, are
normal domains. -/
theorem stalk_normalization_normal_part {S C : Scheme.{u}}
    [IsNoetherian S] [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c]
    (U : S.Opens)
    (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
    (s : S) :
    letI : IsFinite PA.obj.hom := PA.property
    letI : QuasiCompact (c ⁻¹ᵁ U).ι :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
        (inferInstance : QuasiCompact U.ι)
    let f := PA.obj.hom ≫ (c ⁻¹ᵁ U).ι
    let l := pullback.fst c (S.fromSpecStalk s)
    ∀ z : (pullback f.fromNormalization l : Scheme.{u}),
      IsDomain ((pullback f.fromNormalization l : Scheme.{u}).presheaf.stalk z) ∧
      IsIntegrallyClosed ((pullback f.fromNormalization l : Scheme.{u}).presheaf.stalk z) := by
  let : IsFinite PA.obj.hom := PA.property
  let : QuasiCompact (c ⁻¹ᵁ U).ι :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
      (inferInstance : QuasiCompact U.ι)
  intro f l z
  let : IsLocallyNoetherian ((𝟭 Scheme).obj PA.obj.left) :=
    LocallyOfFiniteType.isLocallyNoetherian (f ≫ c)
  have hP := normal_stalks_of_smooth_integral_base hS (f ≫ c)
  have hN := relativeNormalization_normal_stalks f hP
  exact normal_stalks_of_flat_preimmersion (pullback.fst f.fromNormalization l) hN z

end AlgebraicGeometry.Scheme
