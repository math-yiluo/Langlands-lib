/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Algebra.Module.Torsion.Free
import WeilConjectures.AlgebraicGeometry.Morphisms.NormalizationStalkBaseChange
import WeilConjectures.AlgebraicGeometry.Morphisms.RelativeNormalizationNormalStalks
import WeilConjectures.RingTheory.SmoothNormalRing
import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat
@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme
-- The affine argument is the one used in StalkNormalizationBoundaryDimensionTwoTransfer.
private theorem normal_stalks_of_smooth_integral_base {Y Z : Scheme.{u}} [IsIntegral Z]
    (hZ : ∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z))
    (g : Y ⟶ Z) [Smooth g] (y : Y) :
    IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y) := by
  obtain ⟨U, hU, V, hV, hy, hVU, _⟩ := Smooth.exists_isStandardSmooth g y
  let : Nonempty U := ⟨⟨g y, hVU hy⟩⟩
  let : IsIntegrallyClosed Γ(Z, U) := isIntegrallyClosed_of_isIntegrallyClosed_stalk hZ U
  have hnormal := (g.smooth_appLE hU hV hVU).isNormalRing (fun q hq ↦ by
    let : IsIntegrallyClosed (Localization.AtPrime q) :=
      isIntegrallyClosed_of_isLocalization _ q.primeCompl q.primeCompl_le_nonZeroDivisors
    exact ⟨inferInstance, inferInstance⟩)
  let : Algebra Γ(Y, V) (Y.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨y, hy⟩
  have := hV.isLocalization_stalk ⟨y, hy⟩
  let q := (hV.primeIdealOf ⟨y, hy⟩).asIdeal
  obtain ⟨hd, hi⟩ := hnormal q
  let : IsDomain (Localization.AtPrime q) := hd
  let : IsIntegrallyClosed (Localization.AtPrime q) := hi
  let e := IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q)
    (Y.presheaf.stalk y)
  exact ⟨e.symm.injective.isDomain e.symm, IsIntegrallyClosed.of_equiv e.toRingEquiv⟩

private theorem domain_stalk_of_flat {Y Z : Scheme.{u}}
    (g : Y ⟶ Z) [Flat g] (y : Y)
    [IsDomain (Y.presheaf.stalk y)] : IsDomain (Z.presheaf.stalk (g y)) := by
  algebraize [(g.stalkMap y).hom]
  have : Module.FaithfullyFlat (Z.presheaf.stalk (g y)) (Y.presheaf.stalk y) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap g y) (g.toLRSHom.prop y)
  have hf : RingHom.FaithfullyFlat (g.stalkMap y).hom :=
    ‹Module.FaithfullyFlat (Z.presheaf.stalk (g y)) (Y.presheaf.stalk y)›
  exact hf.injective.isDomain (g.stalkMap y).hom

set_option linter.unusedVariables false in
/-- The normalization stalk in the punctured DVR situation is a domain.
-/
theorem punctured_dvr_normalization_stalk_isDomain
    {X : Scheme.{u}} [IsLocallyNoetherian X] (U : X.Opens)
    {P : Scheme.{u}} (p : P ⟶ U.toScheme) [IsFinite p] (hetale : Etale p)
    (x : (p ≫ U.ι).normalization)
    (hs : (p ≫ U.ι).fromNormalization x ∉ U)
    [IsDomain (X.presheaf.stalk ((p ≫ U.ι).fromNormalization x))]
    [IsDiscreteValuationRing (X.presheaf.stalk ((p ≫ U.ι).fromNormalization x))] :
    IsDomain ((p ≫ U.ι).normalization.presheaf.stalk x) := by
  let : Etale p := hetale
  let f := p ≫ U.ι
  let s := f.fromNormalization x
  let a₀ := X.fromSpecStalk s
  -- Keep the identity pullback to match the stalk-base-change comparison verbatim.
  let L := Limits.pullback (𝟙 X) a₀
  let a := Limits.pullback.fst (𝟙 X) a₀
  let d := Limits.pullback.snd (𝟙 X) a₀
  let : IsIntegral L := IsIntegral.of_isIso (inv d)
  let g := Limits.pullback.snd f a
  have hA : ∀ z : Spec (X.presheaf.stalk s),
      IsIntegrallyClosed ((Spec (X.presheaf.stalk s)).presheaf.stalk z) := by
    intro z
    let q := z.asIdeal
    let : IsIntegrallyClosed (Localization.AtPrime q) :=
      isIntegrallyClosed_of_isLocalization _ q.primeCompl q.primeCompl_le_nonZeroDivisors
    exact IsIntegrallyClosed.of_equiv
      (Spec.stalkIso (X.presheaf.stalk s) z).commRingCatIsoToRingEquiv.symm
  have hL : ∀ z : L, IsIntegrallyClosed (L.presheaf.stalk z) := by
    intro z
    let : IsIntegrallyClosed ((Spec (X.presheaf.stalk s)).presheaf.stalk (d z)) := hA (d z)
    exact IsIntegrallyClosed.of_equiv
      (asIso (d.stalkMap z)).commRingCatIsoToRingEquiv
  have hQ := normal_stalks_of_smooth_integral_base hL g
  have hN := relativeNormalization_normal_stalks g hQ
  let : IsIso (f.normalizationPullback a) :=
    Hom.isIso_normalizationPullback_stalk (𝟙 X) f s
  -- The canonical map from the stalk spectrum supplies a point above x.
  let t := Spec.map (f.fromNormalization.stalkMap x)
  let b₀ : Spec (f.normalization.presheaf.stalk x) ⟶ L :=
    Limits.pullback.lift (t ≫ a₀) t (by simp)
  let b : Spec (f.normalization.presheaf.stalk x) ⟶
      Limits.pullback f.fromNormalization a :=
    Limits.pullback.lift (f.normalization.fromSpecStalk x)
      b₀ (by
        simp only [b₀, a, Limits.pullback.lift_fst]
        exact (SpecMap_stalkMap_fromSpecStalk f.fromNormalization).symm)
  let y := b (IsLocalRing.closedPoint (f.normalization.presheaf.stalk x))
  have hy : Limits.pullback.fst f.fromNormalization a y = x := by
    change (b ≫ Limits.pullback.fst f.fromNormalization a) _ = x
    simp [b, fromSpecStalk_closedPoint]
  let e := asIso (f.normalizationPullback a)
  let z := e.inv y
  have hz : e.hom z = y := by simp [z]
  let : IsDomain (g.normalization.presheaf.stalk z) := (hN z).1
  have : IsDomain ((Limits.pullback f.fromNormalization a).presheaf.stalk y) := by
    have := (asIso (e.hom.stalkMap z)).commRingCatIsoToRingEquiv.toMulEquiv.isDomain
    change IsDomain ((Limits.pullback f.fromNormalization a).presheaf.stalk (e.hom z)) at this
    rw [hz] at this
    exact this
  have hd := domain_stalk_of_flat (Limits.pullback.fst f.fromNormalization a) y
  change IsDomain
    (f.normalization.presheaf.stalk ((Limits.pullback.fst f.fromNormalization a) y)) at hd
  rw [hy] at hd
  exact hd
end AlgebraicGeometry.Scheme
