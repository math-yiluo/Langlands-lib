/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.Regular.SMul
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Noetherian

import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import WeilConjectures.AlgebraicGeometry.Morphisms.NormalizationStalkBaseChange
import WeilConjectures.AlgebraicGeometry.Morphisms.RelativeNormalizationNormalStalks
import WeilConjectures.RingTheory.SmoothNormalRing
import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs

/-! # Principalness of the normalized root stalk maximal ideal

## References

* Stacks Project, Tags 0307, 035L and 00PD
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

-- Smooth ascent on affine charts, followed by localization at the source point.
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

private theorem normal_stalk_over_dvr
    {X : Scheme.{u}} [IsLocallyNoetherian X] (U : X.Opens)
    {P : Scheme.{u}} (p : P ⟶ U.toScheme) [IsFinite p] (hetale : Etale p)
    (x : (p ≫ U.ι).normalization)
    [IsDomain (X.presheaf.stalk ((p ≫ U.ι).fromNormalization x))]
    [IsDiscreteValuationRing (X.presheaf.stalk ((p ≫ U.ι).fromNormalization x))] :
    IsDomain ((p ≫ U.ι).normalization.presheaf.stalk x) ∧
      IsIntegrallyClosed ((p ≫ U.ι).normalization.presheaf.stalk x) := by
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
  let k := Limits.pullback.fst f.fromNormalization a
  algebraize [(k.stalkMap y).hom]
  have : Module.FaithfullyFlat (f.normalization.presheaf.stalk (k y))
      ((Limits.pullback f.fromNormalization a).presheaf.stalk y) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap k y) (k.toLRSHom.prop y)
  have hf : RingHom.FaithfullyFlat (k.stalkMap y).hom :=
    ‹Module.FaithfullyFlat (f.normalization.presheaf.stalk (k y))
      ((Limits.pullback f.fromNormalization a).presheaf.stalk y)›
  let ek := RingEquiv.ofBijective (k.stalkMap y).hom
    ⟨hf.injective, k.stalkMap_surjective y⟩
  have hi : IsIntegrallyClosed (g.normalization.presheaf.stalk z) := (hN z).2
  let := hi
  have hi' : IsIntegrallyClosed
      ((Limits.pullback f.fromNormalization a).presheaf.stalk y) := by
    have := IsIntegrallyClosed.of_equiv
      (asIso (e.hom.stalkMap z)).commRingCatIsoToRingEquiv.symm
    change IsIntegrallyClosed
      ((Limits.pullback f.fromNormalization a).presheaf.stalk (e.hom z)) at this
    rw [hz] at this
    exact this
  let := hi'
  have hresult : IsDomain (f.normalization.presheaf.stalk (k y)) ∧
      IsIntegrallyClosed (f.normalization.presheaf.stalk (k y)) :=
    ⟨ek.toMulEquiv.isDomain, IsIntegrallyClosed.of_equiv ek.symm⟩
  change IsDomain (f.normalization.presheaf.stalk
    ((Limits.pullback.fst f.fromNormalization a) y)) ∧ _ at hresult
  rw [hy] at hresult
  exact hresult

/-- The normalized stalk maximal ideal is principal, without a tame-ramification bound. -/
theorem root_normalization_stalk_maximalIdeal_isPrincipal
    (H : CommRingCat.{u}) [IsNoetherianRing H] (g : H)
    (hg : IsSMulRegular H g) [IsDomain (H ⧸ Ideal.span {g})]
    (n : ℕ) (hn : 0 < n) :
    let A := AdjoinRoot ((Polynomial.X : Polynomial H) ^ n - Polynomial.C g)
    let N := Spec (CommRingCat.of A)
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H A g)
    ∀ (hN : IsLocallyNoetherian N),
    letI := hN
    ∀ (P : Scheme.{u}) (p : P ⟶ V.toScheme) (hp : IsFinite p),
    letI := hp
    let a := p ≫ V.ι
    Etale p → IsFinite a.fromNormalization →
    ∀ (x : a.normalization),
      (a.fromNormalization x).asIdeal = Ideal.span
        {AdjoinRoot.root ((Polynomial.X : Polynomial H) ^ n - Polynomial.C g)} →
      IsRegularLocalRing (N.presheaf.stalk (a.fromNormalization x)) →
      (IsLocalRing.maximalIdeal (a.normalization.presheaf.stalk x)).IsPrincipal := by
  dsimp only
  intro hN P p hp hetale hfinite x hx hreg
  let := hN
  let := hp
  let A := AdjoinRoot ((Polynomial.X : Polynomial H) ^ n - Polynomial.C g)
  let N := Spec (CommRingCat.of A)
  let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H A g)
  let a := p ≫ V.ι
  let s := a.fromNormalization x
  let R := N.presheaf.stalk s
  let t : A := AdjoinRoot.root ((Polynomial.X : Polynomial H) ^ n - Polynomial.C g)
  let := hreg
  have hdom : IsDomain R := inferInstance
  let := hdom
  let e : Localization.AtPrime s.asIdeal ≃+* R :=
    (AlgebraicGeometry.StructureSheaf.stalkIso A s).toRingEquiv
  let : IsDomain (Localization.AtPrime s.asIdeal) := e.toMulEquiv.isDomain
  let := Polynomial.Monic.free_adjoinRoot (Polynomial.monic_X_pow_sub_C g hn.ne')
  have hgA : IsSMulRegular A (algebraMap H A g) := by
    have h := Module.Flat.isSMulRegular_of_isRegular (M := A)
      ((Commute.isRegular_iff (fun b ↦ Commute.all g b)).mpr hg.isLeftRegular)
    simpa [IsSMulRegular, Algebra.smul_def] using h
  have hrel : t ^ n = algebraMap H A g := by
    have heval := AdjoinRoot.eval₂_root
      ((Polynomial.X : Polynomial H) ^ n - Polynomial.C g)
    simpa only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C, sub_eq_zero, ← AdjoinRoot.algebraMap_eq] using heval
  have hgL := hgA.of_isLocalization (Localization.AtPrime s.asIdeal) s.asIdeal.primeCompl
  have htL : algebraMap A (Localization.AtPrime s.asIdeal) t ≠ 0 := by
    intro ht
    have hz : algebraMap A (Localization.AtPrime s.asIdeal) (algebraMap H A g) = 0 := by
      rw [← hrel, map_pow, ht, zero_pow hn.ne']
    have hone : (1 : Localization.AtPrime s.asIdeal) = 0 := hgL (by simp [hz])
    exact one_ne_zero hone
  have hmL : IsLocalRing.maximalIdeal (Localization.AtPrime s.asIdeal) =
      Ideal.span {algebraMap A (Localization.AtPrime s.asIdeal) t} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    have hmap := congrArg
      (Ideal.map (algebraMap A (Localization.AtPrime s.asIdeal))) hx
    simpa only [Ideal.map_span, Set.image_singleton] using hmap
  have hdvrL := IsDiscreteValuationRing.of_maximalIdeal_eq_span_singleton htL hmL
  let := hdvrL
  have hdvr : IsDiscreteValuationRing R :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e
  let := hdvr
  obtain ⟨hd, hi⟩ := normal_stalk_over_dvr V p hetale x
  let := hd
  let := hi
  let := hfinite
  have : IsLocallyNoetherian a.normalization :=
    LocallyOfFiniteType.isLocallyNoetherian a.fromNormalization
  let S := a.normalization.presheaf.stalk x
  let φ := (a.fromNormalization.stalkMap x).hom
  have hqf : φ.QuasiFinite := a.fromNormalization.quasiFiniteAt x
  have hdim : ringKrullDim S ≤ ringKrullDim R := by
    let : Algebra R S := φ.toAlgebra
    have : Algebra.QuasiFinite R S := hqf
    apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap φ)
    intro q r hqr
    refine lt_of_le_of_ne (Ideal.comap_mono hqr.le) ?_
    intro heq
    have h := Algebra.QuasiFinite.eq_of_le_of_under_eq (R := R)
      q.asIdeal r.asIdeal hqr.le (congrArg PrimeSpectrum.asIdeal heq)
    exact hqr.ne (PrimeSpectrum.ext h)
  have hdimS : ringKrullDim S ≤ 1 :=
    hdim.trans_eq (IsDiscreteValuationRing.ringKrullDim_eq_one R)
  have hregular := IsRegularLocalRing.of_isIntegrallyClosed S hdimS
  apply IsLocalRing.finrank_cotangentSpace_le_one_iff.mp
  have hcot := (IsRegularLocalRing.iff_finrank_cotangentSpace S).mp hregular
  exact_mod_cast hcot.le.trans hdimS

end AlgebraicGeometry.Scheme
