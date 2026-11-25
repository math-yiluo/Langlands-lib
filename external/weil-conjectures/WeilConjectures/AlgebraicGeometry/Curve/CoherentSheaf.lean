/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch
public import WeilConjectures.AlgebraicGeometry.Modules.Annihilator
public import WeilConjectures.AlgebraicGeometry.Modules.GenericRank
public import WeilConjectures.AlgebraicGeometry.Modules.HilbertPolynomial
public import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine
public import WeilConjectures.AlgebraicGeometry.Modules.Torsion
public import WeilConjectures.AlgebraicGeometry.Modules.VanishingOnOpen
public import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
public import WeilConjectures.AlgebraicGeometry.Regular

/-!
# Coherent sheaves on a smooth curve: torsion and the locally free quotient

Let `X` be an integral scheme smooth of relative dimension one over a field `k`. Its local rings
are fields or discrete valuation rings, so on an affine open `W` a module over `Γ(X, W)` is flat
as soon as it is torsion-free (`AlgebraicGeometry.Scheme.flat_of_torsion_eq_bot`). For a
coherent `𝒪_X`-module `ℱ` with torsion subsheaf `𝒯` (`AlgebraicGeometry.Scheme.Modules.torsion`)
this gives:

* the quotient `ℱ / 𝒯` is finite locally free of rank `rk ℱ`
  (`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_torsionQuotient`);
* `𝒯` vanishes at the generic point, so `rk (ℱ / 𝒯) = rk ℱ`.

(blueprint: `theorem-riemann-roch-coherent-serre-duality--1`,
`theorem-riemann-roch-coherent-serre-duality`)
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {X : Scheme.{u}}

section LocalRings

/-- **The local rings of a smooth curve are valuation rings.** A local ring of a scheme smooth of
relative dimension one over a field is regular of dimension at most one, hence a field or a
discrete valuation ring. -/
theorem valuationRing_stalk_of_smoothOfRelativeDimension_one (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsRegular X] (x : X) :
    ValuationRing (X.presheaf.stalk x) := by
  have : IsLocallyNoetherian X := by
    have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
    exact LocallyOfFiniteType.isLocallyNoetherian f
  by_cases hF : IsField (X.presheaf.stalk x)
  · refine ValuationRing.iff_dvd_total.mpr ⟨fun a b ↦ ?_⟩
    by_cases ha : a = 0
    · right
      rw [ha]
      exact dvd_zero b
    · left
      obtain ⟨c, hc⟩ := hF.mul_inv_cancel ha
      exact ⟨c * b, by rw [← mul_assoc, hc, one_mul]⟩
  · have hle : ringKrullDim (X.presheaf.stalk x) ≤ 1 :=
      (ringKrullDim_stalk_le_topologicalKrullDim x).trans
        (by exact_mod_cast topologicalKrullDim_le_of_smoothOfRelativeDimension f 1)
    have hreg :=
      (IsRegularLocalRing.iff_finrank_cotangentSpace (X.presheaf.stalk x)).mp inferInstance
    have h0 : Module.finrank (IsLocalRing.ResidueField (X.presheaf.stalk x))
        (IsLocalRing.CotangentSpace (X.presheaf.stalk x)) ≠ 0 := fun h ↦
      hF (IsLocalRing.finrank_cotangentSpace_eq_zero_iff.mp h)
    have h1 : Module.finrank (IsLocalRing.ResidueField (X.presheaf.stalk x))
        (IsLocalRing.CotangentSpace (X.presheaf.stalk x)) ≤ 1 := by
      have := hreg ▸ hle
      exact_mod_cast this
    have hfin : Module.finrank (IsLocalRing.ResidueField (X.presheaf.stalk x))
        (IsLocalRing.CotangentSpace (X.presheaf.stalk x)) = 1 := by omega
    have : IsDiscreteValuationRing (X.presheaf.stalk x) :=
      ((IsDiscreteValuationRing.TFAE _ hF).out 1 6).mpr hfin
    infer_instance

/-- **Localizations of affine coordinate rings of a smooth curve are valuation rings.** -/
theorem valuationRing_localization_of_isAffineOpen (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsIntegral X] {W : X.Opens} (hW : IsAffineOpen W)
    [Nonempty W] (P : Ideal Γ(X, W)) [P.IsPrime] :
    ValuationRing (Localization.AtPrime P) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : IsRegular X := IsRegular.of_smooth f
  let y : PrimeSpectrum Γ(X, W) := ⟨P, inferInstance⟩
  have hy : hW.fromSpec y ∈ W := by
    rw [← SetLike.mem_coe, ← hW.range_fromSpec]
    exact ⟨y, rfl⟩
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hW.fromSpec y, hy⟩
  have := hW.isLocalization_stalk' y hy
  have := valuationRing_stalk_of_smoothOfRelativeDimension_one f (hW.fromSpec y)
  let e := IsLocalization.algEquiv P.primeCompl (X.presheaf.stalk (hW.fromSpec y))
    (Localization.AtPrime P)
  exact Function.Surjective.valuationRing (e : X.presheaf.stalk (hW.fromSpec y) →+* _)
    e.surjective

/-- **Torsion-free modules over the coordinate ring of an affine open of a smooth curve are
flat.** -/
theorem flat_of_torsion_eq_bot (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 f]
    [IsIntegral X] {W : X.Opens} (hW : IsAffineOpen W) [Nonempty W] (N : Type*)
    [AddCommGroup N] [Module Γ(X, W) N] (hN : Submodule.torsion Γ(X, W) N = ⊥) :
    Module.Flat Γ(X, W) N :=
  (Module.Flat.flat_iff_torsion_eq_bot_of_valuationRing_localization_isMaximal
    fun P _ ↦ valuationRing_localization_of_isAffineOpen f hW P).mpr hN

end LocalRings

namespace Modules

section TorsionFree

variable [IsIntegral X]

/-- **The torsion-free quotient has torsion-free sections.** On an integral scheme, the sections of
`ℱ / ℱ_tors` over a nonempty affine open are a torsion-free module, for `ℱ` quasi-coherent. -/
theorem torsion_sections_torsionQuotient_eq_bot (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] {W : X.Opens} (hW : IsAffineOpen W)
    [Nonempty W] : Submodule.torsion Γ(X, W) Γ(torsionQuotient ℱ, W) = ⊥ := by
  have hne : (W : Set X).Nonempty := by
    obtain ⟨x⟩ := ‹Nonempty W›
    exact ⟨x.1, x.2⟩
  have hS := shortExact_torsionShortComplex ℱ
  have := hS.mono_f
  have : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) (torsionShortComplex ℱ).X₁ :=
    inferInstanceAs (SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) (torsion ℱ))
  rw [eq_bot_iff]
  intro q hq
  obtain ⟨⟨a, ha⟩, haq⟩ := (Submodule.mem_torsion_iff q).mp hq
  obtain ⟨m, rfl⟩ := surjective_app_g_of_isAffineOpen hS hW q
  have h0 : (torsionShortComplex ℱ).g.app W (a • m) = 0 := by
    rw [Hom.app_smul]
    exact haq
  obtain ⟨t, ht⟩ := exists_app_f_eq_of_app_g_eq_zero hS.exact W _ h0
  have hat : IsTorsionSection ℱ (a • m) := ht ▸ t.2
  rw [isTorsionSection_iff_exists_smul_eq_zero hW hne] at hat
  obtain ⟨b, hb, hbam⟩ := hat
  have hm : IsTorsionSection ℱ m := by
    rw [isTorsionSection_iff_exists_smul_eq_zero hW hne]
    refine ⟨b * a, mul_ne_zero hb (nonZeroDivisors.ne_zero ha), ?_⟩
    rw [mul_smul]
    exact hbam
  have : m = (torsionShortComplex ℱ).f.app W ⟨m, hm⟩ := rfl
  rw [Submodule.mem_bot, this, ← ConcreteCategory.comp_apply, ← Hom.comp_app,
    (torsionShortComplex ℱ).zero]
  rfl

end TorsionFree

section Curve

variable [X.Over (Spec (.of k))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsIntegral X]

omit [IsIntegral X] in
variable (k) in
include k in
lemma isLocallyNoetherian_of_smoothOfRelativeDimension_one : IsLocallyNoetherian X := by
  have : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 1 _
  exact LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))

variable (k) in
include k in
/-- **Torsion-free coherent modules on a smooth curve are locally free.** A quasi-coherent
`𝒪_X`-module of finite presentation whose sections over the nonempty affine opens are
torsion-free is finite locally free: these sections are finitely presented, and flat by
`AlgebraicGeometry.Scheme.flat_of_torsion_eq_bot`. -/
theorem isFiniteLocallyFree_of_torsion_eq_bot (ℰ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℰ]
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) ℰ]
    (h : ∀ W : X.Opens, IsAffineOpen W → Nonempty W →
      Submodule.torsion Γ(X, W) Γ(ℰ, W) = ⊥) :
    ℰ.IsFiniteLocallyFree := by
  have := isLocallyNoetherian_of_smoothOfRelativeDimension_one k (X := X)
  refine isFiniteLocallyFree_of_isAffineOpen ℰ fun W hW ↦ ⟨?_, ?_⟩
  · have := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
    have := finite_sections_of_isFinitePresentation ℰ hW
    exact Module.finitePresentation_of_finite _ _
  · by_cases hne : Nonempty W
    · exact flat_of_torsion_eq_bot (X ↘ Spec (.of k)) hW _ (h W hW hne)
    · have : Subsingleton Γ(ℰ, W) := ⟨fun a b ↦
        (eq_zero_of_forall_exists a fun x hx ↦ (hne ⟨⟨x, hx⟩⟩).elim).trans
          (eq_zero_of_forall_exists b fun x hx ↦ (hne ⟨⟨x, hx⟩⟩).elim).symm⟩
      infer_instance

variable (k) in
include k in
/-- **The torsion-free quotient of a coherent module on a smooth curve is locally free of rank
`rk ℱ`.** For a coherent `𝒪_X`-module `ℱ` on an integral scheme `X` smooth of relative dimension
one over a field, `ℱ / ℱ_tors` is finite locally free, with constant rank the generic rank of
`ℱ`, since the torsion vanishes at the generic point.

(blueprint: `theorem-riemann-roch-coherent-serre-duality--1`) -/
theorem isFiniteLocallyFreeOfRank_torsionQuotient (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) ℱ] :
    (torsionQuotient ℱ).IsFiniteLocallyFreeOfRank ℱ.rank := by
  have := isLocallyNoetherian_of_smoothOfRelativeDimension_one k (X := X)
  have : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) (torsionQuotient ℱ) :=
    isQuasicoherent_cokernel _
  have : SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) (torsionQuotient ℱ) :=
    isFinitePresentation_cokernel _
  have : (torsionQuotient ℱ).IsFiniteLocallyFree :=
    isFiniteLocallyFree_of_torsion_eq_bot k _ fun W hW _ ↦
      torsion_sections_torsionQuotient_eq_bot ℱ hW
  have h := isFiniteLocallyFreeOfRank_rank (torsionQuotient ℱ)
  have : Subsingleton ((torsionShortComplex ℱ).X₁.presheaf.stalk (genericPoint X)) :=
    subsingleton_stalk_torsion ℱ
  have hr : ℱ.rank = (torsionQuotient ℱ).rank :=
    rank_eq_of_shortExact_of_subsingleton (shortExact_torsionShortComplex ℱ)
  rwa [← hr] at h

end Curve

end Modules

end AlgebraicGeometry.Scheme
