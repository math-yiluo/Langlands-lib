/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.Reduction.RealLissePurity
public import WeilConjectures.DeligneLaumon.Reduction.FiniteEtaleChart
public import WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed
public import WeilConjectures.DeligneLaumon.Reduction.RealCurve
public import WeilConjectures.WeilSheaf.UpperStarExact
public import WeilConjectures.WeilSheaf.UpperStarFiniteEtale

/-!
# Real Weil sheaves on an arbitrary base are mixed

A constructible Weil sheaf is `ι`-*real* (`AlgebraicGeometry.WeilSheaf.IsReal`) if the realization
under `ι` of every local Frobenius characteristic polynomial has real coefficients. Over a curve
this forces purity on a dense open, which is the content of the blueprint section
`chap-Purity-of-real-sheaves`; this file states the extension of that statement to an arbitrary
separated finite-type `k₀`-scheme, which is the input the Deligne–Laumon reduction needs in order
to turn the reality of a local `L`-factor into a weight bound.

## Implementation notes

A Noetherian induction reduces to a real sheaf on a nonempty open, which may be taken finite
étale over a nonempty open of some `𝔸ᵈ`; pushing forward, to a real sheaf on a nonempty open of
`𝔸ᵈ`, lisse on a smooth affine open. There its irreducible constituents are pure
(`AlgebraicGeometry.WeilSheaf.IsReal.exists_isPunctuallyPureOfWeight_cokernel_of_smooth`, by
curve testing and purity on curves), so it is mixed, and mixedness is spliced back along the
open–closed sequence.

## Main statements

- `AlgebraicGeometry.WeilSheaf.isMixed_of_forall_exists_isMixed_upperStar_opensι`: the Noetherian
  induction of `theorem-real-constructible-sheaves-are-mixed--1`.
- `AlgebraicGeometry.WeilSheaf.IsReal.isMixed`: blueprint
`theorem-real-constructible-sheaves-are-mixed--1` and
  `theorem-real-constructible-sheaves-are-mixed--1`.

## References

- [Deligne, *La conjecture de Weil : II*][deligne1980], Publ. Math. IHÉS **52** (1980), §1.8, for
  real sheaves and their mixedness.
- [Kiehl, Weissauer, *Weil conjectures, perverse sheaves and l-adic Fourier
  transform*][kiehlWeissauer2001], Springer (2001), Appendix B, for the
  irreducibility-preserving Bertini theorem the proof uses.
-/

@[expose] public section

universe u

open CategoryTheory Limits

/- Through `Mathlib.AlgebraicGeometry.Group.Affine`, `Spec k₀` is also an object over itself via
`specOverSpec`; prefer the identity structure `CategoryTheory.instOverClass`. -/
attribute [local instance 1100] CategoryTheory.instOverClass

namespace AlgebraicGeometry

open scoped ProEtale

open TopologicalSpace

namespace WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {ι : PadicAlgCl l →+* ℂ}

/-- Every Weil sheaf on a nonempty open of `𝔸⁰ = Spec k₀` is mixed. -/
theorem exists_isMixed_upperStar_opensι_of_isEmpty {n : Type u} [IsEmpty n]
    (O : 𝔸(n; Spec (CommRingCat.of k₀)).Opens) [Nonempty O] (G : WeilSheaf k₀ l O) :
    ∃ O' : O.toScheme.Opens, (O' : Set O).Nonempty ∧
      ((WeilSheaf.upperStar O'.ι).obj G).IsMixed ι := by
  have hO : IsOpenImmersion (O.toScheme ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over O.ι]; infer_instance
  have : LocallyQuasiFinite ((⊤ : O.toScheme.Opens).toScheme ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over (⊤ : O.toScheme.Opens).ι]; infer_instance
  have : IsSeparated ((⊤ : O.toScheme.Opens).toScheme ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over (⊤ : O.toScheme.Opens).ι]; infer_instance
  have : LocallyOfFiniteType ((⊤ : O.toScheme.Opens).toScheme ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over (⊤ : O.toScheme.Opens).ι]; infer_instance
  have : QuasiCompact ((⊤ : O.toScheme.Opens).toScheme ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over (⊤ : O.toScheme.Opens).ι]; infer_instance
  obtain ⟨o⟩ := ‹Nonempty O›
  exact ⟨⊤, ⟨o, trivial⟩, isMixed_of_locallyQuasiFinite ι _⟩

/-- An `ι`-real Weil sheaf on a nonempty open of the affine line `𝔸¹` (with any one-element index
type) is `ι`-mixed on a nonempty open:
it is lisse on a dense open, a smooth geometrically connected curve. -/
theorem IsReal.exists_isMixed_upperStar_opensι_of_card_eq_one {n : Type u} [Finite n]
    (hn : Nat.card n = 1) (O : 𝔸(n; Spec (CommRingCat.of k₀)).Opens) [Nonempty O]
    {G : WeilSheaf k₀ l O}
    (hG : G.IsReal ι) :
    ∃ O' : O.toScheme.Opens, (O' : Set O).Nonempty ∧
      ((WeilSheaf.upperStar O'.ι).obj G).IsMixed ι := by
  have := isNoetherian_of_locallyOfFiniteType
    (𝔸(n; Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀))
  have : LocallyOfFiniteType (O.toScheme ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over O.ι]; infer_instance
  have : QuasiCompact (O.toScheme ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over O.ι]; infer_instance
  obtain ⟨U, hU, hlisse⟩ := exists_dense_isLisse_upperStar G
  have hne : (U : Set O).Nonempty := hU.nonempty
  have : Nonempty U := hne.to_subtype
  have hv : U.toScheme ↘ Spec (CommRingCat.of k₀) =
      (U.ι ≫ O.ι) ≫ 𝔸(n; Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀) := by
    rw [Category.assoc, comp_over O.ι, comp_over U.ι]
  have : SmoothOfRelativeDimension 1 (U.toScheme ↘ Spec (CommRingCat.of k₀)) := by
    have := AffineSpace.smoothOfRelativeDimension_over n (Spec (CommRingCat.of k₀))
    rw [hn] at this
    rw [hv, show 1 = 0 + 1 from rfl]; infer_instance
  have : GeometricallyConnected (U.toScheme ↘ Spec (CommRingCat.of k₀)) := by
    have := GeometricallyIrreducible.comp_of_isOpenImmersion (U.ι ≫ O.ι)
      (𝔸(n; Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀))
    rw [hv]; exact GeometricallyConnected.of_geometricallyIrreducible _
  have : IsSeparated (U.toScheme ↘ Spec (CommRingCat.of k₀)) := by
    rw [hv]; infer_instance
  have : LocallyOfFiniteType (U.toScheme ↘ Spec (CommRingCat.of k₀)) := by
    rw [hv]; infer_instance
  have : QuasiCompact (U.toScheme ↘ Spec (CommRingCat.of k₀)) := by
    rw [hv]; infer_instance
  exact ⟨U, hne, (hG.upperStar U.ι).isMixed_of_isLisse hlisse⟩

/-- An `ι`-real Weil sheaf on a nonempty open subscheme of `𝔸ᵈ` over `k₀` is `ι`-mixed on a
nonempty open, granted the case `d ≥ 2` (the hypothesis `h`, which carries the curve argument of
`theorem-real-constructible-sheaves-are-mixed--1`: curve testing and purity of real lisse sheaves on
curves): for `d = 0` every Weil sheaf on a point is mixed and for `d = 1` this is the curve case. -/
theorem IsReal.exists_isMixed_upperStar_opensι_of_affineSpace
    (h : ∀ (d : ℕ), 2 ≤ d → ∀ (O : 𝔸(ULift.{u} (Fin d); Spec (CommRingCat.of k₀)).Opens)
      [Nonempty O] (G : WeilSheaf k₀ l O), G.IsReal ι →
        ∃ O' : O.toScheme.Opens, (O' : Set O).Nonempty ∧
          ((WeilSheaf.upperStar O'.ι).obj G).IsMixed ι) {d : ℕ}
    (O : 𝔸(ULift.{u} (Fin d); Spec (CommRingCat.of k₀)).Opens) [Nonempty O]
    {G : WeilSheaf k₀ l O} (hG : G.IsReal ι) :
    ∃ O' : O.toScheme.Opens, (O' : Set O).Nonempty ∧
      ((WeilSheaf.upperStar O'.ι).obj G).IsMixed ι := by
  by_cases hd : 2 ≤ d
  · exact h d hd O G hG
  obtain rfl | rfl : d = 0 ∨ d = 1 := by omega
  · exact exists_isMixed_upperStar_opensι_of_isEmpty O G
  · exact hG.exists_isMixed_upperStar_opensι_of_card_eq_one (by simp) O

open ZeroObject in
/-- A Weil sheaf on a scheme without points is mixed of weights at most `w`, for every `w`: the
filtration `0 ⊆ F` has the single quotient `F`, which is punctually pure of weight `w` since
there are no closed points. -/
theorem isMixedOfWeightsAtMost_of_isEmpty {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] [IsEmpty X] (F : WeilSheaf k₀ l X)
    (w : ℝ) : F.IsMixedOfWeightsAtMost ι w :=
  ⟨1, ![0, F], fun i ↦ Fin.cases (0 : (0 : WeilSheaf k₀ l X) ⟶ F) (fun j ↦ j.elim0) i,
    Limits.isZero_zero _, ⟨Iso.refl _⟩,
    fun i ↦ Fin.cases ⟨fun _ _ _ ↦ (Limits.isZero_zero _).eq_of_tgt _ _⟩ (fun j ↦ j.elim0) i,
    fun _ ↦ ⟨w, le_rfl, fun x ↦ isEmptyElim x.1⟩⟩

/-- **Reduction of mixedness of real sheaves to a nonempty open.** Suppose that on every nonempty
reduced separated `k₀`-scheme `T` of finite type, every `ι`-real Weil sheaf is `ι`-mixed on some
nonempty open of `T`. Then every `ι`-real Weil sheaf on a separated finite-type `k₀`-scheme is
`ι`-mixed (blueprint: `theorem-real-constructible-sheaves-are-mixed--1`, the reduction to a lisse
stratum).

Noetherian induction on the closed subsets of `X`: on a reduced closed subscheme `T`, a real
sheaf is mixed on a nonempty open `U` by hypothesis and, by induction, on the reduced closed
complement of `U`; mixed filtrations glue along the open–closed exact sequence
(`AlgebraicGeometry.WeilSheaf.IsMixedOfWeightsAtMost.of_openClosed`), and reality is inherited
by restrictions (`AlgebraicGeometry.WeilSheaf.IsReal.upperStar`). -/
theorem isMixed_of_forall_exists_isMixed_upperStar_opensι
    (h : ∀ (T : Scheme.{u}) [T.Over (Spec (CommRingCat.of k₀))] [IsReduced T] [Nonempty T]
      [IsSeparated (T ↘ Spec (CommRingCat.of k₀))]
      [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀))]
      [QuasiCompact (T ↘ Spec (CommRingCat.of k₀))] (G : WeilSheaf k₀ l T), G.IsReal ι →
        ∃ U : T.Opens, (U : Set T).Nonempty ∧ ((WeilSheaf.upperStar U.ι).obj G).IsMixed ι)
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] {F : WeilSheaf k₀ l X} (hF : F.IsReal ι) :
    F.IsMixed ι := by
  have := isNoetherian_of_locallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))
  -- Noetherian induction on the closed subsets of `X`.
  have key : ∀ (Z : Closeds X) (T : Scheme.{u}) [T.Over (Spec (CommRingCat.of k₀))]
      [IsReduced T] (i : T ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of k₀))],
      Set.range i ⊆ Z → ∀ G : WeilSheaf k₀ l T,
        haveI : LocallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀)) := by
          rw [← comp_over i]; infer_instance
        G.IsReal ι → G.IsMixed ι := by
    intro Z
    induction Z using WellFoundedLT.induction with
    | ind Z ih =>
    intro T _ _ i _ _ hiZ G hG
    have : LocallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀)) := by
      rw [← comp_over i]; infer_instance
    have : QuasiCompact (T ↘ Spec (CommRingCat.of k₀)) := by
      rw [← comp_over i]; infer_instance
    have : IsSeparated (T ↘ Spec (CommRingCat.of k₀)) := by
      rw [← comp_over i]; infer_instance
    have := isNoetherian_of_locallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀))
    cases isEmpty_or_nonempty T
    · exact ⟨0, isMixedOfWeightsAtMost_of_isEmpty G 0⟩
    obtain ⟨U, ⟨u, hu⟩, w₁, hU⟩ := h T G hG
    -- The reduced closed complement `T'` of `U`.
    let C : Closeds T := ⟨(U : Set T)ᶜ, U.isOpen.isClosed_compl⟩
    let i' := (Scheme.IdealSheafData.vanishingIdeal C).subschemeι
    let : (Scheme.IdealSheafData.vanishingIdeal C).subscheme.Over
        (Spec (CommRingCat.of k₀)) := ⟨i' ≫ T ↘ Spec (CommRingCat.of k₀)⟩
    have : i'.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
    have : LocallyOfFiniteType ((Scheme.IdealSheafData.vanishingIdeal C).subscheme ↘
        Spec (CommRingCat.of k₀)) := inferInstanceAs (LocallyOfFiniteType (i' ≫ _))
    have hrange : Set.range i' = C := by
      rw [Scheme.IdealSheafData.range_subschemeι,
        Scheme.IdealSheafData.coe_support_vanishingIdeal]
    let Z' : Closeds X := ⟨i '' C, i.isClosedEmbedding.isClosedMap _ C.isClosed⟩
    have hZ' : Z' < Z := by
      refine lt_of_le_of_ne (fun y ⟨t, _, ht⟩ ↦ hiZ ⟨t, ht⟩) fun h ↦ ?_
      have : i u ∈ (Z' : Set X) := h ▸ hiZ ⟨u, rfl⟩
      obtain ⟨t, ht, hti⟩ := this
      exact ht (i.isClosedEmbedding.injective hti ▸ hu)
    obtain ⟨w₂, hT'⟩ := ih Z' hZ' _ (i' ≫ i) (by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hrange]; exact subset_rfl)
      _ (hG.upperStar i')
    have : NoetherianSpace U.toScheme := inferInstanceAs (NoetherianSpace (U : Set T))
    exact ⟨max w₁ w₂, IsMixedOfWeightsAtMost.of_openClosed (j := U.ι) (i := i')
      (by rw [Scheme.Opens.range_ι, hrange]; exact isCompl_compl)
      (hU.mono_weight (le_max_left _ _)) (hT'.mono_weight (le_max_right _ _))⟩
  -- `X` is the union of the empty open and its reduction.
  let i := (Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds X)).subschemeι
  let : (Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds X)).subscheme.Over
      (Spec (CommRingCat.of k₀)) := ⟨i ≫ X ↘ Spec (CommRingCat.of k₀)⟩
  have : i.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have : LocallyOfFiniteType ((Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds X)).subscheme ↘
      Spec (CommRingCat.of k₀)) := inferInstanceAs (LocallyOfFiniteType (i ≫ _))
  have : IsEmpty (⊥ : X.Opens).toScheme := ⟨fun x ↦ x.2⟩
  have : QuasiCompact (⊥ : X.Opens).ι := inferInstance
  obtain ⟨w, hw⟩ := key ⊤ _ i (Set.subset_univ _) _ (hF.upperStar i)
  exact ⟨w, IsMixedOfWeightsAtMost.of_openClosed (j := (⊥ : X.Opens).ι) (i := i)
    (by rw [Scheme.Opens.range_ι, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]; exact isCompl_bot_top)
    (isMixedOfWeightsAtMost_of_isEmpty _ w) hw⟩

/-- Mixedness is preserved by pullback along any morphism of `k₀`-schemes: the pullback is exact
and preserves punctual purity. -/
theorem IsMixed.upperStar {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [Y.Over (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))] {F : WeilSheaf k₀ l Y}
    (hF : F.IsMixed ι) (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))] :
    ((WeilSheaf.upperStar φ).obj F).IsMixed ι :=
  let ⟨w, hw⟩ := hF
  ⟨w, hw.map (WeilSheaf.upperStar φ) fun _ _ hG ↦ hG.upperStar φ⟩

/-- Mixedness is invariant under isomorphism. -/
theorem IsMixed.of_iso {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] {F G : WeilSheaf k₀ l X}
    (hF : F.IsMixed ι) (e : F ≅ G) : G.IsMixed ι :=
  let ⟨w, hw⟩ := hF
  ⟨w, hw.of_iso e⟩

/-- A quotient of a mixed Weil sheaf is mixed. -/
theorem IsMixed.of_epi {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] {F G : WeilSheaf k₀ l X}
    (hF : F.IsMixed ι) (p : F ⟶ G) [Epi p] : G.IsMixed ι :=
  let ⟨w, hw⟩ := hF
  ⟨w, hw.of_epi p⟩

/-- If the pullback of `G` along an open immersion `k` is mixed, then so is its restriction to
the open image of `k`. -/
theorem IsMixed.upperStar_opensRange_ι {W T : Scheme.{u}} [W.Over (Spec (CommRingCat.of k₀))]
    [T.Over (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (W ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀))] {k : W ⟶ T} [IsOpenImmersion k]
    [k.IsOver (Spec (CommRingCat.of k₀))] {G : WeilSheaf k₀ l T}
    (h : ((WeilSheaf.upperStar k).obj G).IsMixed ι) :
    ((WeilSheaf.upperStar k.opensRange.ι).obj G).IsMixed ι := by
  have hk : k.isoOpensRange.inv ≫ k = k.opensRange.ι :=
    (Iso.inv_comp_eq _).2 (Scheme.Hom.isoOpensRange_hom_ι k).symm
  have : k.isoOpensRange.inv.IsOver (Spec (CommRingCat.of k₀)) := ⟨by
    rw [← comp_over k, ← Category.assoc, hk, comp_over]⟩
  obtain ⟨e₁⟩ := nonempty_upperStar_congr_iso (l := l) hk G
  obtain ⟨e₂⟩ := nonempty_upperStar_comp_iso (l := l) k.isoOpensRange.inv k G
  exact (h.upperStar k.isoOpensRange.inv).of_iso (e₂.symm ≪≫ e₁)

/-- **Real lisse sheaves on smooth affine schemes are mixed.** Let `X₀` be a smooth geometrically
connected affine scheme of dimension `d ≥ 2` over `k₀` and `𝒢` an `ι`-real lisse Weil sheaf on
`X₀`. Then `𝒢` is `ι`-mixed: the successive quotients of a filtration with irreducible lisse
quotients are punctually pure
(`AlgebraicGeometry.WeilSheaf.IsReal.exists_isPunctuallyPureOfWeight_cokernel_of_smooth`)
(blueprint: `theorem-real-constructible-sheaves-are-mixed--1`, the lisse stratum). -/
theorem IsReal.isMixed_of_isLisse_of_smooth {X₀ : Scheme.{u}}
    [X₀.Over (Spec (CommRingCat.of k₀))] [IsAffine X₀] {d : ℕ} (hd : 2 ≤ d)
    [SmoothOfRelativeDimension d (X₀ ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (X₀ ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (X₀ ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X₀ ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X₀ ↘ Spec (CommRingCat.of k₀))]
    {𝒢 : WeilSheaf k₀ l X₀} (hreal : 𝒢.IsReal ι) (h𝒢 : 𝒢.IsLisse) : 𝒢.IsMixed ι := by
  obtain ⟨n, H, φ, h0, ⟨e⟩, hmono, hlisse, hirr⟩ := h𝒢.exists_filtration_isIrreducibleLisse
  have hpure (i : Fin n) : ∃ w : ℝ, (cokernel (φ i)).IsPunctuallyPureOfWeight ι w := by
    obtain ⟨ψ, hψ⟩ := exists_mono_of_chain φ hmono e i.succ
    have := hmono i
    exact hreal.exists_isPunctuallyPureOfWeight_cokernel_of_smooth hd h𝒢 (φ i) ψ (hlisse _)
      (hlisse _) (hirr i)
  choose w hw using hpure
  refine ⟨∑ i, |w i|, n, H, φ, h0, ⟨e⟩, hmono, fun i ↦ ⟨w i, ?_, hw i⟩⟩
  exact (le_abs_self _).trans
    (Finset.single_le_sum (fun j _ ↦ abs_nonneg (w j)) (Finset.mem_univ i))

/-- An `ι`-real Weil sheaf on a nonempty open subscheme of `𝔸ᵈ` over `k₀`, `d ≥ 2`, is `ι`-mixed
on a nonempty open: it is lisse on a dense open, which contains a nonempty affine open, smooth
and geometrically connected over `k₀` (blueprint:
`theorem-real-constructible-sheaves-are-mixed--1`). -/
theorem IsReal.exists_isMixed_upperStar_opensι_of_two_le {d : ℕ} (hd : 2 ≤ d)
    (O : 𝔸(ULift.{u} (Fin d); Spec (CommRingCat.of k₀)).Opens) [Nonempty O]
    {G : WeilSheaf k₀ l O} (hG : G.IsReal ι) :
    ∃ O' : O.toScheme.Opens, (O' : Set O).Nonempty ∧
      ((WeilSheaf.upperStar O'.ι).obj G).IsMixed ι := by
  have := isNoetherian_of_locallyOfFiniteType
    (𝔸(ULift.{u} (Fin d); Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀))
  have : LocallyOfFiniteType (O.toScheme ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over O.ι]; infer_instance
  have : QuasiCompact (O.toScheme ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over O.ι]; infer_instance
  obtain ⟨U, hU, hlisse⟩ := exists_dense_isLisse_upperStar G
  obtain ⟨x, hx⟩ := hU.nonempty
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hx
  have : IsAffine V.toScheme := hV
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  have : (O.toScheme.homOfLE hVU).IsOver (Spec (CommRingCat.of k₀)) := ⟨by
    rw [← comp_over U.ι, Scheme.homOfLE_ι_assoc, comp_over]⟩
  have hVlisse : ((WeilSheaf.upperStar V.ι).obj G).IsLisse := by
    rw [isLisse_upperStar_congr (O.toScheme.homOfLE_ι hVU).symm, isLisse_upperStar_comp_iff]
    exact hlisse.upperStar _
  have hv : V.toScheme ↘ Spec (CommRingCat.of k₀) =
      (V.ι ≫ O.ι) ≫ 𝔸(ULift.{u} (Fin d); Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀) := by
    rw [Category.assoc, comp_over O.ι, comp_over V.ι]
  have : SmoothOfRelativeDimension d (V.toScheme ↘ Spec (CommRingCat.of k₀)) := by
    have := AffineSpace.smoothOfRelativeDimension_over (ULift.{u} (Fin d))
      (Spec (CommRingCat.of k₀))
    rw [Nat.card_ulift, Nat.card_eq_fintype_card, Fintype.card_fin] at this
    have : SmoothOfRelativeDimension (0 + d) ((V.ι ≫ O.ι) ≫
        𝔸(ULift.{u} (Fin d); Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀)) :=
      inferInstance
    rw [zero_add] at this
    rwa [hv]
  have : GeometricallyConnected (V.toScheme ↘ Spec (CommRingCat.of k₀)) := by
    have := GeometricallyIrreducible.comp_of_isOpenImmersion (V.ι ≫ O.ι)
      (𝔸(ULift.{u} (Fin d); Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀))
    rw [hv]; exact GeometricallyConnected.of_geometricallyIrreducible _
  have : IsSeparated (V.toScheme ↘ Spec (CommRingCat.of k₀)) := by
    rw [hv]; infer_instance
  have : LocallyOfFiniteType (V.toScheme ↘ Spec (CommRingCat.of k₀)) := by
    rw [hv]; infer_instance
  have : QuasiCompact (V.toScheme ↘ Spec (CommRingCat.of k₀)) := by
    rw [hv]; infer_instance
  exact ⟨V, ⟨x, hxV⟩, (hG.upperStar V.ι).isMixed_of_isLisse_of_smooth hd hVlisse⟩

/-- An `ι`-real Weil sheaf on a nonempty reduced separated `k₀`-scheme `T` of finite type is
`ι`-mixed on a nonempty open of `T` (blueprint: `theorem-real-constructible-sheaves-are-mixed--1`,
the step on a nonempty open). A nonempty open `W` of `T` is finite étale over a nonempty open `O` of
some `𝔸ᵈ` (`AlgebraicGeometry.exists_isFinite_etale_to_affineSpace`) by `π : W ⟶ O`. The direct
image `π_* (G|W)` is real, hence mixed on a nonempty open `O'` of `O`; pulling back, `π^* π_* (G|W)`
is mixed over `π⁻¹ O'`, and so is its quotient `G|W` under the counit of `π^* ⊣ π_*`, an
epimorphism since `π` is finite étale. -/
theorem IsReal.exists_isMixed_upperStar_opensι (T : Scheme.{u})
    [T.Over (Spec (CommRingCat.of k₀))] [IsReduced T] [Nonempty T]
    [IsSeparated (T ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (T ↘ Spec (CommRingCat.of k₀))] {G : WeilSheaf k₀ l T} (hG : G.IsReal ι) :
    ∃ U : T.Opens, (U : Set T).Nonempty ∧ ((WeilSheaf.upperStar U.ι).obj G).IsMixed ι := by
  obtain ⟨W, j, d, O, π, hj, hW, hπf, hπe, hπs, hcomm⟩ :=
    exists_isFinite_etale_to_affineSpace T (T ↘ Spec (CommRingCat.of k₀))
  have := isNoetherian_of_locallyOfFiniteType
    (𝔸(ULift.{u} (Fin d); Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀))
  let : W.Over (Spec (CommRingCat.of k₀)) := ⟨j ≫ T ↘ Spec (CommRingCat.of k₀)⟩
  have : j.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have : π.IsOver (Spec (CommRingCat.of k₀)) := ⟨by rw [← comp_over O.ι]; exact hcomm⟩
  have : LocallyOfFiniteType (W ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (LocallyOfFiniteType (j ≫ _))
  have : LocallyOfFiniteType (O.toScheme ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over O.ι]; infer_instance
  have : QuasiCompact (O.toScheme ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over O.ι]; infer_instance
  have : QuasiSeparated (O.toScheme ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over O.ι]; infer_instance
  have : Nonempty O := ⟨π.base (Classical.arbitrary W)⟩
  obtain ⟨O', ⟨o, ho⟩, hmix⟩ := exists_isMixed_upperStar_opensι_of_affineSpace
    (fun _ hd O _ _ hG ↦ hG.exists_isMixed_upperStar_opensι_of_two_le hd O) O
    ((hG.upperStar j).lowerStar_of_isFinite π)
  -- pull back along `π' : π⁻¹ O' ⟶ O'`
  have : (π ∣_ O').IsOver (Spec (CommRingCat.of k₀)) := ⟨by
    rw [← comp_over O'.ι, morphismRestrict_ι_assoc, comp_over π, comp_over (π ⁻¹ᵁ O').ι]⟩
  obtain ⟨e₁⟩ := nonempty_upperStar_comp_iso (l := l) (π ∣_ O') O'.ι
    ((WeilSheaf.lowerStar π).obj ((WeilSheaf.upperStar j).obj G))
  obtain ⟨e₂⟩ := nonempty_upperStar_congr_iso (l := l) (morphismRestrict_ι π O')
    ((WeilSheaf.lowerStar π).obj ((WeilSheaf.upperStar j).obj G))
  obtain ⟨e₃⟩ := nonempty_upperStar_comp_iso (l := l) (π ⁻¹ᵁ O').ι π
    ((WeilSheaf.lowerStar π).obj ((WeilSheaf.upperStar j).obj G))
  have hmix' := (hmix.upperStar (π ∣_ O')).of_iso (e₁.symm ≪≫ e₂ ≪≫ e₃)
  -- the counit of `π^* ⊣ π_*` is an epimorphism since `π` is finite étale
  have := epi_upperStarLowerStarAdjunction_counit_app_of_finite_etale (l := l) π
    ((WeilSheaf.upperStar j).obj G)
  have h₂ : ((WeilSheaf.upperStar (π ⁻¹ᵁ O').ι).obj ((WeilSheaf.upperStar j).obj G)).IsMixed ι :=
    hmix'.of_epi ((WeilSheaf.upperStar (π ⁻¹ᵁ O').ι).map
      ((upperStarLowerStarAdjunction (k₀ := k₀) (l := l) π).counit.app
        ((WeilSheaf.upperStar j).obj G)))
  obtain ⟨e₄⟩ := nonempty_upperStar_comp_iso (l := l) (π ⁻¹ᵁ O').ι j G
  obtain ⟨p, hp⟩ := hπs.surj o
  refine ⟨((π ⁻¹ᵁ O').ι ≫ j).opensRange, ⟨j.base p, ⟨⟨p, ?_⟩, rfl⟩⟩,
    (h₂.of_iso e₄.symm).upperStar_opensRange_ι⟩
  rw [Scheme.Hom.mem_preimage, hp]
  exact ho

/-- Every constructible `ι`-real Weil sheaf on a separated finite-type `k₀`-scheme is `ι`-mixed
(blueprint: `theorem-real-constructible-sheaves-are-mixed--1`).

By Noetherian induction
(`AlgebraicGeometry.WeilSheaf.isMixed_of_forall_exists_isMixed_upperStar_opensι`) it suffices
to make a real sheaf mixed on a nonempty open
(`AlgebraicGeometry.WeilSheaf.IsReal.exists_isMixed_upperStar_opensι`): after shrinking, the
sheaf is lisse on a smooth affine stratum, where curve testing
(`AlgebraicGeometry.WeilSheaf.exists_isClosedImmersion_isIrreducibleLocalSystem_upperStar`) and
purity of real lisse sheaves on curves
(`AlgebraicGeometry.WeilSheaf.IsReal.exists_isPunctuallyPureOfWeight_cokernel`) make the
geometric constituents pure
(`AlgebraicGeometry.WeilSheaf.IsReal.exists_isPunctuallyPureOfWeight_cokernel_of_smooth`). -/
theorem IsReal.isMixed {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] {F : WeilSheaf k₀ l X} (hF : F.IsReal ι) :
    F.IsMixed ι :=
  isMixed_of_forall_exists_isMixed_upperStar_opensι
    (fun T _ _ _ _ _ _ _ hG ↦ hG.exists_isMixed_upperStar_opensι T) hF

end WeilSheaf

end AlgebraicGeometry
