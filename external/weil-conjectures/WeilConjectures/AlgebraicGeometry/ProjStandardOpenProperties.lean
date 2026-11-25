/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# Basis, inclusions and finite coverings of standard opens of Proj

Source: Stacks Project, Constructions, Section 01M3 and Lemma 01M4;
Algebra, Lemma 00JP (blueprint: lem-weil-pbc-proj-standard-open-inclusion).
-/

@[expose] public section

universe u v w

namespace AlgebraicGeometry.Proj

private theorem positiveBasis
    {S : Type u} [CommRing S] {σ : Type v} [SetLike σ S] [AddSubgroupClass σ S]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] :
    TopologicalSpace.Opens.IsBasis
      {U | ∃ (f : S) (d : ℕ), 0 < d ∧ f ∈ 𝒜 d ∧ U = basicOpen 𝒜 f} := by
  rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
  intro U x hx
  obtain ⟨_, ⟨r, rfl⟩, hxr, hrU⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp (isBasis_basicOpen 𝒜) hx
  rw [basicOpen_eq_iSup_proj] at hxr
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hxr
  have hcover := Scheme.OpenCover.iSup_opensRange (affineOpenCover 𝒜).openCover
  have hxcover : x ∈ ⨆ j, ((affineOpenCover 𝒜).openCover.f j).opensRange := by
    rw [hcover]
    trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hxcover
  change x ∈ (awayι 𝒜 j.2.1 j.2.2 j.1.2).opensRange at hj
  rw [opensRange_awayι] at hj
  refine ⟨basicOpen 𝒜 (GradedRing.proj 𝒜 i r * j.2.1),
    ⟨_, i + j.1, Nat.add_pos_right i j.1.2,
      SetLike.mul_mem_graded (Subtype.prop _) j.2.2, rfl⟩, ?_, ?_⟩
  · rw [basicOpen_mul]
    exact ⟨hi, hj⟩
  · rw [basicOpen_mul]
    exact inf_le_left.trans ((le_iSup (fun i ↦ basicOpen 𝒜 (GradedRing.proj 𝒜 i r)) i).trans
      ((basicOpen_eq_iSup_proj 𝒜 r).ge.trans hrU))

private theorem chartCover
    {S : Type u} [CommRing S] {σ : Type v} [SetLike σ S] [AddSubgroupClass σ S]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] {f : S} {d : ℕ} (hd : 0 < d) (hf : f ∈ 𝒜 d)
    {I : Type w} (g : I → S) (k : I → ℕ) (hk : ∀ i, 0 < k i)
    (hg : ∀ i, g i ∈ 𝒜 (k i)) :
    basicOpen 𝒜 f ≤ ⨆ i, basicOpen 𝒜 (g i) ↔
      Ideal.span (Set.range (fun i ↦ HomogeneousLocalization.Away.mk 𝒜 hf (k i)
        (g i ^ d) (by simpa [smul_eq_mul, mul_comm] using
          SetLike.pow_mem_graded d (hg i)))) = ⊤ := by
  let φ := awayι 𝒜 f hf hd
  have hpre : φ ⁻¹ᵁ (⨆ i, basicOpen 𝒜 (g i)) =
      ⨆ i, PrimeSpectrum.basicOpen (HomogeneousLocalization.Away.isLocalizationElem hf (hg i)) := by
    rw [Scheme.Hom.preimage_iSup]
    exact iSup_congr fun i ↦ awayι_preimage_basicOpen 𝒜 hf hd (hg i) (hk i)
  rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff, ← hpre]
  rw [← opensRange_awayι 𝒜 f hf hd]
  constructor
  · intro h
    apply top_le_iff.mp
    intro x _
    exact h ⟨x, rfl⟩
  · intro h x hx
    obtain ⟨y, rfl⟩ := hx
    change φ y ∈ _
    have hy : y ∈ φ ⁻¹ᵁ (⨆ i, basicOpen 𝒜 (g i)) := by rw [h]; trivial
    exact hy

private theorem chartUnit
    {S : Type u} [CommRing S] {σ : Type v} [SetLike σ S] [AddSubgroupClass σ S]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] {f g : S} {d k : ℕ} (hd : 0 < d) (hk : 0 < k)
    (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 k) (h : basicOpen 𝒜 g ≤ basicOpen 𝒜 f) :
    IsUnit (HomogeneousLocalization.Away.isLocalizationElem hg hf) := by
  have hc := (chartCover 𝒜 hk hg (fun _ : Unit ↦ f) (fun _ ↦ d)
    (fun _ ↦ hd) (fun _ ↦ hf)).mp (by simpa using h)
  simpa only [Set.range_const, Ideal.span_singleton_eq_top] using hc

private theorem ordinaryUnit
    {S : Type u} [CommRing S] {σ : Type v} [SetLike σ S] [AddSubgroupClass σ S]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] {f g : S} {d k : ℕ} (hd : 0 < d) (hk : 0 < k)
    (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 k) (h : basicOpen 𝒜 g ≤ basicOpen 𝒜 f) :
    IsUnit (algebraMap S (Localization.Away g) f) := by
  have hu := (chartUnit 𝒜 hd hk hf hg h).map
    (algebraMap (HomogeneousLocalization.Away 𝒜 g) (Localization.Away g))
  have hv : IsUnit (algebraMap S (Localization.Away g) (f ^ k)) := by
    rw [← IsLocalization.mk'_spec (M := Submonoid.powers g) (Localization.Away g) (f ^ k)
      ⟨g ^ d, ⟨d, rfl⟩⟩]
    apply IsUnit.mul
    · simpa only [HomogeneousLocalization.algebraMap_apply,
        HomogeneousLocalization.Away.isLocalizationElem,
        HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk'] using hu
    · exact IsLocalization.map_units (Localization.Away g) _
  rw [map_pow] at hv
  exact (isUnit_pow_iff hk.ne').mp hv

private theorem homogeneousFactor
    {S : Type u} [CommRing S] {σ : Type v} [SetLike σ S] [AddSubgroupClass σ S]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] {f g : S} {d k : ℕ} (hk : 0 < k)
    (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 k)
    (hu : IsUnit (algebraMap S (Localization.Away g) f)) :
    ∃ (e l : ℕ) (a : S), 0 < e ∧ a ∈ 𝒜 l ∧ g ^ e = a * f := by
  obtain ⟨z, hz, b, hb⟩ :=
    (IsLocalization.algebraMap_isUnit_iff (Submonoid.powers g)).mp hu
  obtain ⟨n, rfl⟩ := hz
  change g ^ n = f * b at hb
  let e := n + d + 1
  have he : 0 < e := by dsimp [e]; omega
  have hd : d ≤ e * k := by
    have : e ≤ e * k := Nat.le_mul_of_pos_right e hk
    dsimp [e] at *
    omega
  have heq : g ^ e = f * (b * g ^ (d + 1)) := by
    dsimp [e]
    rw [show n + d + 1 = n + (d + 1) by omega, pow_add, hb]
    ring
  refine ⟨e, e * k - d, (DirectSum.decompose 𝒜 (b * g ^ (d + 1)) (e * k - d)),
    he, Subtype.prop _, ?_⟩
  have hp := congrArg (fun x ↦ (DirectSum.decompose 𝒜 x (e * k) : S)) heq
  rw [DirectSum.decompose_of_mem_same 𝒜 (by
    simpa [smul_eq_mul] using SetLike.pow_mem_graded e hg),
    DirectSum.coe_decompose_mul_of_left_mem_of_le 𝒜 hf hd] at hp
  simpa [mul_comm] using hp

private theorem finiteRefinement
    {S : Type u} [CommRing S] {σ : Type v} [SetLike σ S] [AddSubgroupClass σ S]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] {f : S} {d : ℕ} (hd : 0 < d) (hf : f ∈ 𝒜 d)
    (I : Type w) (U : I → (Proj 𝒜).Opens) (hU : (⨆ i, U i) = basicOpen 𝒜 f) :
    ∃ (n : ℕ) (g : Fin n → S) (k : Fin n → ℕ),
      (∀ i, 0 < k i ∧ g i ∈ 𝒜 (k i)) ∧
      basicOpen 𝒜 f = ⨆ i, basicOpen 𝒜 (g i) ∧
      ∀ i, ∃ j, basicOpen 𝒜 (g i) ≤ U j := by
  classical
  have hpoint (x : basicOpen 𝒜 f) :
      ∃ (g : S) (k : ℕ) (j : I), 0 < k ∧ g ∈ 𝒜 k ∧
        x.1 ∈ basicOpen 𝒜 g ∧ basicOpen 𝒜 g ≤ U j := by
    have hx : x.1 ∈ ⨆ i, U i := hU.symm ▸ x.2
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    obtain ⟨V, ⟨g, k, hk, hg, rfl⟩, hxg, hgj⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp (positiveBasis 𝒜) hj
    exact ⟨g, k, j, hk, hg, hxg, hgj⟩
  choose g k j hk hg hxg hgj using hpoint
  obtain ⟨t, ht⟩ := (isAffineOpen_basicOpen 𝒜 f hf hd).isCompact.elim_finite_subcover
    (fun x ↦ (basicOpen 𝒜 (g x) : Set (Proj 𝒜))) (fun x ↦ (basicOpen 𝒜 (g x)).isOpen)
    (fun x hx ↦ Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxg ⟨x, hx⟩⟩)
  let e := (Fintype.equivFin t).symm
  refine ⟨Fintype.card t, (fun i ↦ g (e i).1), (fun i ↦ k (e i).1),
    (fun i ↦ ⟨hk _, hg _⟩), le_antisymm ?_ ?_, (fun i ↦ ⟨j _, hgj _⟩)⟩
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht hx)
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨(Fintype.equivFin t) ⟨y, hy⟩, by simpa [e] using hxy⟩
  · refine iSup_le fun i ↦ (hgj _).trans ?_
    exact (le_iSup U (j (e i).1)).trans_eq hU

/-- Standard opens of positive homogeneous degree form a basis, intersect by multiplication,
and satisfy the power-divisibility inclusion and degree-zero unit-ideal covering criteria.
Source: Stacks Project, Constructions, Section 01M3 and Lemma 01M4 (1)(a),(b), (2), (3);
Algebra, Lemma 00JP (blueprint: lem-weil-pbc-proj-standard-open-inclusion).

Proof:
1. By `lem-weil-pbc-projective-spectrum-basic-opens-basis`, basic opens are open and
   `D(fg) = D(f) ∩ D(g)` because each point represents a prime ideal.
2. Decompose an element defining a basic neighbourhood into homogeneous components.
   A component outside the point's prime gives a smaller neighbourhood; if its degree
   is zero, multiply it by a positive-degree homogeneous element outside that prime.
   Such an element exists because the prime does not contain the irrelevant ideal.
3. For `D₊(g) ⊆ D₊(f)`, the chart identification from
   `lem-weil-pbc-proj-basic-open-intersection` identifies the inverse image of `D₊(f)`
   with the principal open of `f ^ deg g / g ^ deg f`. It is the whole spectrum, so
   `lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact` makes this fraction a unit.
4. It follows that `f` is invertible in `S_g`. Write its inverse as `b / g ^ n`, enlarge
   `n` to be positive with `n * deg g ≥ deg f`, and clear a power of `g` from the
   localization equality. Taking the appropriate homogeneous component of `b` gives
   `g ^ e = a * f`, with `a` homogeneous and `e ≥ 1`. If the product is nonzero,
   comparison of homogeneous degrees gives `deg a = e * deg g - deg f`.
5. Conversely, such a relation shows that any prime avoiding `g` avoids `f`.
   The inverse of `f` is `a / g ^ e`; the inverse of the degree-zero fraction is
   `a ^ deg g / g ^ (e * deg g - deg f)`. If `a * f = 0`, `g` is nilpotent,
   both localizations are zero rings, and the unit assertions still hold.
6. The chart is homeomorphic to the spectrum of the degree-zero localization, hence
   quasi-compact by `lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact`.
   Refine an arbitrary open cover using step 2, then take a finite subcover.
7. The chart pulls back the opens `D₊(gᵢ)` to principal opens of
   `gᵢ ^ deg f / f ^ deg gᵢ`. By the same spectrum lemma, these cover the chart
   exactly when their generators span the unit ideal.
-/
theorem standardOpenProperties
    {S : Type u} [CommRing S] {σ : Type v} [SetLike σ S] [AddSubgroupClass σ S]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] :
    TopologicalSpace.Opens.IsBasis
      {U | ∃ (f : S) (d : ℕ), 0 < d ∧ f ∈ 𝒜 d ∧ U = basicOpen 𝒜 f} ∧
    (∀ (f g : S) (d k : ℕ), 0 < d → 0 < k → f ∈ 𝒜 d → g ∈ 𝒜 k →
      basicOpen 𝒜 f ⊓ basicOpen 𝒜 g = basicOpen 𝒜 (f * g)) ∧
    (∀ (f g : S) (d k : ℕ) (_hd : 0 < d) (_hk : 0 < k)
      (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 k),
      (basicOpen 𝒜 g ≤ basicOpen 𝒜 f ↔
        ∃ (e l : ℕ) (a : S), 0 < e ∧ a ∈ 𝒜 l ∧ g ^ e = a * f) ∧
      (∀ (e l : ℕ) (a : S), 0 < e → a ∈ 𝒜 l → g ^ e = a * f →
        a * f ≠ 0 → l = e * k - d) ∧
      (basicOpen 𝒜 g ≤ basicOpen 𝒜 f →
        IsUnit (algebraMap S (Localization.Away g) f) ∧
        IsUnit (HomogeneousLocalization.Away.mk 𝒜 hg d (f ^ k)
          (by simpa [smul_eq_mul, mul_comm] using SetLike.pow_mem_graded k hf)))) ∧
    (∀ (f : S) (d : ℕ), 0 < d → f ∈ 𝒜 d →
      ∀ (I : Type w) (U : I → (Proj 𝒜).Opens),
        (⨆ i, U i) = basicOpen 𝒜 f →
        ∃ (n : ℕ) (g : Fin n → S) (k : Fin n → ℕ),
          (∀ i, 0 < k i ∧ g i ∈ 𝒜 (k i)) ∧
          basicOpen 𝒜 f = ⨆ i, basicOpen 𝒜 (g i) ∧
          ∀ i, ∃ j, basicOpen 𝒜 (g i) ≤ U j) ∧
    (∀ (f : S) (d : ℕ) (_hd : 0 < d) (hf : f ∈ 𝒜 d)
      (n : ℕ) (g : Fin n → S) (k : Fin n → ℕ)
      (_hk : ∀ i, 0 < k i) (hg : ∀ i, g i ∈ 𝒜 (k i)),
      basicOpen 𝒜 f ≤ ⨆ i, basicOpen 𝒜 (g i) ↔
        Ideal.span (Set.range (fun i : Fin n ↦
          HomogeneousLocalization.Away.mk 𝒜 hf (k i) (g i ^ d)
            (by simpa [smul_eq_mul, mul_comm] using SetLike.pow_mem_graded d (hg i)))) = ⊤) := by
  refine ⟨positiveBasis 𝒜, ?_, ?_, ?_, ?_⟩
  · intro f g d k _hd _hk _hf _hg
    exact (basicOpen_mul 𝒜 f g).symm
  · intro f g d k hd hk hf hg
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · intro h
      exact homogeneousFactor 𝒜 hk hf hg (ordinaryUnit 𝒜 hd hk hf hg h)
    · rintro ⟨e, l, a, he, _ha, hrel⟩
      rw [← basicOpen_pow 𝒜 g e he, hrel, basicOpen_mul]
      exact inf_le_right
    · intro e l a _he ha hrel hne
      have hpow : a * f ∈ 𝒜 (e * k) := by
        rw [← hrel]
        simpa [smul_eq_mul] using SetLike.pow_mem_graded e hg
      have hdeg := DirectSum.degree_eq_of_mem_mem 𝒜
        (SetLike.mul_mem_graded ha hf) hpow hne
      omega
    · intro h
      exact ⟨ordinaryUnit 𝒜 hd hk hf hg h, chartUnit 𝒜 hd hk hf hg h⟩
  · intro f d hd hf I U hU
    exact finiteRefinement 𝒜 hd hf I U hU
  · intro f d hd hf n g k hk hg
    exact chartCover 𝒜 hd hf g k hk hg

end AlgebraicGeometry.Proj
