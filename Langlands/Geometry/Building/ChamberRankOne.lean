import Langlands.Geometry.Building.ChamberFiltration
import Langlands.GroupScheme.Rational.RootFactorPairConsequences
import Langlands.GroupScheme.Reductive.RootDatumAssembly
import Langlands.GroupScheme.Rational.RelativeRootsCharacterSpan
import Langlands.GroupScheme.Rational.RelativeWeylCharacterAction

/-!
# The rank-one factorization `u u′ = x′ z x` on the apartment

For building data `B`, a relative root `a`, `u ∈ U_a(F) ∖ {1}` and `u′ ∈ U_{-a}(F) ∖ {1}`
with `x_a(u) + x_{-a}(u′) > 0` at a point `x` of the apartment, the product `u u′` is
`x′ z x″` with `x′ ∈ U_{-a}(F)`, `x″ ∈ U_a(F)`, `z ∈ Z(F)`, the valuation bounds of
Kaletha–Prasad Proposition 7.1.1(1), and conjugation by `z` preserving the valuation
`x_a`. The construction uses opposite factor pairs (the conclusion of KP Proposition
2.11.17, `RelativeRoot.HasRankOneFactorization`) and axiom V 5; it does not use AS 1.

At a point `x` of a chamber this gives the rank-one exchange
`U_{-a,x,0} U_{a,x,0} ⊆ U_{a,x,0} U_{-a,x,0} Z(k)^♯_x`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.Geometry.Building

/-! ### Elementary facts about valuations of the root datum -/

namespace IsRootDatumValuation

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} {i : S.toGrp ⟶ G}
  [Mono i.hom.hom.left] [IsAffineHom G.X.hom] {φ : RootFunctionFamily S G}

theorem le_apply_inv (h : IsRootDatumValuation i φ) {a : characterLattice S}
    (ha : a ∈ relativeRoots i) {g : rationalPoints G} (hg : g ∈ rootGroupPoints i a) :
    φ a g ≤ φ a g⁻¹ := by
  induction hv : φ a g using WithTop.recTopCoe with
  | top =>
    have h1 : g = 1 := (h.eq_top_iff a ha g hg).1 hv
    rw [h1, inv_one, (h.eq_top_iff a ha 1 (Subgroup.one_mem _)).2 rfl]
  | coe r =>
    have hmem : g ∈ rootFiltration i φ a r := ⟨hg, hv.symm ▸ le_refl _⟩
    exact (h.inv_mem a ha r g hmem).2

/-- `φ_a(g⁻¹) = φ_a(g)` (KP Remark 6.1.5, from V 1). -/
theorem apply_inv (h : IsRootDatumValuation i φ) (a : characterLattice S)
    (g : rationalPoints G) : φ a g⁻¹ = φ a g := by
  by_cases ha : a ∉ relativeRoots i
  · rw [h.eq_top_of_not_mem_roots a ha, h.eq_top_of_not_mem_roots a ha]
  push Not at ha
  by_cases hg : g ∈ rootGroupPoints i a
  · refine le_antisymm ?_ (h.le_apply_inv ha hg)
    simpa only [inv_inv] using h.le_apply_inv ha (Subgroup.inv_mem _ hg)
  · have hg' : g⁻¹ ∉ rootGroupPoints i a := fun h' => hg (by simpa using Subgroup.inv_mem _ h')
    rw [h.eq_top_of_not_mem a ha g hg, h.eq_top_of_not_mem a ha _ hg']

/-- The ultrametric inequality `min(φ_a(g), φ_a(h)) ≤ φ_a(gh)` (from V 1). -/
theorem min_le_apply_mul (h : IsRootDatumValuation i φ) {a : characterLattice S}
    (ha : a ∈ relativeRoots i) {g g' : rationalPoints G} (hg : g ∈ rootGroupPoints i a)
    (hg' : g' ∈ rootGroupPoints i a) : min (φ a g) (φ a g') ≤ φ a (g * g') := by
  induction hv : min (φ a g) (φ a g') using WithTop.recTopCoe with
  | top =>
    have h1 : φ a g = ⊤ := by
      have h := min_le_left (φ a g) (φ a g')
      rw [hv] at h
      exact top_le_iff.1 h
    have h2 : φ a g' = ⊤ := by
      have h := min_le_right (φ a g) (φ a g')
      rw [hv] at h
      exact top_le_iff.1 h
    rw [(h.eq_top_iff a ha g hg).1 h1, (h.eq_top_iff a ha g' hg').1 h2, one_mul,
      (h.eq_top_iff a ha 1 (Subgroup.one_mem _)).2 rfl]
  | coe r =>
    have h1 : g ∈ rootFiltration i φ a r := ⟨hg, hv ▸ min_le_left _ _⟩
    have h2 : g' ∈ rootFiltration i φ a r := ⟨hg', hv ▸ min_le_right _ _⟩
    exact (h.mul_mem a ha r g g' h1 h2).2

/-- If `φ_a(g′) < φ_a(g)`, then `φ_a(g g′) = φ_a(g′)` (KP Remark 6.1.5). -/
theorem apply_mul_eq_right_of_lt (h : IsRootDatumValuation i φ) {a : characterLattice S}
    (ha : a ∈ relativeRoots i) {g g' : rationalPoints G} (hg : g ∈ rootGroupPoints i a)
    (hg' : g' ∈ rootGroupPoints i a) (hlt : φ a g' < φ a g) : φ a (g * g') = φ a g' := by
  have hle : φ a g' ≤ φ a (g * g') := by
    simpa only [min_eq_right hlt.le] using h.min_le_apply_mul ha hg hg'
  refine le_antisymm ?_ hle
  by_contra hcon
  push Not at hcon
  have h2 := h.min_le_apply_mul ha (Subgroup.inv_mem _ hg) (Subgroup.mul_mem _ hg hg')
  rw [h.apply_inv, inv_mul_cancel_left] at h2
  exact absurd h2 (not_le.2 (lt_min hlt hcon))

/-- V 5 for the second element of an opposite factor pair: `φ_{-a}(u″) = -φ_a(u)`. -/
theorem opposite_snd (h : IsRootDatumValuation i φ) {a : characterLattice S}
    (ha : a ∈ relativeRoots i) {u : rationalPoints G} (hu : u ∈ rootGroupPoints i a)
    (hu1 : u ≠ 1) {u' u'' : rationalPoints G} (hu' : u' ∈ rootGroupPoints i (-a))
    (hu'' : u'' ∈ rootGroupPoints i (-a)) (hn : u' * u * u'' ∈ normalizerPoints i) :
    φ (-a) u'' + φ a u = 0 := by
  have hn' : u''⁻¹ * u⁻¹ * u'⁻¹ ∈ normalizerPoints i := by
    have := (normalizerPoints i).inv_mem hn
    simpa only [mul_inv_rev, mul_assoc] using this
  have h5 := h.opposite a ha u⁻¹ (Subgroup.inv_mem _ hu) (inv_ne_one.2 hu1) u''⁻¹
    (Subgroup.inv_mem _ hu'') u'⁻¹ (Subgroup.inv_mem _ hu') hn'
  rwa [h.apply_inv, h.apply_inv] at h5

end IsRootDatumValuation

/-- If `y + t = 0` in `ℝ ∪ {∞}` with `t` finite, then `y = -t`. -/
theorem withTop_eq_neg_of_add_eq_zero {y : WithTop ℝ} {t : ℝ}
    (h : y + (t : WithTop ℝ) = 0) : y = ((-t : ℝ) : WithTop ℝ) := by
  induction y using WithTop.recTopCoe with
  | top => exact absurd h (by simp)
  | coe s =>
    rw [← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_inj] at h
    rw [WithTop.coe_inj]
    linarith

namespace KPApartmentData

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} {i : S.toGrp ⟶ G}
  [Mono i.hom.hom.left] [IsAffineHom G.X.hom] {ω : kˣ → ℝ} {D : KPApartmentData i ω}

/-- A nonidentity root element has a finite valuation at every point. -/
theorem exists_val_eq_coe (x : D.Apartment) {a : characterLattice S}
    (ha : a ∈ relativeRoots i) {u : rationalPoints G} (hu : u ∈ rootGroupPoints i a)
    (hu1 : u ≠ 1) : ∃ t : ℝ, x.val a u = t := by
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 (mt (x.isValuation.eq_top_iff a ha u hu).1 hu1)
  exact ⟨t, ht.symm⟩

/-- Every normalizer point moves an apartment point by a translation, since the apartment
is an `N(k)`-stable equipollence class. -/
theorem exists_smul_val_eq_vadd (n : normalizerPoints i) (x : D.Apartment) :
    ∃ w : V S, n • x.val = w +ᵥ x.val :=
  D.equipollent_of_mem x.mem (D.smul_mem n _ x.mem)

/-- The translation part of `n = r₁ v r₂ ∈ N(k)`, with `v ∈ U_b(k) ∖ {1}` and
`r₁, r₂ ∈ U_{-b}(k)`, takes the value `-2 x_b(v)` on `b`. The proof uses V 5 for `v`
and for `r₂`, whose opposite pair is `(v, (n⁻¹ r₁⁻¹ n)⁻¹)`. -/
theorem eval_translation_eq_of_factor (x : D.Apartment) {b : characterLattice S}
    (hb : b ∈ relativeRoots i) (hb' : -b ∈ relativeRoots i) {v r₁ r₂ : rationalPoints G}
    (hv : v ∈ rootGroupPoints i b) (hv1 : v ≠ 1)
    (hr₁ : r₁ ∈ rootGroupPoints i (-b)) (hr₂ : r₂ ∈ rootGroupPoints i (-b))
    (hn : r₁ * v * r₂ ∈ normalizerPoints i)
    (hflip : weylAction i ⟨r₁ * v * r₂, hn⟩ b = -b) {t : ℝ} (ht : x.val b v = t)
    {w : V S} (hw : (⟨r₁ * v * r₂, hn⟩ : normalizerPoints i) • x.val = w +ᵥ x.val) :
    eval S b w = -2 * t := by
  have h := x.isValuation
  have hinv : weylAction i (⟨r₁ * v * r₂, hn⟩ : normalizerPoints i)⁻¹ (-b) = b := by
    rw [← hflip, weylAction_inv_apply_apply]
  have hκ : (r₁ * v * r₂)⁻¹ * r₁⁻¹ * (r₁ * v * r₂) ∈ rootGroupPoints i b := by
    have := conj_mem_rootGroupPoints (⟨r₁ * v * r₂, hn⟩ : normalizerPoints i)⁻¹
      (Subgroup.inv_mem _ hr₁)
    rw [hinv] at this
    simpa only [Subgroup.coe_inv, inv_inv] using this
  have hv' : v ∈ rootGroupPoints i (-(-b)) := by rwa [neg_neg]
  have hκ' : ((r₁ * v * r₂)⁻¹ * r₁⁻¹ * (r₁ * v * r₂))⁻¹ ∈ rootGroupPoints i (-(-b)) := by
    rw [neg_neg]
    exact Subgroup.inv_mem _ hκ
  have hpair : v * r₂ * ((r₁ * v * r₂)⁻¹ * r₁⁻¹ * (r₁ * v * r₂))⁻¹ ∈ normalizerPoints i := by
    have heq : v * r₂ * ((r₁ * v * r₂)⁻¹ * r₁⁻¹ * (r₁ * v * r₂))⁻¹ = r₁ * v * r₂ := by group
    rw [heq]
    exact hn
  -- V 5 for `v`
  have h5v := h.opposite b hb v hv hv1 r₁ hr₁ r₂ hr₂ hn
  rw [ht] at h5v
  have hr₁t := withTop_eq_neg_of_add_eq_zero h5v
  have h5v' := h.opposite_snd hb hv hv1 hr₁ hr₂ hn
  rw [ht] at h5v'
  have hr₂t := withTop_eq_neg_of_add_eq_zero h5v'
  have hr₂1 : r₂ ≠ 1 := by
    rintro rfl
    rw [(h.eq_top_iff (-b) hb' 1 (Subgroup.one_mem _)).2 rfl] at hr₂t
    exact WithTop.top_ne_coe hr₂t
  -- V 5 for `r₂`, second element
  have h5r := h.opposite_snd hb' hr₂ hr₂1 hv' hκ' hpair
  rw [neg_neg, hr₂t, h.apply_inv] at h5r
  have hκt := withTop_eq_neg_of_add_eq_zero h5r
  rw [neg_neg] at hκt
  -- evaluate the translation at `(-b, r₁⁻¹)`
  have hev := congrArg (fun φ : RootFunctionFamily S G => φ (-b) r₁⁻¹) hw
  simp only [RootFunctionFamily.smul_apply, RootFunctionFamily.vadd_apply] at hev
  rw [hinv, h.apply_inv] at hev
  rw [hκt, hr₁t, ← WithTop.coe_add, WithTop.coe_inj, eval_neg_char] at hev
  linarith

/-- Two opposite pairs, of `v′ ∈ U_{-c}(k)` and of `w ∈ U_c(k)`, give normalizer points whose
product acts trivially on characters: both represent the reflection along `c`, with equal
coroots by `coroot_eq_of_weylAction`. -/
theorem weylAction_mul_factorPairs_eq_one (hT : IsSplitTorus S.toGrp)
    (hfinite : (relativeRoots i).Finite)
    (hspan : Submodule.span ℚ
      (toRat '' (relativeRoots i ∪ Set.range (torusCharacterRestrict i))) = ⊤)
    {c : characterLattice S} (hc : c ∈ relativeRoots i)
    {w v' : rationalPoints G} (hw : w ∈ rootGroupPoints i c) (hw1 : w ≠ 1)
    (hv' : v' ∈ rootGroupPoints i (-c)) (hv'1 : v' ≠ 1)
    {p q : rationalPoints G × rationalPoints G}
    (hp : RelativeRoot.IsOppositeFactorPair i (-c) v' p)
    (hq : RelativeRoot.IsOppositeFactorPair i c w q) :
    weylAction i ((⟨q.1 * w * q.2, hq.2.2⟩ : normalizerPoints i) *
      ⟨p.1 * v' * p.2, hp.2.2⟩) = 1 := by
  have hc0 : c ≠ 0 := hc.1
  obtain ⟨hα2, hαw⟩ := hq.coroot_spec i hT hc0 hw hw1
  obtain ⟨hβ2, hβw⟩ := hp.coroot_spec i hT (neg_ne_zero.2 hc0) hv' hv'1
  set α := hq.coroot i hT hc0 hw hw1
  set β := hp.coroot i hT (neg_ne_zero.2 hc0) hv' hv'1
  have hβ2' : latticePairing S c (-β) = 2 := by
    rw [map_neg, ← hβ2, map_neg, LinearMap.neg_apply]
  have hβw' : ∀ χ, weylAction i (⟨p.1 * v' * p.2, hp.2.2⟩ : normalizerPoints i) χ =
      χ - latticePairing S χ (-β) • c := by
    intro χ
    rw [hβw χ, map_neg, neg_smul, smul_neg]
  have heq : α = -β := coroot_eq_of_weylAction i hT hfinite hspan hc hα2 hβ2' hαw hβw'
  refine LinearEquiv.ext fun χ => ?_
  rw [map_mul, LinearEquiv.mul_apply, hβw', ← heq, hαw]
  change _ = χ
  simp only [map_sub, map_zsmul, LinearMap.sub_apply, LinearMap.smul_apply, hα2, smul_eq_mul]
  rw [mul_two, sub_smul, add_smul]
  abel

/-- A normalizer point acting trivially on characters, whose translation part vanishes on
`c`, preserves the valuation `x_c` under conjugation. -/
theorem val_conj_eq_of_eval_eq_zero (x : D.Apartment) {N : normalizerPoints i}
    (hN : weylAction i N = 1) {W : V S} (hW : N • x.val = W +ᵥ x.val)
    {c : characterLattice S} (hc : eval S c W = 0) (g : rationalPoints G) :
    x.val c ((N : rationalPoints G) * g * (N : rationalPoints G)⁻¹) = x.val c g := by
  have hev := congrArg (fun φ : RootFunctionFamily S G =>
    φ c ((N : rationalPoints G) * g * (N : rationalPoints G)⁻¹)) hW
  simp only [RootFunctionFamily.smul_apply, RootFunctionFamily.vadd_apply, map_inv, hN,
    inv_one, hc, WithTop.coe_zero, add_zero] at hev
  have hg : (N : rationalPoints G)⁻¹ * ((N : rationalPoints G) * g * (N : rationalPoints G)⁻¹) *
      (N : rationalPoints G) = g := by group
  rw [← hev, hg]
  rfl

/-- The depth bound in KP Proposition 7.1.1(1): if `v v′ = x′ z y` with `v ∈ U_c(k) ∖ {1}`,
`v′, x′ ∈ U_{-c}(k)`, `z ∈ Z(k)`, `y ∈ U_c(k)` and `x_c(v) + x_{-c}(v′) > 0`, then
`x_c(y) ≥ x_c(v)`. If `(s₁, s₂)` is the opposite pair of `y ≠ 1`, then
`(z s₁ z⁻¹ x′⁻¹, v′ s₂)` is an opposite pair of `v`, and V 5 with the ultrametric
inequality bounds `x_c(y)`. -/
theorem le_val_of_mul_eq (hT : IsSplitTorus S.toGrp)
    (hrank : RelativeRoot.HasRankOneFactorization i) (x : D.Apartment)
    {c : characterLattice S} (hc : c ∈ relativeRoots i) (hc' : -c ∈ relativeRoots i)
    {v v' x' z y : rationalPoints G} (hv : v ∈ rootGroupPoints i c) (hv1 : v ≠ 1)
    (hv' : v' ∈ rootGroupPoints i (-c)) (hx' : x' ∈ rootGroupPoints i (-c))
    (hz : z ∈ centralizerPoints i) (hy : y ∈ rootGroupPoints i c)
    (heq : v * v' = x' * z * y) {t t' : ℝ} (ht : x.val c v = t)
    (ht' : (t' : WithTop ℝ) ≤ x.val (-c) v') (hpos : 0 < t + t') :
    (t : WithTop ℝ) ≤ x.val c y := by
  have h := x.isValuation
  by_cases hy1 : y = 1
  · rw [hy1, (h.eq_top_iff c hc 1 (Subgroup.one_mem _)).2 rfl]
    exact le_top
  obtain ⟨r, hr⟩ := exists_val_eq_coe x hc hy hy1
  rw [hr, WithTop.coe_le_coe]
  by_contra hlt
  push Not at hlt
  obtain ⟨s, hs⟩ := ((hrank c hc y hy hy1).1).exists
  have hzN : z ∈ normalizerPoints i := centralizerPoints_le_normalizerPoints i hz
  have hzW : weylAction i ⟨z, hzN⟩ = 1 := (hT.weylAction_eq_one_iff i ⟨z, hzN⟩).2 hz
  have hzs : z * s.1 * z⁻¹ ∈ rootGroupPoints i (-c) := by
    have := conj_mem_rootGroupPoints (⟨z, hzN⟩ : normalizerPoints i) hs.1
    rw [hzW] at this
    exact this
  have hx'i : x'⁻¹ ∈ rootGroupPoints i (-c) := Subgroup.inv_mem _ hx'
  have hr₁ : z * s.1 * z⁻¹ * x'⁻¹ ∈ rootGroupPoints i (-c) := Subgroup.mul_mem _ hzs hx'i
  have hr₂ : v' * s.2 ∈ rootGroupPoints i (-c) := Subgroup.mul_mem _ hv' hs.2.1
  have hn : z * s.1 * z⁻¹ * x'⁻¹ * v * (v' * s.2) ∈ normalizerPoints i := by
    have heq' : z * s.1 * z⁻¹ * x'⁻¹ * v * (v' * s.2) = z * (s.1 * y * s.2) :=
      calc z * s.1 * z⁻¹ * x'⁻¹ * v * (v' * s.2)
          = z * s.1 * z⁻¹ * x'⁻¹ * (v * v') * s.2 := by group
        _ = z * s.1 * z⁻¹ * x'⁻¹ * (x' * z * y) * s.2 := by rw [heq]
        _ = z * (s.1 * y * s.2) := by group
    rw [heq']
    exact Subgroup.mul_mem _ hzN hs.2.2
  -- V 5 for `v` with the pair `(z s₁ z⁻¹ x′⁻¹, v′ s₂)` and for `y` with `(s₁, s₂)`
  have h5v := h.opposite_snd hc hv hv1 hr₁ hr₂ hn
  rw [ht] at h5v
  have hvs := withTop_eq_neg_of_add_eq_zero h5v
  have h5y := h.opposite_snd hc hy hy1 hs.1 hs.2.1 hs.2.2
  rw [hr] at h5y
  have hs2 := withTop_eq_neg_of_add_eq_zero h5y
  have hmin := h.min_le_apply_mul hc' hv' hs.2.1
  rw [hvs, hs2] at hmin
  have h1 : ((-t : ℝ) : WithTop ℝ) < x.val (-c) v' :=
    lt_of_lt_of_le (WithTop.coe_lt_coe.2 (by linarith)) ht'
  have h2 : ((-t : ℝ) : WithTop ℝ) < ((-r : ℝ) : WithTop ℝ) :=
    WithTop.coe_lt_coe.2 (by linarith)
  exact absurd hmin (not_le.2 (lt_min h1 h2))

/-- **Rank-one factorization** (KP Proposition 7.1.1(1), without the fixed-point property
of `z`). Let `v ∈ U_c(k) ∖ {1}` and `v′ ∈ U_{-c}(k) ∖ {1}` with `x_c(v) + x_{-c}(v′) > 0`.
Then `v v′ = x′ z y` with `x′ ∈ U_{-c}(k)`, `z ∈ Z(k)`, `y ∈ U_c(k)`,
`x_{-c}(x′) ≥ x_{-c}(v′)`, `x_c(y) ≥ x_c(v)`, and conjugation by `z` preserves `x_c`.
With `(p₁, p₂)` the opposite pair of `v′`, `w = v p₁⁻¹` and `(q₁, q₂)` the opposite pair
of `w`, take `x′ = q₁⁻¹`, `z = (q₁ w q₂)(p₁ v′ p₂)` and
`y = (p₁ v′ p₂)⁻¹ q₂⁻¹ (p₁ v′ p₂) p₂⁻¹`. -/
theorem exists_rankOne_factorization (hT : IsSplitTorus S.toGrp)
    (hfinite : (relativeRoots i).Finite)
    (hspan : Submodule.span ℚ
      (toRat '' (relativeRoots i ∪ Set.range (torusCharacterRestrict i))) = ⊤)
    (hrank : RelativeRoot.HasRankOneFactorization i) (x : D.Apartment)
    {c : characterLattice S} (hc : c ∈ relativeRoots i) (hc' : -c ∈ relativeRoots i)
    {v v' : rationalPoints G} (hv : v ∈ rootGroupPoints i c) (hv1 : v ≠ 1)
    (hv' : v' ∈ rootGroupPoints i (-c)) (hv'1 : v' ≠ 1) {t t' : ℝ}
    (ht : x.val c v = t) (ht' : x.val (-c) v' = t') (hpos : 0 < t + t') :
    ∃ x' ∈ rootGroupPoints i (-c), ∃ z ∈ centralizerPoints i, ∃ y ∈ rootGroupPoints i c,
      v * v' = x' * z * y ∧ (t' : WithTop ℝ) ≤ x.val (-c) x' ∧
        (t : WithTop ℝ) ≤ x.val c y ∧ ∀ g, x.val c (z * g * z⁻¹) = x.val c g := by
  have h := x.isValuation
  have hc0 : c ≠ 0 := hc.1
  have hc'' : -(-c) ∈ relativeRoots i := by rwa [neg_neg]
  -- the opposite pair `(p₁, p₂)` of `v′`
  obtain ⟨p, hp⟩ := ((hrank (-c) hc' v' hv' hv'1).1).exists
  have hp1 : p.1 ∈ rootGroupPoints i (-(-c)) := hp.1
  have hp2 : p.2 ∈ rootGroupPoints i (-(-c)) := hp.2.1
  rw [neg_neg] at hp1 hp2
  have h5p := h.opposite (-c) hc' v' hv' hv'1 p.1 hp.1 p.2 hp.2.1 hp.2.2
  rw [ht', neg_neg] at h5p
  have hp1t := withTop_eq_neg_of_add_eq_zero h5p
  -- `w = v p₁⁻¹` has `x_c(w) = -x_{-c}(v′)`
  have hp1i : x.val c p.1⁻¹ = ((-t' : ℝ) : WithTop ℝ) := by rw [h.apply_inv]; exact hp1t
  have hlt : x.val c p.1⁻¹ < x.val c v := by
    rw [hp1i, ht, WithTop.coe_lt_coe]
    linarith
  have hw : v * p.1⁻¹ ∈ rootGroupPoints i c := Subgroup.mul_mem _ hv (Subgroup.inv_mem _ hp1)
  have hwt : x.val c (v * p.1⁻¹) = ((-t' : ℝ) : WithTop ℝ) := by
    rw [h.apply_mul_eq_right_of_lt hc hv (Subgroup.inv_mem _ hp1) hlt, hp1i]
  have hw1 : v * p.1⁻¹ ≠ 1 := by
    intro h1
    rw [h1, (h.eq_top_iff c hc 1 (Subgroup.one_mem _)).2 rfl] at hwt
    exact WithTop.top_ne_coe hwt
  -- the opposite pair `(q₁, q₂)` of `w`
  obtain ⟨q, hq⟩ := ((hrank c hc (v * p.1⁻¹) hw hw1).1).exists
  have h5q := h.opposite c hc _ hw hw1 q.1 hq.1 q.2 hq.2.1 hq.2.2
  rw [hwt] at h5q
  have hq1t := withTop_eq_neg_of_add_eq_zero h5q
  rw [neg_neg] at hq1t
  -- the normalizer points `m = p₁ v′ p₂` and `n = q₁ w q₂`
  have hmflip := hp.weylAction_eq_neg i hT (neg_ne_zero.2 hc0) hv' hv'1
  have hnflip := hq.weylAction_eq_neg i hT hc0 hw hw1
  have hminv : weylAction i (⟨p.1 * v' * p.2, hp.2.2⟩ : normalizerPoints i)⁻¹ (-c) = c := by
    have := weylAction_inv_apply_apply (⟨p.1 * v' * p.2, hp.2.2⟩ : normalizerPoints i) (-c)
    rw [hmflip, map_neg] at this
    exact neg_inj.1 this
  have hninv : weylAction i (⟨q.1 * (v * p.1⁻¹) * q.2, hq.2.2⟩ : normalizerPoints i)⁻¹ c = -c := by
    have := weylAction_inv_apply_apply (⟨q.1 * (v * p.1⁻¹) * q.2, hq.2.2⟩ :
      normalizerPoints i) c
    rw [hnflip] at this
    exact neg_eq_iff_eq_neg.1 ((map_neg _ c).symm.trans this)
  -- the product `z = n m` acts trivially on characters
  have hZ := weylAction_mul_factorPairs_eq_one hT hfinite hspan hc hw hw1 hv' hv'1 hp hq
  have hzC := (hT.weylAction_eq_one_iff i _).1 hZ
  -- `y ∈ U_c(k)`
  have hy : (p.1 * v' * p.2)⁻¹ * q.2⁻¹ * (p.1 * v' * p.2) * p.2⁻¹ ∈ rootGroupPoints i c := by
    refine Subgroup.mul_mem _ ?_ (Subgroup.inv_mem _ hp2)
    have := conj_mem_rootGroupPoints (⟨p.1 * v' * p.2, hp.2.2⟩ : normalizerPoints i)⁻¹
      (Subgroup.inv_mem _ (hq.2.1 : q.2 ∈ rootGroupPoints i (-c)))
    rw [hminv] at this
    simpa only [Subgroup.coe_inv, inv_inv] using this
  have heq : v * v' = q.1⁻¹ * (q.1 * (v * p.1⁻¹) * q.2 * (p.1 * v' * p.2)) *
      ((p.1 * v' * p.2)⁻¹ * q.2⁻¹ * (p.1 * v' * p.2) * p.2⁻¹) := by group
  have hx' : q.1⁻¹ ∈ rootGroupPoints i (-c) := Subgroup.inv_mem _ hq.1
  refine ⟨q.1⁻¹, hx', _, hzC, _, hy, heq, ?_, ?_, ?_⟩
  · rw [h.apply_inv, hq1t]
  · refine le_val_of_mul_eq hT hrank x hc hc' hv hv1 hv' hx' hzC hy heq ht ?_ hpos
    rw [ht']
  · -- the translation part of `z` vanishes on `c`
    obtain ⟨wm, hwm⟩ := exists_smul_val_eq_vadd
      (⟨p.1 * v' * p.2, hp.2.2⟩ : normalizerPoints i) x
    obtain ⟨wn, hwn⟩ := exists_smul_val_eq_vadd
      (⟨q.1 * (v * p.1⁻¹) * q.2, hq.2.2⟩ : normalizerPoints i) x
    have hevm := eval_translation_eq_of_factor x hc' hc'' hv' hv'1 hp.1 hp.2.1 hp.2.2
      hmflip ht' hwm
    have hevn := eval_translation_eq_of_factor x hc hc' hw hw1 hq.1 hq.2.1 hq.2.2
      hnflip hwt hwn
    have hW : ((⟨q.1 * (v * p.1⁻¹) * q.2, hq.2.2⟩ : normalizerPoints i) *
        ⟨p.1 * v' * p.2, hp.2.2⟩) • x.val =
        ((⟨q.1 * (v * p.1⁻¹) * q.2, hq.2.2⟩ : normalizerPoints i) • wm + wn) +ᵥ x.val := by
      rw [mul_smul, hwm, RootFunctionFamily.smul_vadd, hwn, vadd_vadd]
    have hev : eval S c ((⟨q.1 * (v * p.1⁻¹) * q.2, hq.2.2⟩ : normalizerPoints i) • wm + wn)
        = 0 := by
      rw [map_add, eval_normalizer_smul, hninv, hevm, hevn]
      ring
    exact val_conj_eq_of_eval_eq_zero x hZ hW hev

/-- `U_{b,x,0} ⊆ G(k)^♯_x` for a relative root `b`. -/
theorem filtration_le_sharpFixer (x : D.Apartment) {b : characterLattice S}
    (hb : b ∈ relativeRoots i) : D.filtration x b 0 ≤ D.sharpFixer {x} := by
  rw [← D.rootFixer_singleton]
  exact D.rootFixer_le_sharpFixer ⟨b, hb⟩ {x}

/-- **Rank-one exchange at a chamber point.** For `x` in a chamber and opposite relative
roots `a, -a`, `U_{-a,x,0} U_{a,x,0} ⊆ U_{a,x,0} U_{-a,x,0} Z(k)^♯_x`. At a chamber point
both depths agree, so nonidentity factors have positive valuations and the rank-one
factorization applies; its central factor lies in `G(k)^♯_x` as a product of root
elements of `G(k)^♯_x`. -/
theorem filtration_neg_mul_filtration_subset (hT : IsSplitTorus S.toGrp)
    (hfinite : (relativeRoots i).Finite)
    (hspan : Submodule.span ℚ
      (toRat '' (relativeRoots i ∪ Set.range (torusCharacterRestrict i))) = ⊤)
    (hrank : RelativeRoot.HasRankOneFactorization i)
    (hAS4 : ∀ ψ ∈ D.extendedAffineRoots,
      ψ ∈ D.affineRoots ∨ (2 : ℝ) • ψ ∈ D.affineRoots)
    {C : Set D.Apartment} (hC : AffineRootSystem.IsChamber D.affineRoots C)
    {x : D.Apartment} (hx : x ∈ C) {a : characterLattice S} (ha : a ∈ relativeRoots i)
    (ha' : -a ∈ relativeRoots i) :
    (D.filtration x (-a) 0 : Set (rationalPoints G)) * D.filtration x a 0 ⊆
      (D.filtration x a 0 : Set (rationalPoints G)) * D.filtration x (-a) 0 *
        D.sharpCentralizer {x} := by
  rintro _ ⟨v, hv, v', hv', rfl⟩
  beta_reduce
  by_cases hv1 : v = 1
  · subst hv1
    rw [show (1 : rationalPoints G) * v' = v' * 1 * 1 by group]
    exact Set.mul_mem_mul (Set.mul_mem_mul hv' (one_mem _)) (one_mem _)
  by_cases hv'1 : v' = 1
  · subst hv'1
    rw [show v * (1 : rationalPoints G) = 1 * v * 1 by group]
    exact Set.mul_mem_mul (Set.mul_mem_mul (one_mem _) hv) (one_mem _)
  obtain ⟨t, ht⟩ := exists_val_eq_coe x ha' hv.1 hv1
  obtain ⟨t', ht'⟩ := exists_val_eq_coe x ha hv'.1 hv'1
  have htpos : 0 < t := by
    have := (D.filtration_eq_filtrationPlus_of_mem_chamber hAS4 hC hx ha' ▸ hv :
      v ∈ D.filtrationPlus x (-a) 0)
    rw [mem_filtrationPlus, ht, WithTop.coe_lt_coe] at this
    exact this.2
  have ht'pos : 0 < t' := by
    have := (D.filtration_eq_filtrationPlus_of_mem_chamber hAS4 hC hx ha ▸ hv' :
      v' ∈ D.filtrationPlus x a 0)
    rw [mem_filtrationPlus, ht', WithTop.coe_lt_coe] at this
    exact this.2
  have ha'' : -(-a) ∈ relativeRoots i := by rwa [neg_neg]
  have hv'a : v' ∈ rootGroupPoints i (-(-a)) := by rw [neg_neg]; exact hv'.1
  have ht'a : x.val (-(-a)) v' = t' := by rw [neg_neg]; exact ht'
  obtain ⟨x', hx', z, hz, y, hy, heq, hx't, hyt, hzc⟩ := exists_rankOne_factorization hT
    hfinite hspan hrank x ha' ha'' hv.1 hv1 hv'a hv'1 ht ht'a (by linarith)
  rw [neg_neg] at hx' hx't
  have hzN : z ∈ normalizerPoints i := centralizerPoints_le_normalizerPoints i hz
  have hzW : weylAction i ⟨z, hzN⟩ = 1 := (hT.weylAction_eq_one_iff i ⟨z, hzN⟩).2 hz
  have hzy : z * y * z⁻¹ ∈ rootGroupPoints i (-a) := by
    have := conj_mem_rootGroupPoints (⟨z, hzN⟩ : normalizerPoints i) hy
    rw [hzW] at this
    exact this
  have hx'F : x' ∈ D.filtration x a 0 :=
    ⟨hx', le_trans (WithTop.coe_le_coe.2 ht'pos.le) hx't⟩
  have hyF : y ∈ D.filtration x (-a) 0 :=
    ⟨hy, le_trans (WithTop.coe_le_coe.2 htpos.le) hyt⟩
  have hzS : z ∈ D.sharpFixer {x} := by
    have hz' : z = x'⁻¹ * (v * v') * y⁻¹ := by rw [heq]; group
    rw [hz']
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ ?_)
      (Subgroup.mul_mem _ ?_ ?_)) (Subgroup.inv_mem _ ?_)
    · exact filtration_le_sharpFixer x ha hx'F
    · exact filtration_le_sharpFixer x ha' hv
    · exact filtration_le_sharpFixer x ha hv'
    · exact filtration_le_sharpFixer x ha' hyF
  rw [heq, show x' * z * y = x' * (z * y * z⁻¹) * z by group]
  refine Set.mul_mem_mul (Set.mul_mem_mul hx'F ⟨hzy, ?_⟩) ⟨hz, hzS⟩
  rw [hzc y]
  exact hyF.2

/-- With opposite factor pairs, the opposite of a relative root is a relative root: a
nonidentity root element exists by V 0, and its factor pair gives a reflection. -/
theorem neg_mem_relativeRoots_of_rankOne (hT : IsSplitTorus S.toGrp)
    (hrank : RelativeRoot.HasRankOneFactorization i) (x : D.Apartment)
    {a : characterLattice S} (ha : a ∈ relativeRoots i) : -a ∈ relativeRoots i := by
  obtain ⟨u, hu, hut⟩ := x.isValuation.exists_ne_top ha
  have hu1 : u ≠ 1 := fun h1 => hut ((x.isValuation.eq_top_iff a ha u hu).2 h1)
  obtain ⟨p, hp⟩ := ((hrank a ha u hu hu1).1).exists
  have hflip := hp.weylAction_eq_neg i hT ha.1 hu hu1
  rw [← hflip]
  exact weylAction_mapsTo_relativeRoots i _ ha

end KPApartmentData

/-- The rank-one exchange `U_{-a,x,0} U_{a,x,0} ⊆ U_{a,x,0} U_{-a,x,0} Z(k)^♯_x` at every
point `x` of a chamber, for apartment data over a split torus with opposite factor pairs
(the conclusion of KP Proposition 2.11.17, `RelativeRoot.HasRankOneFactorization`) and
AS 4. -/
def ChamberRankOneExchangeStatement : Prop :=
  ∀ (k : Type u) [Field k] (S : CommGroupScheme (Spec (CommRingCat.of k)))
    (G : GroupScheme (Spec (CommRingCat.of k))) (i : S.toGrp ⟶ G) [Mono i.hom.hom.left]
    [IsAffineHom G.X.hom] (ω : kˣ → ℝ) (D : KPApartmentData i ω),
    IsSplitTorus S.toGrp → (relativeRoots i).Finite →
    Submodule.span ℚ (toRat '' (relativeRoots i ∪ Set.range (torusCharacterRestrict i))) = ⊤ →
    RelativeRoot.HasRankOneFactorization i →
    (∀ ψ ∈ D.extendedAffineRoots, ψ ∈ D.affineRoots ∨ (2 : ℝ) • ψ ∈ D.affineRoots) →
    ∀ (C : Set D.Apartment) (x : D.Apartment) (a : characterLattice S),
      AffineRootSystem.IsChamber D.affineRoots C → x ∈ C → a ∈ relativeRoots i →
      (D.filtration x (-a) 0 : Set (rationalPoints G)) * D.filtration x a 0 ⊆
        (D.filtration x a 0 : Set (rationalPoints G)) * D.filtration x (-a) 0 *
          D.sharpCentralizer {x}

theorem chamberRankOneExchange : ChamberRankOneExchangeStatement.{u} := by
  intro k _ S G i _ _ ω D hT hfinite hspan hrank hAS4 C x a hC hx ha
  exact KPApartmentData.filtration_neg_mul_filtration_subset hT hfinite
    hspan hrank hAS4 hC hx ha (KPApartmentData.neg_mem_relativeRoots_of_rankOne hT hrank x ha)

end Langlands.Geometry.Building
