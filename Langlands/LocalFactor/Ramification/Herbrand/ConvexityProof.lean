import Langlands.LocalFactor.Ramification.Herbrand.SubextensionProof

/-!
# Convexity of the relative inverse Herbrand function

For a finite Galois field `L` over `F` and a subfield `K`, the relative index
`ψ_{K/F} = φ_{L/K} ∘ ψ_{L/F}` satisfies `ψ_{K/F}(t a) ≤ t ψ_{K/F}(a)` for `a ≥ 0` and
`t ∈ [0, 1]`; in particular `ψ_{K/F}(a/2) ≤ ψ_{K/F}(a)/2`. The proof compares the two
Herbrand polygons of `L` through the monotone ratio of the orders of the lower
ramification groups over `K` and over `F`.
-/

noncomputable section

namespace Langlands.Ramification.HerbrandBridge

open _root_.Langlands.Ramification.Herbrand

universe u uK uE uL

section Polygon

/-- The weighted ramp sum `Σ_{i < N} c(i+1) · ramp_i(u)`, the integral of the step function
equal to `c(i+1)` on `(i, i+1]`. -/
def rampSum (c : ℕ → ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  ∑ i ∈ Finset.range N, c (i + 1) * ramp i u

/-- The unit ramps below `B` sum to the identity on `[0, B]`. -/
theorem sum_ramp_eq (B : ℕ) {u : ℝ} (h0 : 0 ≤ u) (hu : u ≤ B) :
    ∑ i ∈ Finset.range B, ramp i u = u := by
  induction B with
  | zero =>
    simp only [Nat.cast_zero] at hu
    simp [le_antisymm hu h0]
  | succ B ih =>
    rw [Finset.sum_range_succ]
    rcases le_or_gt u B with h | h
    · rw [ih h, ramp_eq_zero h, add_zero]
    · have hone : ∀ i ∈ Finset.range B, ramp i u = 1 := by
        intro i hi
        apply ramp_eq_one
        have : (i : ℝ) + 1 ≤ B := by exact_mod_cast Finset.mem_range.mp hi
        linarith
      rw [Finset.sum_congr rfl hone, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        mul_one, ramp_eq_sub h.le (by push_cast at hu; linarith)]
      ring

/-- On `[0, B]`, a polygon whose orders are `1` past its cutoff `b ≤ B` is the weighted
ramp sum. -/
theorem polygon_eq_sum (g : ℕ → ℕ) {b B : ℕ} (hbB : b ≤ B)
    (htail : ∀ i, b ≤ i → g (i + 1) = 1) {u : ℝ} (h0 : 0 ≤ u) (hu : u ≤ B) :
    polygon g b u = rampSum (fun i => (g i : ℝ)) B u / g 0 := by
  rw [polygon_of_nonneg g b h0, rampSum]
  congr 1
  have hext : ∑ i ∈ Finset.range b, ((g (i + 1) : ℝ) - 1) * ramp i u =
      ∑ i ∈ Finset.range B, ((g (i + 1) : ℝ) - 1) * ramp i u := by
    apply Finset.sum_subset (Finset.range_subset_range.mpr hbB)
    intro i _ hi
    rw [htail i (by simpa using hi)]
    simp
  rw [hext]
  calc u + ∑ i ∈ Finset.range B, ((g (i + 1) : ℝ) - 1) * ramp i u
      = ∑ i ∈ Finset.range B, ramp i u +
          ∑ i ∈ Finset.range B, ((g (i + 1) : ℝ) - 1) * ramp i u := by
        rw [sum_ramp_eq B h0 hu]
    _ = ∑ i ∈ Finset.range B, (g (i + 1) : ℝ) * ramp i u := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring

/-- Ratio monotonicity for weighted ramp sums: if `b i / a i` is nondecreasing, then
`B(x)/A(x)` is nondecreasing on `(0, ∞)`. -/
theorem ramp_sum_ratio_mono (a b : ℕ → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 ≤ b i)
    (hmono : ∀ i j, i ≤ j → b i * a j ≤ b j * a i) (N : ℕ) {x y : ℝ}
    (hxy : x ≤ y) :
    rampSum b N x * rampSum a N y ≤ rampSum b N y * rampSum a N x := by
  unfold rampSum
  set k := ⌈x⌉₊
  set c := b k / a k
  have hc : 0 ≤ c := div_nonneg (hb k) (ha k).le
  have hlow : ∀ i, ramp i x ≠ 0 → b (i + 1) ≤ c * a (i + 1) := by
    intro i hi
    have hix : (i : ℝ) < x := by
      by_contra h
      exact hi (ramp_eq_zero (le_of_not_gt h))
    have hik : i + 1 ≤ k := Nat.lt_ceil.mpr hix
    have h := hmono (i + 1) k hik
    rw [div_mul_eq_mul_div, le_div_iff₀ (ha k)]
    linarith
  have hupp : ∀ i, ramp i y - ramp i x ≠ 0 → c * a (i + 1) ≤ b (i + 1) := by
    intro i hi
    have hxi : x < (i : ℝ) + 1 := by
      by_contra h
      have h1 : (i : ℝ) + 1 ≤ x := le_of_not_gt h
      exact hi (by rw [ramp_eq_one h1, ramp_eq_one (h1.trans hxy), sub_self])
    have hki : k ≤ i + 1 := Nat.ceil_le.mpr (by push_cast; exact hxi.le)
    have h := hmono k (i + 1) hki
    rw [div_mul_eq_mul_div, div_le_iff₀ (ha k)]
    linarith
  set Ax := ∑ i ∈ Finset.range N, a (i + 1) * ramp i x
  set Bx := ∑ i ∈ Finset.range N, b (i + 1) * ramp i x
  set dA := ∑ i ∈ Finset.range N, a (i + 1) * (ramp i y - ramp i x)
  set dB := ∑ i ∈ Finset.range N, b (i + 1) * (ramp i y - ramp i x)
  have hAy : ∑ i ∈ Finset.range N, a (i + 1) * ramp i y = Ax + dA := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hBy : ∑ i ∈ Finset.range N, b (i + 1) * ramp i y = Bx + dB := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hAx : 0 ≤ Ax := Finset.sum_nonneg fun i _ => mul_nonneg (ha _).le (ramp_nonneg i x)
  have hdA : 0 ≤ dA := Finset.sum_nonneg fun i _ =>
    mul_nonneg (ha _).le (sub_nonneg.mpr (ramp_monotone i hxy))
  have h1 : Bx ≤ c * Ax := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : ramp i x = 0
    · simp [hi]
    · rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hlow i hi) (ramp_nonneg i x)
  have h2 : c * dA ≤ dB := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : ramp i y - ramp i x = 0
    · simp [hi]
    · rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hupp i hi) (sub_nonneg.mpr (ramp_monotone i hxy))
  rw [hAy, hBy]
  nlinarith [mul_le_mul_of_nonneg_right h1 hdA, mul_le_mul_of_nonneg_left h2 hAx]

end Polygon

section Orders

open _root_.Langlands.Ramification.Padic

variable {p : ℕ} [Fact p.Prime] (K : Type uK) [Field K] [Algebra (Padic p) K]
  (E : Type uE) [Field E] [Algebra (Padic p) E] {L : PadicField.{uL} p}
  [Algebra K E] [Algebra E L.Carrier] [Algebra K L.Carrier]
  [IsScalarTower K E L.Carrier]
  [IsScalarTower (Padic p) K L.Carrier] [IsScalarTower (Padic p) E L.Carrier]
  (T : L.TopologicalData)

/-- The lower groups over `E` are the preimages of those over `K`. -/
theorem lowerRamificationGroup_subfield_eq_comap (i : ℕ) :
    Padic.lowerRamificationGroup T E i =
      (Padic.lowerRamificationGroup T K i).comap
        (AlgEquiv.restrictScalarsHom K : (L.Carrier ≃ₐ[E] L.Carrier) →* _) := by
  ext σ
  exact Iff.rfl

/-- The order of a lower group over `E`, times its relative index, is the order over `K`. -/
theorem lowerGroupOrder_subfield_mul_relIndex (i : ℕ) :
    Padic.lowerGroupOrder T E i *
        (AlgEquiv.restrictScalarsHom K :
          (L.Carrier ≃ₐ[E] L.Carrier) →* (L.Carrier ≃ₐ[K] L.Carrier)).range.relIndex
          (Padic.lowerRamificationGroup T K i) =
      Padic.lowerGroupOrder T K i := by
  set ι : (L.Carrier ≃ₐ[E] L.Carrier) →* (L.Carrier ≃ₐ[K] L.Carrier) :=
    AlgEquiv.restrictScalarsHom K
  have hinj : Function.Injective ι := fun σ τ h => AlgEquiv.ext fun x =>
    congrArg (fun ρ : L.Carrier ≃ₐ[K] L.Carrier => ρ x) h
  have hcard : Padic.lowerGroupOrder T E i =
      Nat.card (ι.range ⊓ Padic.lowerRamificationGroup T K i : Subgroup _) := by
    unfold Padic.lowerGroupOrder
    rw [lowerRamificationGroup_subfield_eq_comap K E T i, ← Subgroup.map_comap_eq,
      Subgroup.card_map_of_injective hinj]
  have h := Subgroup.relIndex_inf_mul_relIndex (⊥ : Subgroup (L.Carrier ≃ₐ[K] L.Carrier))
    ι.range (Padic.lowerRamificationGroup T K i)
  rw [Subgroup.relIndex_bot_left, bot_inf_eq, Subgroup.relIndex_bot_left] at h
  rw [hcard]
  exact h

/-- The ratio of the lower group orders over `E` and over `K` is nondecreasing. -/
theorem lowerGroupOrder_subfield_ratio {i j : ℕ} (hij : i ≤ j) :
    (Padic.lowerGroupOrder T E i : ℝ) * Padic.lowerGroupOrder T K j ≤
      (Padic.lowerGroupOrder T E j : ℝ) * Padic.lowerGroupOrder T K i := by
  have : FiniteDimensional K L.Carrier :=
    Module.Finite.of_restrictScalars_finite (Padic p) K L.Carrier
  set H := (AlgEquiv.restrictScalarsHom K :
    (L.Carrier ≃ₐ[E] L.Carrier) →* (L.Carrier ≃ₐ[K] L.Carrier)).range
  have hi := lowerGroupOrder_subfield_mul_relIndex K E T i
  have hj := lowerGroupOrder_subfield_mul_relIndex K E T j
  have hle : H.relIndex (Padic.lowerRamificationGroup T K j) ≤
      H.relIndex (Padic.lowerRamificationGroup T K i) :=
    Subgroup.relIndex_le_of_le_right (Padic.lowerRamificationGroup_antitone T K hij)
      (Subgroup.index_ne_zero_of_finite)
  rw [← hi, ← hj]
  have hnat : Padic.lowerGroupOrder T E i *
      (Padic.lowerGroupOrder T E j * H.relIndex (Padic.lowerRamificationGroup T K j)) ≤
      Padic.lowerGroupOrder T E j *
        (Padic.lowerGroupOrder T E i * H.relIndex (Padic.lowerRamificationGroup T K i)) := by
    rw [mul_left_comm]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hle)
  exact_mod_cast hnat

/-- On `[0, B]`, with `B` past the cutoff, the Herbrand function is the weighted ramp sum. -/
theorem herbrandPhi_eq_sum (F' : Type uK) [Field F'] [Algebra (Padic p) F'] [Algebra F' L.Carrier]
    [IsScalarTower (Padic p) F' L.Carrier] {B : ℕ} (hB : ramificationCutoff T F' ≤ B) {u : ℝ}
    (h0 : 0 ≤ u) (hu : u ≤ B) :
    Padic.herbrandPhi T F' u =
      rampSum (fun i => (Padic.lowerGroupOrder T F' i : ℝ)) B u / Padic.lowerGroupOrder T F' 0 :=
  polygon_eq_sum _ hB (fun i hi => lowerGroupOrder_tail T F' i hi) h0 hu

/-- Star-shapedness of the relative index: `φ_{L/E}(ψ_{L/K}(t a)) ≤ t φ_{L/E}(ψ_{L/K}(a))`. -/
theorem herbrandPhi_herbrandPsi_mul_le {a t : ℝ} (ha : 0 ≤ a) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Padic.herbrandPhi T E (Padic.herbrandPsi T K (t * a)) ≤
      t * Padic.herbrandPhi T E (Padic.herbrandPsi T K a) := by
  have hφnn : 0 ≤ Padic.herbrandPhi T E (Padic.herbrandPsi T K a) := by
    have h := (Padic.herbrandPhi_strictMono T E).monotone
      ((Padic.herbrandPsi_strictMono T K).monotone ha)
    rwa [Padic.herbrandPsi_zero, Padic.herbrandPhi_zero] at h
  rcases (mul_nonneg ht0 ha).eq_or_lt with h0 | hpos
  · rw [← h0, Padic.herbrandPsi_zero, Padic.herbrandPhi_zero]
    exact mul_nonneg ht0 hφnn
  have hapos : 0 < a := by
    rcases ha.eq_or_lt with h | h
    · rw [← h, mul_zero] at hpos
      exact absurd hpos (lt_irrefl 0)
    · exact h
  have hta : t * a ≤ a := by nlinarith
  set x := Padic.herbrandPsi T K (t * a)
  set y := Padic.herbrandPsi T K a
  have hx : 0 < x := Padic.herbrandPsi_pos T K hpos
  have hxy : x ≤ y := (Padic.herbrandPsi_strictMono T K).monotone hta
  set B := max (ramificationCutoff T K) (max (ramificationCutoff T E) ⌈y⌉₊)
  have hBK : ramificationCutoff T K ≤ B := le_max_left _ _
  have hBE : ramificationCutoff T E ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hyB : y ≤ B := (Nat.le_ceil y).trans (by exact_mod_cast
    (le_max_right _ _ : ⌈y⌉₊ ≤ max (ramificationCutoff T E) ⌈y⌉₊).trans (le_max_right _ _))
  have hxB : x ≤ B := hxy.trans hyB
  have hg0 : (0 : ℝ) < Padic.lowerGroupOrder T K 0 := by exact_mod_cast lowerGroupOrder_pos T K 0
  have hh0 : (0 : ℝ) < Padic.lowerGroupOrder T E 0 := by exact_mod_cast lowerGroupOrder_pos T E 0
  have hAx := herbrandPhi_eq_sum T K hBK hx.le hxB
  have hAy := herbrandPhi_eq_sum T K hBK (hx.le.trans hxy) hyB
  have hBx := herbrandPhi_eq_sum T E hBE hx.le hxB
  have hBy := herbrandPhi_eq_sum T E hBE (hx.le.trans hxy) hyB
  rw [Padic.herbrandPhi_herbrandPsi] at hAx hAy
  have hratio := ramp_sum_ratio_mono (fun i => (Padic.lowerGroupOrder T K i : ℝ))
    (fun i => (Padic.lowerGroupOrder T E i : ℝ))
    (fun i => by exact_mod_cast lowerGroupOrder_pos T K i)
    (fun i => Nat.cast_nonneg _) (fun i j hij => lowerGroupOrder_subfield_ratio K E T hij) B hxy
  rw [eq_div_iff hg0.ne'] at hAx hAy
  rw [eq_div_iff hh0.ne'] at hBx hBy
  rw [← hAx, ← hAy, ← hBx, ← hBy] at hratio
  set g0 : ℝ := ((Padic.lowerGroupOrder T K 0 : ℕ) : ℝ)
  set h0' : ℝ := ((Padic.lowerGroupOrder T E 0 : ℕ) : ℝ)
  have key : (h0' * g0 * a) * Padic.herbrandPhi T E x ≤
      (h0' * g0 * a) * (t * Padic.herbrandPhi T E y) := by
    calc (h0' * g0 * a) * Padic.herbrandPhi T E x
        = (Padic.herbrandPhi T E x * h0') * (a * g0) := by ring
      _ ≤ (Padic.herbrandPhi T E y * h0') * (t * a * g0) := hratio
      _ = (h0' * g0 * a) * (t * Padic.herbrandPhi T E y) := by ring
  exact le_of_mul_le_mul_left key (by positivity)

end Orders

section Relative

open _root_.Langlands.Ramification.Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uK} p) {K : PadicField.{uE} p}
  {Ω : Type uL} [Field Ω] [Algebra F.Carrier Ω] [Algebra K.Carrier Ω] [Algebra (Padic p) Ω]
  [Algebra F.Carrier K.Carrier] [IsScalarTower F.Carrier K.Carrier Ω]
  [IsScalarTower (Padic p) F.Carrier Ω] [IsScalarTower (Padic p) K.Carrier Ω]

attribute [local instance] extension_padicScalarTower

variable {M : FiniteGaloisIntermediateField F.Carrier Ω}
  (h : ∀ x : K.Carrier, algebraMap K.Carrier Ω x ∈ M.toIntermediateField)

theorem relativeIndex_zero : relativeIndex F M h 0 = 0 := by
  unfold relativeIndex
  rw [Padic.herbrandPsi_zero, Padic.herbrandPhi_zero]

theorem relativeIndex_strictMono : StrictMono (relativeIndex F M h) :=
  (Padic.herbrandPhi_strictMono _ _).comp (Padic.herbrandPsi_strictMono _ _)

theorem relativeIndex_continuous : Continuous (relativeIndex F M h) :=
  (Padic.herbrandPhi_continuous _ _).comp (Padic.herbrandPsi_continuous _ _)

/-- Star-shapedness of the relative index on `[0, ∞)`. -/
theorem relativeIndex_mul_le {a t : ℝ} (ha : 0 ≤ a) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    relativeIndex F M h (t * a) ≤ t * relativeIndex F M h a :=
  herbrandPhi_herbrandPsi_mul_le F.Carrier K.Carrier
    (finiteGaloisPadicField K (extendFiniteGalois h)).canonicalTopologicalData ha ht0 ht1

end Relative

section Intermediate

open LocalClassField

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (E : FiniteIntermediateExtension F.Carrier)

attribute [local instance] asPadicField_isScalarTower

theorem relativeHerbrandPsi_zero : relativeHerbrandPsi E 0 = 0 :=
  relativeIndex_zero F (algebraMap_mem_galoisClosure E)

theorem relativeHerbrandPsi_strictMono : StrictMono (relativeHerbrandPsi E) :=
  relativeIndex_strictMono F (algebraMap_mem_galoisClosure E)

theorem relativeHerbrandPsi_continuous : Continuous (relativeHerbrandPsi E) :=
  relativeIndex_continuous F (algebraMap_mem_galoisClosure E)

theorem relativeHerbrandPsi_nonneg {a : ℝ} (ha : 0 ≤ a) : 0 ≤ relativeHerbrandPsi E a := by
  rw [← relativeHerbrandPsi_zero E]
  exact (relativeHerbrandPsi_strictMono E).monotone ha

/-- `ψ_{E/F}(t a) ≤ t ψ_{E/F}(a)` for `a ≥ 0` and `0 ≤ t ≤ 1`. -/
theorem relativeHerbrandPsi_mul_le {a t : ℝ} (ha : 0 ≤ a) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    relativeHerbrandPsi E (t * a) ≤ t * relativeHerbrandPsi E a :=
  relativeIndex_mul_le F (algebraMap_mem_galoisClosure E) ha ht0 ht1

/-- The inequality `ψ_{E/F}(a/2) ≤ ψ_{E/F}(a)/2` used in Deligne–Henniart 4.8. -/
theorem relativeHerbrandPsi_half_le {a : ℝ} (ha : 0 ≤ a) :
    relativeHerbrandPsi E (a / 2) ≤ relativeHerbrandPsi E a / 2 := by
  have h := relativeHerbrandPsi_mul_le E ha (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 : ℝ) / 2 ≤ 1)
  rw [show (1 : ℝ) / 2 * a = a / 2 by ring] at h
  linarith

end Intermediate

end Langlands.Ramification.HerbrandBridge
