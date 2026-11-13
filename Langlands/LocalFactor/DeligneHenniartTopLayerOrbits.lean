import Langlands.LocalFactor.DeligneHenniartTopLayerTrace

/-!
# Fixed fields, stabilizers and ramp sums for the top-layer congruence

Auxiliary facts for the proof of `TopLayerNormTraceStatement`:

* comparison lemmas for the weighted ramp sums `rampSum` that express the integrals
  `∫_0^t |J_s| ds` of lower group orders;
* the fixed field of a subgroup `J ≤ Gal(M/K)` as a p-adic field, the orders of its lower
  ramification groups (`|J ∩ G_i|`), and the trace of a `J`-invariant element as an orbit sum;
* for a transitive action of a finite group with point stabilizer `H` and a normal subgroup
  `N`, the stabilizer of a `k`-element subset meets `N` in at most `k |H ∩ N|` elements, with
  equality `|N| = |H ∩ N|` when `N ≤ H`.
-/

noncomputable section

namespace Langlands.LocalFactor.NonabelianSystem.DeligneHenniart.TopLayer

open Ramification.Padic Ramification.HerbrandBridge

/-! ## Ramp sums -/

/-- `rampSum` is linear in its weights: differences. -/
theorem rampSum_sub (a b : ℕ → ℝ) (N : ℕ) (t : ℝ) :
    rampSum (fun i => a i - b i) N t = rampSum a N t - rampSum b N t := by
  unfold rampSum
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `rampSum` is linear in its weights: scalar multiples. -/
theorem rampSum_const_mul (k : ℝ) (a : ℕ → ℝ) (N : ℕ) (t : ℝ) :
    rampSum (fun i => k * a i) N t = k * rampSum a N t := by
  unfold rampSum
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- A weighted ramp sum with nonnegative weights is nonnegative. -/
theorem rampSum_nonneg (c : ℕ → ℝ) (hc : ∀ i, 0 ≤ c i) (N : ℕ) (t : ℝ) :
    0 ≤ rampSum c N t :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hc _) (Ramification.Herbrand.ramp_nonneg i t)

/-- With weights at least one, a weighted ramp sum grows at least as fast as its argument on
`[0, N]`. -/
theorem sub_le_rampSum_sub (c : ℕ → ℝ) (hc : ∀ i, 1 ≤ c i) (N : ℕ) {x y : ℝ} (hy : 0 ≤ y)
    (hxy : y ≤ x) (hx : x ≤ N) :
    x - y ≤ rampSum c N x - rampSum c N y := by
  have hsx := sum_ramp_eq N (hy.trans hxy) hx
  have hsy := sum_ramp_eq N hy (hxy.trans hx)
  unfold rampSum
  rw [← Finset.sum_sub_distrib]
  conv_lhs => rw [← hsx, ← hsy, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hm := Ramification.Herbrand.ramp_monotone i hxy
  nlinarith [hc (i + 1)]

/-- A weighted ramp sum with nonnegative weights is positive as soon as one weight `c (i₀ + 1)`
with `i₀ < N` is positive and `t > i₀`. -/
theorem rampSum_pos (c : ℕ → ℝ) (hc : ∀ i, 0 ≤ c i) (N : ℕ) {t : ℝ} {i₀ : ℕ} (hi : i₀ < N)
    (hpos : 0 < c (i₀ + 1)) (ht : (i₀ : ℝ) < t) :
    0 < rampSum c N t := by
  unfold rampSum
  have hramp : 0 < Ramification.Herbrand.ramp i₀ t :=
    lt_min one_pos (lt_max_of_lt_right (sub_pos.mpr ht))
  calc (0 : ℝ) < c (i₀ + 1) * Ramification.Herbrand.ramp i₀ t := mul_pos hpos hramp
    _ ≤ ∑ i ∈ Finset.range N, c (i + 1) * Ramification.Herbrand.ramp i t :=
      Finset.single_le_sum (f := fun i => c (i + 1) * Ramification.Herbrand.ramp i t)
        (fun i _ => mul_nonneg (hc _) (Ramification.Herbrand.ramp_nonneg i t))
        (Finset.mem_range.mpr hi)

/-! ## Fixed fields as p-adic fields -/

section FixedField

universe u w

variable {p : ℕ} [Fact p.Prime] {K : PadicField.{u} p} {M : PadicField.{w} p}
  [Algebra K.Carrier M.Carrier] [IsScalarTower (Padic p) K.Carrier M.Carrier]
  [FiniteDimensional K.Carrier M.Carrier]

/-- The fixed field of a subgroup of `Gal(M/K)`, as a p-adic field. -/
abbrev fixedPadicField (J : Subgroup (M.Carrier ≃ₐ[K.Carrier] M.Carrier)) : PadicField.{w} p where
  Carrier := IntermediateField.fixedField J
  finiteDimensional :=
    FiniteDimensional.trans (Padic p) K.Carrier (IntermediateField.fixedField J)

variable [IsGalois K.Carrier M.Carrier]

omit [IsGalois K.Carrier M.Carrier] in
/-- An automorphism over `K` is linear over the fixed field of `J` exactly when it lies
in `J`. -/
theorem range_restrictScalarsHom_fixedPadicField
    (J : Subgroup (M.Carrier ≃ₐ[K.Carrier] M.Carrier)) :
    (AlgEquiv.restrictScalarsHom K.Carrier :
      (M.Carrier ≃ₐ[(fixedPadicField J).Carrier] M.Carrier) →*
        (M.Carrier ≃ₐ[K.Carrier] M.Carrier)).range = J := by
  ext σ
  have hJ := IntermediateField.fixingSubgroup_fixedField J
  conv_rhs => rw [← hJ]
  rw [IntermediateField.mem_fixingSubgroup_iff, MonoidHom.mem_range]
  constructor
  · rintro ⟨τ, rfl⟩ x hx
    exact τ.commutes ⟨x, hx⟩
  · intro h
    exact ⟨{ σ.toRingEquiv with commutes' := fun x => h x x.2 }, AlgEquiv.ext fun _ => rfl⟩

omit [IsGalois K.Carrier M.Carrier] in
/-- The lower group orders of `M` over the fixed field of `J` are `|J ∩ G_i|`. -/
theorem lowerGroupOrder_fixedPadicField (TM : M.TopologicalData)
    (J : Subgroup (M.Carrier ≃ₐ[K.Carrier] M.Carrier)) (i : ℕ) :
    lowerGroupOrder TM (fixedPadicField J).Carrier i =
      Nat.card (J ⊓ lowerRamificationGroup TM K.Carrier i : Subgroup _) := by
  set ι : (M.Carrier ≃ₐ[(fixedPadicField J).Carrier] M.Carrier) →*
      (M.Carrier ≃ₐ[K.Carrier] M.Carrier) := AlgEquiv.restrictScalarsHom K.Carrier
  have hinj : Function.Injective ι := fun σ τ h => AlgEquiv.ext fun x =>
    congrArg (fun ρ : M.Carrier ≃ₐ[K.Carrier] M.Carrier => ρ x) h
  unfold lowerGroupOrder
  rw [Ramification.HerbrandBridge.lowerRamificationGroup_subfield_eq_comap K.Carrier
      (fixedPadicField J).Carrier TM i, ← Subgroup.card_map_of_injective hinj,
    Subgroup.map_comap_eq, range_restrictScalarsHom_fixedPadicField J]

/-- For `z` fixed by `J`, the sum of the conjugates of `z` over `Gal(M/K)` is
`|J| Tr_{F/K}(z)`, with `F` the fixed field of `J`. -/
theorem sum_algEquiv_apply_eq_card_mul_trace
    (J : Subgroup (M.Carrier ≃ₐ[K.Carrier] M.Carrier)) (z : (fixedPadicField J).Carrier) :
    ∑ σ : M.Carrier ≃ₐ[K.Carrier] M.Carrier, σ (z : M.Carrier) =
      (Nat.card J : M.Carrier) * algebraMap K.Carrier M.Carrier
        (Algebra.trace K.Carrier (fixedPadicField J).Carrier z) := by
  rw [← trace_eq_sum_automorphisms,
    ← Algebra.trace_trace (S := (fixedPadicField J).Carrier),
    show (z : M.Carrier) = algebraMap (fixedPadicField J).Carrier M.Carrier z from rfl,
    Algebra.trace_algebraMap, IntermediateField.finrank_fixedField_eq_card, map_nsmul,
    map_nsmul, nsmul_eq_mul]

end FixedField

/-! ## Stabilizers of finite subsets -/

section Stabilizer

open scoped Pointwise

variable {G X : Type*} [Group G] [MulAction G X]

/-- The stabilizer of `g • x₀` meets a normal subgroup `N` in as many elements as the
stabilizer of `x₀`. -/
theorem card_stabilizer_smul_inf (N : Subgroup G) [hN : N.Normal] (x₀ : X) (g : G) :
    Nat.card (MulAction.stabilizer G (g • x₀) ⊓ N : Subgroup G) =
      Nat.card (MulAction.stabilizer G x₀ ⊓ N : Subgroup G) := by
  refine Nat.card_congr
    { toFun := fun h => ⟨g⁻¹ * h * g, ?_⟩
      invFun := fun k => ⟨g * k * g⁻¹, ?_⟩
      left_inv := fun h => Subtype.ext (by simp [mul_assoc])
      right_inv := fun k => Subtype.ext (by simp [mul_assoc]) }
  · obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp h.2
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [MulAction.mem_stabilizer_iff] at h1 ⊢
      rw [mul_smul, mul_smul, h1, inv_smul_smul]
    · simpa using hN.conj_mem _ h2 g⁻¹
  · obtain ⟨k1, k2⟩ := Subgroup.mem_inf.mp k.2
    refine Subgroup.mem_inf.mpr ⟨?_, hN.conj_mem _ k2 g⟩
    rw [MulAction.mem_stabilizer_iff] at k1 ⊢
    rw [mul_smul, mul_smul, inv_smul_smul, k1]

/-- Under a transitive action with point stabilizer `Stab(x₀)`, the stabilizer of a nonempty
finite set `S` meets a normal subgroup `N` in at most `|S| |Stab(x₀) ∩ N|` elements. -/
theorem card_stabilizer_finset_inf_le [Finite G] [DecidableEq X] (N : Subgroup G) [N.Normal] (x₀ : X)
    (htrans : ∀ x : X, ∃ g : G, g • x₀ = x) (S : Finset X) (hS : S.Nonempty) :
    Nat.card (MulAction.stabilizer G S ⊓ N : Subgroup G) ≤
      S.card * Nat.card (MulAction.stabilizer G x₀ ⊓ N : Subgroup G) := by
  obtain ⟨x, hx⟩ := hS
  obtain ⟨g, rfl⟩ := htrans x
  set T := (MulAction.stabilizer G S ⊓ N : Subgroup G)
  have horb : Nat.card (MulAction.orbit T (g • x₀)) *
      Nat.card (MulAction.stabilizer T (g • x₀)) = Nat.card T := by
    rw [Nat.card_coe_set_eq, ← MulAction.index_stabilizer, mul_comm]
    exact Subgroup.card_mul_index _
  have h1 : Nat.card (MulAction.orbit T (g • x₀)) ≤ S.card := by
    have hsub : MulAction.orbit T (g • x₀) ⊆ (S : Set X) := by
      rintro _ ⟨t, rfl⟩
      have ht : (t : G) • S = S := (Subgroup.mem_inf.mp t.2).1
      change (t : G) • (g • x₀) ∈ (S : Set X)
      rw [← ht, Finset.coe_smul_finset]
      exact Set.smul_mem_smul_set hx
    calc Nat.card (MulAction.orbit T (g • x₀)) = (MulAction.orbit T (g • x₀)).ncard := rfl
      _ ≤ (S : Set X).ncard := Set.ncard_le_ncard hsub S.finite_toSet
      _ = S.card := Set.ncard_coe_finset S
  have h2 : Nat.card (MulAction.stabilizer T (g • x₀)) ≤
      Nat.card (MulAction.stabilizer G (g • x₀) ⊓ N : Subgroup G) := by
    refine Nat.card_le_card_of_injective
      (fun t => ⟨((t : T) : G), Subgroup.mem_inf.mpr ⟨?_, (Subgroup.mem_inf.mp (t : T).2).2⟩⟩) ?_
    · exact t.2
    · intro a b h
      apply Subtype.ext
      apply Subtype.ext
      simpa using congrArg Subtype.val h
  rw [card_stabilizer_smul_inf N x₀ g] at h2
  rw [← horb]
  exact Nat.mul_le_mul h1 h2

/-- If a normal subgroup `N` fixes `x₀` under a transitive action, it fixes every point, hence
lies in the stabilizer of every finite set. -/
theorem le_stabilizer_finset [DecidableEq X] (N : Subgroup G) [hN : N.Normal] (x₀ : X)
    (htrans : ∀ x : X, ∃ g : G, g • x₀ = x) (hle : N ≤ MulAction.stabilizer G x₀)
    (S : Finset X) : N ≤ MulAction.stabilizer G S := by
  intro n hn
  have hfix : ∀ x : X, n • x = x := by
    intro x
    obtain ⟨g, rfl⟩ := htrans x
    have hc : g⁻¹ * n * g ∈ MulAction.stabilizer G x₀ := hle (by simpa using hN.conj_mem n hn g⁻¹)
    rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, inv_smul_eq_iff] at hc
    exact hc
  rw [MulAction.mem_stabilizer_iff]
  ext x
  rw [Finset.mem_smul_finset]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [hfix y]
  · intro hx
    exact ⟨x, hx, hfix x⟩

end Stabilizer

end Langlands.LocalFactor.NonabelianSystem.DeligneHenniart.TopLayer
