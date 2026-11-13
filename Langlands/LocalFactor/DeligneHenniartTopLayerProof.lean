import Langlands.LocalFactor.DeligneHenniartTopLayerStatement
import Langlands.LocalFactor.DeligneHenniartTopLayerOrbits
import Langlands.LocalFactor.DeligneHenniartOrbitAlgebra

/-!
# Proof of the top-layer norm–trace congruence (DH81 Corollary 3.12(i))

Let `X` be the set of `K`-embeddings of `L` into `M` and `G = Gal(M/K)`. Then
`N(1 + y) - 1 - Tr y = Σ_{S ⊆ X, |S| ≥ 2} Π_{x ∈ S} x(y)`. Group the subsets `S` into
`G`-orbits: the orbit sum of `P_S = Π_{x ∈ S} x(y)` is `Tr_{F_S/K}(P_S)`, where `F_S` is the
fixed field of the stabilizer `G_S` of `S`. Since `|G_S ∩ G_i| ≤ |S| |H ∩ G_i|` for the lower
ramification groups `G_i` and `H = Gal(M/L)`, with strict inequality at `i = ⌈ψ_{M/K}(n)⌉`
(there `G_i ⊆ H` acts trivially on `X`), the trace bound of `DeligneHenniartTopLayerTrace`
applies to every orbit. The trace conclusion is the same bound for `F = L` at level `n - 1`.
-/

noncomputable section

namespace Langlands.LocalFactor.NonabelianSystem.DeligneHenniart.TopLayer

open Ramification.Padic Ramification.HerbrandBridge PadicField.TopologicalData
open scoped Pointwise

/-! ## Embeddings into a Galois extension -/

section Embeddings

variable {K L M : Type*} [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M]

/-- `Gal(M/K)` acts on the `K`-embeddings of `L` into `M` by composition. -/
abbrev embeddingAction : MulAction (M ≃ₐ[K] M) (L →ₐ[K] M) where
  smul g x := g.toAlgHom.comp x
  one_smul x := by
    ext
    rfl
  mul_smul g h x := by
    ext
    rfl

attribute [local instance] embeddingAction

theorem smul_embedding_apply (g : M ≃ₐ[K] M) (x : L →ₐ[K] M) (a : L) :
    (g • x) a = g (x a) := rfl

variable [Algebra L M] [IsScalarTower K L M]

/-- The stabilizer of the inclusion `L → M` is the image of `Gal(M/L)`. -/
theorem stabilizer_inclusion_eq_range :
    MulAction.stabilizer (M ≃ₐ[K] M) (IsScalarTower.toAlgHom K L M) =
      (AlgEquiv.restrictScalarsHom K : (M ≃ₐ[L] M) →* (M ≃ₐ[K] M)).range := by
  ext σ
  rw [MulAction.mem_stabilizer_iff, MonoidHom.mem_range]
  constructor
  · intro h
    refine ⟨{ σ.toRingEquiv with commutes' := fun a => ?_ }, AlgEquiv.ext fun _ => rfl⟩
    exact congrArg (fun f : L →ₐ[K] M => f a) h
  · rintro ⟨τ, rfl⟩
    ext a
    exact τ.commutes a

end Embeddings

/-- `Π (1 + f i) - 1 - Σ f i` is the sum of `Π_{i ∈ S} f i` over the subsets with at least
two elements. -/
theorem prod_one_add_sub_one_sub_sum {ι R : Type*} [CommRing R] [DecidableEq ι]
    (s : Finset ι) (f : ι → R) :
    ∏ i ∈ s, (1 + f i) - 1 - ∑ i ∈ s, f i =
      ∑ S ∈ s.powerset.filter (fun S => 2 ≤ S.card), ∏ i ∈ S, f i := by
  rw [Finset.prod_one_add,
    ← Finset.sum_filter_add_sum_filter_not s.powerset (fun S => 2 ≤ S.card)]
  have hsmall : s.powerset.filter (fun S => ¬ 2 ≤ S.card) =
      s.powersetCard 0 ∪ s.powersetCard 1 := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_union,
      Finset.mem_powersetCard]
    constructor
    · rintro ⟨h, hc⟩
      rcases (by omega : S.card = 0 ∨ S.card = 1) with h0 | h1
      · exact Or.inl ⟨h, h0⟩
      · exact Or.inr ⟨h, h1⟩
    · rintro (⟨h, h0⟩ | ⟨h, h1⟩)
      · exact ⟨h, by omega⟩
      · exact ⟨h, by omega⟩
  have hdisj : Disjoint (s.powersetCard 0) (s.powersetCard 1) := by
    rw [Finset.disjoint_left]
    intro S h0 h1
    rw [Finset.mem_powersetCard] at h0 h1
    omega
  rw [hsmall, Finset.sum_union hdisj, Finset.powersetCard_zero, Finset.powersetCard_one,
    Finset.sum_singleton, Finset.prod_empty, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, Finset.prod_singleton]
  ring

/-! ## The p-adic setting -/

section Padic

universe u v w

variable {p : ℕ} [Fact p.Prime] {K : PadicField.{u} p} {L : PadicField.{v} p}
  {M : PadicField.{w} p}
  [Algebra K.Carrier L.Carrier] [Algebra L.Carrier M.Carrier] [Algebra K.Carrier M.Carrier]
  [IsScalarTower K.Carrier L.Carrier M.Carrier]
  [IsScalarTower (Padic p) K.Carrier L.Carrier] [IsScalarTower (Padic p) L.Carrier M.Carrier]
  [IsScalarTower (Padic p) K.Carrier M.Carrier]
  [FiniteDimensional K.Carrier L.Carrier] [FiniteDimensional K.Carrier M.Carrier]
  [IsGalois K.Carrier M.Carrier]
  (TK : K.TopologicalData) (TL : L.TopologicalData) (TM : M.TopologicalData)

attribute [local instance] embeddingAction

omit [IsScalarTower (Padic p) K.Carrier L.Carrier] [FiniteDimensional K.Carrier L.Carrier]
  [FiniteDimensional K.Carrier M.Carrier] [IsGalois K.Carrier M.Carrier] in
/-- The lower group orders of `M` over `L` are `|H ∩ G_i|`, with `H` the stabilizer of the
inclusion of `L`. -/
theorem lowerGroupOrder_eq_card_stabilizer_inf (i : ℕ) :
    lowerGroupOrder TM L.Carrier i =
      Nat.card (MulAction.stabilizer (M.Carrier ≃ₐ[K.Carrier] M.Carrier)
        (IsScalarTower.toAlgHom K.Carrier L.Carrier M.Carrier) ⊓
          lowerRamificationGroup TM K.Carrier i : Subgroup _) := by
  have hinj : Function.Injective (AlgEquiv.restrictScalarsHom K.Carrier :
      (M.Carrier ≃ₐ[L.Carrier] M.Carrier) →* (M.Carrier ≃ₐ[K.Carrier] M.Carrier)) :=
    fun σ τ h => AlgEquiv.ext fun x =>
      congrArg (fun ρ : M.Carrier ≃ₐ[K.Carrier] M.Carrier => ρ x) h
  unfold lowerGroupOrder
  rw [Ramification.HerbrandBridge.lowerRamificationGroup_subfield_eq_comap K.Carrier L.Carrier
      TM i, ← Subgroup.card_map_of_injective hinj, Subgroup.map_comap_eq,
    stabilizer_inclusion_eq_range]

omit [IsScalarTower (Padic p) K.Carrier L.Carrier] [IsScalarTower (Padic p) L.Carrier M.Carrier]
  [IsScalarTower (Padic p) K.Carrier M.Carrier] [FiniteDimensional K.Carrier L.Carrier]
  [FiniteDimensional K.Carrier M.Carrier] in
/-- Every embedding of `L` is a Galois translate of the inclusion. -/
theorem exists_smul_inclusion (x : L.Carrier →ₐ[K.Carrier] M.Carrier) :
    ∃ g : M.Carrier ≃ₐ[K.Carrier] M.Carrier,
      g • IsScalarTower.toAlgHom K.Carrier L.Carrier M.Carrier = x :=
  exists_automorphism_extending_embedding K.Carrier L.Carrier M.Carrier x

omit [IsScalarTower (Padic p) K.Carrier L.Carrier] [IsScalarTower (Padic p) L.Carrier M.Carrier]
  [FiniteDimensional K.Carrier L.Carrier] [FiniteDimensional K.Carrier M.Carrier] in
/-- Embeddings of `L` do not change the order of `M`. -/
theorem ord_embedding_apply (x : L.Carrier →ₐ[K.Carrier] M.Carrier) (a : L.Carrier) :
    TM.ord (x a) = TM.ord (algebraMap L.Carrier M.Carrier a) := by
  obtain ⟨g, rfl⟩ := exists_smul_inclusion x
  exact ord_algEquiv_apply TM g _

omit [IsScalarTower (Padic p) K.Carrier L.Carrier] [IsScalarTower (Padic p) L.Carrier M.Carrier]
  [FiniteDimensional K.Carrier L.Carrier] [FiniteDimensional K.Carrier M.Carrier] in
/-- `P_S = Π_{x ∈ S} x(y)` is nonzero of order `|S| ord_M(y)`. -/
theorem prod_embeddings_ord {y : L.Carrier} (hy : y ≠ 0)
    (S : Finset (L.Carrier →ₐ[K.Carrier] M.Carrier)) :
    (∏ x ∈ S, x y) ≠ 0 ∧
      TM.ord (∏ x ∈ S, x y) = S.card * TM.ord (algebraMap L.Carrier M.Carrier y) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [TM.ord_one]
  | insert x S hx ih =>
    obtain ⟨h0, hord⟩ := ih
    have hxy : x y ≠ 0 := (map_ne_zero x).mpr hy
    rw [Finset.prod_insert hx, Finset.card_insert_of_notMem hx]
    refine ⟨mul_ne_zero hxy h0, ?_⟩
    rw [TM.ord_mul hxy h0, hord, ord_embedding_apply TM x y]
    push_cast
    ring

omit [Algebra L.Carrier M.Carrier] [IsScalarTower K.Carrier L.Carrier M.Carrier]
  [IsScalarTower (Padic p) K.Carrier L.Carrier] [IsScalarTower (Padic p) L.Carrier M.Carrier]
  [IsScalarTower (Padic p) K.Carrier M.Carrier] [FiniteDimensional K.Carrier L.Carrier]
  [FiniteDimensional K.Carrier M.Carrier] [IsGalois K.Carrier M.Carrier] in
/-- `g(P_S) = P_{g S}`. -/
theorem algEquiv_prod_embeddings [DecidableEq (L.Carrier →ₐ[K.Carrier] M.Carrier)]
    (g : M.Carrier ≃ₐ[K.Carrier] M.Carrier) (y : L.Carrier)
    (S : Finset (L.Carrier →ₐ[K.Carrier] M.Carrier)) :
    g (∏ x ∈ S, x y) = ∏ x ∈ g • S, x y := by
  rw [map_prod, Finset.smul_finset_def, Finset.prod_image fun a _ b _ h =>
    MulAction.injective g h]
  rfl

omit [IsScalarTower (Padic p) K.Carrier L.Carrier] in
/-- The orbit step: for `|S| ≥ 2`, the sum of `P_T` over the `Gal(M/K)`-orbit of `S` is the
image of an element of `K` of order at least `n + 1`. -/
theorem exists_orbit_sum_eq [DecidableEq (L.Carrier →ₐ[K.Carrier] M.Carrier)]
    (n N c : ℕ) (hcut : ramificationCutoff TM K.Carrier ≤ N)
    (htN : herbrandPsi TM K.Carrier n ≤ N) (hc1 : (c : ℝ) - 1 < herbrandPsi TM K.Carrier n)
    (hc0 : 1 ≤ c) (hcN : c ≤ N)
    (hcH : lowerRamificationGroup TM K.Carrier c ≤
      MulAction.stabilizer (M.Carrier ≃ₐ[K.Carrier] M.Carrier)
        (IsScalarTower.toAlgHom K.Carrier L.Carrier M.Carrier))
    {y : L.Carrier} (hy : y ≠ 0)
    (hyR : rampSum (fun i => (lowerGroupOrder TM L.Carrier i : ℝ)) N
        (herbrandPsi TM K.Carrier n) ≤ TM.ord (algebraMap L.Carrier M.Carrier y))
    (S : Finset (L.Carrier →ₐ[K.Carrier] M.Carrier)) (hS : 2 ≤ S.card) :
    ∃ k ∈ TK.additiveLattice (-((n : ℤ) + 1)),
      ∑ T ∈ (MulAction.orbit (M.Carrier ≃ₐ[K.Carrier] M.Carrier) S).toFinite.toFinset,
          ∏ x ∈ T, x y = algebraMap K.Carrier M.Carrier k := by
  set J := MulAction.stabilizer (M.Carrier ≃ₐ[K.Carrier] M.Carrier) S with hJ
  set t := herbrandPsi TM K.Carrier n with ht
  set P := ∏ x ∈ S, x y with hP
  have hPfix : P ∈ IntermediateField.fixedField J := by
    rw [IntermediateField.mem_fixedField_iff]
    intro g hg
    rw [hP, algEquiv_prod_embeddings g y S, MulAction.mem_stabilizer_iff.mp hg]
  obtain ⟨hP0, hPord⟩ := prod_embeddings_ord TM hy S
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  have hj : ∀ i, (lowerGroupOrder TM (fixedPadicField J).Carrier i : ℝ) ≤
      S.card * (lowerGroupOrder TM L.Carrier i : ℝ) := by
    intro i
    rw [lowerGroupOrder_fixedPadicField, lowerGroupOrder_eq_card_stabilizer_inf (K := K) TM i]
    exact_mod_cast card_stabilizer_finset_inf_le (lowerRamificationGroup TM K.Carrier i)
      (IsScalarTower.toAlgHom K.Carrier L.Carrier M.Carrier) exists_smul_inclusion S hSne
  have hjc : lowerGroupOrder TM (fixedPadicField J).Carrier c =
      lowerGroupOrder TM L.Carrier c := by
    rw [lowerGroupOrder_fixedPadicField, lowerGroupOrder_eq_card_stabilizer_inf (K := K) TM c,
      inf_eq_right.mpr (le_stabilizer_finset _ _ exists_smul_inclusion hcH S),
      inf_eq_right.mpr hcH]
  have hpos : 0 < rampSum (fun i => (S.card : ℝ) * lowerGroupOrder TM L.Carrier i -
      lowerGroupOrder TM (fixedPadicField J).Carrier i) N t := by
    refine rampSum_pos _ (fun i => sub_nonneg.mpr (hj i)) N (i₀ := c - 1) (by omega) ?_ ?_
    · rw [Nat.sub_add_cancel hc0, hjc]
      have h1 : (0 : ℝ) < lowerGroupOrder TM L.Carrier c := by
        exact_mod_cast lowerGroupOrder_pos TM L.Carrier c
      have h2 : (2 : ℝ) ≤ S.card := by exact_mod_cast hS
      nlinarith
    · rw [Nat.cast_sub hc0]
      push_cast
      linarith
  rw [rampSum_sub, rampSum_const_mul] at hpos
  have hlt : rampSum (fun i => (lowerGroupOrder TM (fixedPadicField J).Carrier i : ℝ)) N t <
      TM.ord (algebraMap (fixedPadicField J).Carrier M.Carrier ⟨P, hPfix⟩) := by
    change _ < ((TM.ord P : ℤ) : ℝ)
    rw [hPord]
    push_cast
    have h2 : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hyR h2]
  have htr := trace_mem_additiveLattice (F := fixedPadicField J) TK TM n N hcut htN
    (⟨P, hPfix⟩ : IntermediateField.fixedField J) (fun h => hP0 (congrArg Subtype.val h)) hlt
  refine ⟨_, htr, ?_⟩
  have hD2 := sum_action_eq_card_stabilizer_nsmul (M.Carrier ≃ₐ[K.Carrier] M.Carrier)
    (Finset (L.Carrier →ₐ[K.Carrier] M.Carrier)) M.Carrier (fun T => ∏ x ∈ T, x y) S
  have hsum := sum_algEquiv_apply_eq_card_mul_trace J
    (⟨P, hPfix⟩ : IntermediateField.fixedField J)
  have hg : ∀ g : M.Carrier ≃ₐ[K.Carrier] M.Carrier,
      (fun T => ∏ x ∈ T, x y) (g • S) = g P := fun g => (algEquiv_prod_embeddings g y S).symm
  simp only [hg] at hD2
  rw [hD2, nsmul_eq_mul] at hsum
  have : CharZero M.Carrier := Algebra.charZero_of_charZero (Padic p) M.Carrier
  have hJ0 : (Nat.card J : M.Carrier) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  exact mul_left_cancel₀ hJ0 hsum

end Padic

/-! ## The main theorem -/

universe u v w

attribute [local instance] embeddingAction

/-- **Deligne–Henniart 1981, Corollary 3.12(i).** For `L/K` inside a finite Galois `M/K`, an
integer `n ≥ 1` with `G^w ⊆ Gal(M/L)` for some `w < n`, and `y ∈ L` with
`ord_L y ≥ φ_{M/L}(ψ_{M/K}(n))`: `ord_K(Tr y) ≥ n` and `N(1 + y) ≡ 1 + Tr y` modulo
`U_K^{n+1}`. -/
theorem topLayerNormTrace : TopLayerNormTraceStatement.{u, v, w} := by
  intro p _ K L M _ _ _ _ _ _ _ _ _ _ TK TL TM n hn hw y hy0 hy
  classical
  have : FiniteDimensional L.Carrier M.Carrier :=
    Module.Finite.of_restrictScalars_finite (Padic p) L.Carrier M.Carrier
  have : IsGalois L.Carrier M.Carrier :=
    IsGalois.tower_top_of_isGalois K.Carrier L.Carrier M.Carrier
  have : CharZero K.Carrier := Algebra.charZero_of_charZero (Padic p) K.Carrier
  have : Algebra.IsSeparable K.Carrier L.Carrier := Algebra.IsAlgebraic.isSeparable_of_perfectField
  set t := herbrandPsi TM K.Carrier n with ht
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have ht0 : 0 < t := herbrandPsi_pos TM K.Carrier hn'
  set c := ⌈t⌉₊ with hc
  have hc0 : 1 ≤ c := Nat.one_le_ceil_iff.mpr ht0
  have hc1 : (c : ℝ) - 1 < t := by
    have := Nat.ceil_lt_add_one ht0.le
    linarith
  have htc : t ≤ c := Nat.le_ceil t
  set N := ramificationCutoff TM K.Carrier + ramificationCutoff TM L.Carrier + c with hN
  have hcutK : ramificationCutoff TM K.Carrier ≤ N := by omega
  have hcutL : ramificationCutoff TM L.Carrier ≤ N := by omega
  have hcN : c ≤ N := by omega
  have htN : t ≤ N := htc.trans (by exact_mod_cast hcN)
  -- `G_c` fixes `L`
  obtain ⟨w', hwn, hwfix⟩ := hw
  have hcH : lowerRamificationGroup TM K.Carrier c ≤
      MulAction.stabilizer (M.Carrier ≃ₐ[K.Carrier] M.Carrier)
        (IsScalarTower.toAlgHom K.Carrier L.Carrier M.Carrier) := by
    intro σ hσ
    have hσw : σ ∈ upperRamificationGroup TM K.Carrier w' := by
      have hle : herbrandPsi TM K.Carrier w' ≤ c :=
        (herbrandPsi_strictMono TM K.Carrier hwn).le.trans htc
      have hanti := lowerRamificationGroupReal_antitone TM K.Carrier hle
      rw [lowerRamificationGroupReal_nat] at hanti
      exact hanti hσ
    rw [MulAction.mem_stabilizer_iff]
    ext a
    exact hwfix σ hσw a
  -- the order of `y` in `M`
  have hyR : rampSum (fun i => (lowerGroupOrder TM L.Carrier i : ℝ)) N t ≤
      TM.ord (algebraMap L.Carrier M.Carrier y) := by
    have hphi := herbrandPhi_eq_sum TM L.Carrier hcutL ht0.le htN
    have hord := ord_algebraMap_eq TL TM y
    have hh0 : (0 : ℝ) < lowerGroupOrder TM L.Carrier 0 := by
      exact_mod_cast lowerGroupOrder_pos TM L.Carrier 0
    rw [hphi, div_le_iff₀ hh0] at hy
    rw [hord]
    push_cast
    linarith
  -- the trace
  have htrace : Algebra.trace K.Carrier L.Carrier y ∈ TK.additiveLattice (-(n : ℤ)) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hm0 : 0 ≤ herbrandPsi TM K.Carrier m := by
      simpa using (herbrandPsi_strictMono TM K.Carrier).monotone (Nat.cast_nonneg (α := ℝ) m)
    have hmt : herbrandPsi TM K.Carrier m < t :=
      herbrandPsi_strictMono TM K.Carrier (by push_cast; linarith)
    have hgrow := sub_le_rampSum_sub (fun i => (lowerGroupOrder TM L.Carrier i : ℝ))
      (fun i => by exact_mod_cast lowerGroupOrder_one_le TM L.Carrier i) N hm0 hmt.le htN
    have hm := trace_mem_additiveLattice (F := L) TK TM m N hcutK (hmt.le.trans htN) y hy0
      (by linarith)
    simpa using hm
  refine ⟨htrace, ?_⟩
  intro z u hz hu
  -- the remainder `N(1 + y) - 1 - Tr y`
  set R := Algebra.norm K.Carrier (1 + y) - 1 - Algebra.trace K.Carrier L.Carrier y with hRdef
  have hR : R ∈ TK.additiveLattice (-((n : ℤ) + 1)) := by
    set S' : AddSubgroup M.Carrier :=
      (TK.additiveLattice (-((n : ℤ) + 1))).map (algebraMap K.Carrier M.Carrier).toAddMonoidHom
    set 𝒮 := (Finset.univ : Finset (L.Carrier →ₐ[K.Carrier] M.Carrier)).powerset.filter
      (fun S => 2 ≤ S.card) with h𝒮
    have hmap : algebraMap K.Carrier M.Carrier R = ∑ S ∈ 𝒮, ∏ x ∈ S, x y := by
      rw [hRdef, map_sub, map_sub, map_one, algebraMap_norm_eq_prod_embeddings_normal,
        algebraMap_trace_eq_sum_embeddings_normal]
      simp only [map_add, map_one]
      exact prod_one_add_sub_one_sub_sum _ _
    have hmem : algebraMap K.Carrier M.Carrier R ∈ S' := by
      rw [hmap]
      apply sum_mem_of_orbit_sums (M.Carrier ≃ₐ[K.Carrier] M.Carrier)
        (Finset (L.Carrier →ₐ[K.Carrier] M.Carrier)) M.Carrier S'
      · intro g S hS
        rw [h𝒮, Finset.mem_filter] at hS ⊢
        exact ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
          by rw [Finset.card_smul_finset]; exact hS.2⟩
      · intro S hS
        rw [h𝒮, Finset.mem_filter] at hS
        obtain ⟨k, hk, hkeq⟩ :=
          exists_orbit_sum_eq TK TM n N c hcutK htN hc1 hc0 hcN hcH hy0 hyR S hS.2
        rw [hkeq]
        exact ⟨k, hk, rfl⟩
    obtain ⟨k, hk, hkR⟩ := hmem
    rwa [← (algebraMap K.Carrier M.Carrier).injective hkR]
  -- the unit
  have hvtr : TK.discreteValuation (Algebra.trace K.Carrier L.Carrier y) < 1 := by
    have h := (TK.mem_additiveLattice _ _).mp htrace
    refine h.trans_lt ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have hvR : TK.discreteValuation R ≤ WithZero.exp (-((n : ℤ) + 1)) :=
    (TK.mem_additiveLattice _ _).mp hR
  have hvRlt : TK.discreteValuation R < 1 := by
    refine hvR.trans_lt ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have hvu : TK.discreteValuation (u : K.Carrier) = 1 := by
    rw [hu]
    exact Valuation.map_one_add_of_lt _ hvtr
  have hNm : Algebra.norm K.Carrier (1 + y) = (u : K.Carrier) + R := by
    rw [hu, hRdef]
    ring
  have hvN : TK.discreteValuation (Algebra.norm K.Carrier (1 + y)) = 1 := by
    rw [hNm, Valuation.map_add_eq_of_lt_left _ (by rw [hvu]; exact hvRlt), hvu]
  have hu0 : (u : K.Carrier) ≠ 0 := u.ne_zero
  have hval : ((Units.map (Algebra.norm K.Carrier : L.Carrier →* K.Carrier) z * u⁻¹ :
      K.Carrierˣ) : K.Carrier) = Algebra.norm K.Carrier (1 + y) * (u : K.Carrier)⁻¹ := by
    rw [Units.val_mul, Units.coe_map, Units.val_inv_eq_inv_val, hz]
  rw [PadicField.TopologicalData.mem_principalUnits, hval]
  constructor
  · rw [map_mul, map_inv₀, hvN, hvu, inv_one, mul_one]
  · have hsub : Algebra.norm K.Carrier (1 + y) * (u : K.Carrier)⁻¹ - 1 =
        R * (u : K.Carrier)⁻¹ := by
      rw [hNm]
      field_simp
      ring
    rw [hsub, map_mul, map_inv₀, hvu, inv_one, mul_one]
    push_cast
    exact hvR

end Langlands.LocalFactor.NonabelianSystem.DeligneHenniart.TopLayer
