import Langlands.Representation.CuspidalSupport.DualAveraging

/-!
# One compact open subgroup with block Iwahori factorizations for every shape

Every identity neighbourhood of the actual p-adic `GL_n` contains a single
compact open subgroup having the published weak-chamber block Iwahori
factorization for every block shape of `n` simultaneously; for positive rank
it is a positive principal level subgroup. The product-Levi form follows.
-/

open Filter Topology

namespace Langlands.GeneralLinear.BlockShape

universe uF

private def UniformEntryIdeal {k : Type*} [Field k] {n : ℕ}
    (O : Subring k) (I : Ideal O) (g : GeneralLinear n k) : Prop :=
  ∀ i j, ∃ x : O, x ∈ I ∧ (x : k) = g i j - (1 : Matrix (Fin n) (Fin n) k) i j

private theorem uniformEntryIdeal_upper_conj {k : Type*} [Field k] {n : ℕ}
    (B : GeneralLinear.BlockShape n) (O : Subring k) (I : Ideal O)
    (a : Fin B.length → kˣ)
    (ha : ∀ i j : Fin B.length, i < j → ((a i * (a j)⁻¹ : kˣ) : k) ∈ O)
    {g : GeneralLinear n k} (hg : g ∈ B.unipotentSubgroup k)
    (hentry : UniformEntryIdeal O I g) :
    UniformEntryIdeal O I (B.blockScalar k a * g * (B.blockScalar k a)⁻¹) := by
  intro x y
  obtain ⟨⟨i, r⟩, rfl⟩ := B.indexEquiv.surjective x
  obtain ⟨⟨j, s⟩, rfl⟩ := B.indexEquiv.surjective y
  change ∃ v : O, v ∈ I ∧ (v : k) =
    (B.blockScalar k a * g * (B.blockScalar k a)⁻¹) (B.index i r) (B.index j s) -
      (1 : Matrix (Fin n) (Fin n) k) (B.index i r) (B.index j s)
  rw [B.blockScalar_conj_apply k a g i j r s]
  rcases lt_trichotomy i j with hij | hij | hij
  · have hne : B.index i r ≠ B.index j s := by
      intro he
      have := congrArg Sigma.fst (B.indexEquiv.injective he)
      exact hij.ne this
    obtain ⟨v, hv, he⟩ := hentry (B.index i r) (B.index j s)
    refine ⟨⟨((a i * (a j)⁻¹ : kˣ) : k), ha i j hij⟩ * v,
      I.mul_mem_left _ hv, ?_⟩
    change (((a i * (a j)⁻¹ : kˣ) : k) * (v : k)) = _
    simpa only [Matrix.one_apply, ite_eq_right hne, sub_zero] using
      congrArg (fun z : k => (((a i * (a j)⁻¹ : kˣ) : k) * z)) he
  · subst j
    simpa only [mul_inv_cancel, Units.val_one, one_mul] using
      hentry (B.index i r) (B.index i s)
  · have hne : B.index i r ≠ B.index j s := by
      intro he
      have := congrArg Sigma.fst (B.indexEquiv.injective he)
      exact hij.ne this.symm
    have hzero := (B.mem_parabolic_iff k g).mp
      ((B.mem_unipotentSubgroup_iff k g).mp hg).1 i j r s hij
    exact ⟨0, I.zero_mem, by simp [hzero, hne]⟩

private theorem uniformEntryIdeal_lower_inv_conj {k : Type*} [Field k] {n : ℕ}
    (B : GeneralLinear.BlockShape n) (O : Subring k) (I : Ideal O)
    (a : Fin B.length → kˣ)
    (ha : ∀ i j : Fin B.length, i < j → ((a i * (a j)⁻¹ : kˣ) : k) ∈ O)
    {g : GeneralLinear n k} (hg : g ∈ B.oppositeUnipotentSubgroup k)
    (hentry : UniformEntryIdeal O I g) :
    UniformEntryIdeal O I ((B.blockScalar k a)⁻¹ * g * B.blockScalar k a) := by
  intro x y
  obtain ⟨⟨i, r⟩, rfl⟩ := B.indexEquiv.surjective x
  obtain ⟨⟨j, s⟩, rfl⟩ := B.indexEquiv.surjective y
  change ∃ v : O, v ∈ I ∧ (v : k) =
    ((B.blockScalar k a)⁻¹ * g * B.blockScalar k a) (B.index i r) (B.index j s) -
      (1 : Matrix (Fin n) (Fin n) k) (B.index i r) (B.index j s)
  rw [B.blockScalar_inv_conj_apply k a g i j r s]
  rcases lt_trichotomy i j with hij | hij | hij
  · have hne : B.index i r ≠ B.index j s := by
      intro he
      have := congrArg Sigma.fst (B.indexEquiv.injective he)
      exact hij.ne this
    have hzero := (B.mem_oppositeParabolic_iff k g).mp
      ((B.mem_oppositeUnipotentSubgroup_iff k g).mp hg).1 i j r s hij
    exact ⟨0, I.zero_mem, by simp [hzero, hne]⟩
  · subst j
    simpa only [inv_mul_cancel, Units.val_one, one_mul] using
      hentry (B.index i r) (B.index i s)
  · have hne : B.index i r ≠ B.index j s := by
      intro he
      have := congrArg Sigma.fst (B.indexEquiv.injective he)
      exact hij.ne this.symm
    have hratio : (((a i)⁻¹ * a j : kˣ) : k) ∈ O := by
      simpa only [mul_comm] using ha j i hij
    obtain ⟨v, hv, he⟩ := hentry (B.index i r) (B.index j s)
    refine ⟨⟨(((a i)⁻¹ * a j : kˣ) : k), hratio⟩ * v,
      I.mul_mem_left _ hv, ?_⟩
    change ((((a i)⁻¹ * a j : kˣ) : k) * (v : k)) = _
    simpa only [Matrix.one_apply, ite_eq_right hne, sub_zero] using
      congrArg (fun z : k => ((((a i)⁻¹ * a j : kˣ) : k) * z)) he

private theorem uniformPrincipal_upper_conj
    {k : Type uF} [Field k] {n : ℕ} (B : GeneralLinear.BlockShape (n + 1))
    (O : Subring k) (I : Ideal O) (a : Fin B.length → kˣ)
    (ha : ∀ i j : Fin B.length, i < j → ((a i * (a j)⁻¹ : kˣ) : k) ∈ O)
    {g : GeneralLinear (n + 1) k} (hg : g ∈ B.unipotentSubgroup k)
    (hK : g ∈ Conductor.principalCongruenceSubgroup O n I) :
    B.blockScalar k a * g * (B.blockScalar k a)⁻¹ ∈
      Conductor.principalCongruenceSubgroup O n I := by
  obtain ⟨hforward, hinverse⟩ :=
    (Conductor.mem_principalCongruenceSubgroup_iff O n I g).mp hK
  apply (Conductor.mem_principalCongruenceSubgroup_iff O n I _).mpr
  constructor
  · exact uniformEntryIdeal_upper_conj B O I a ha hg hforward
  · simpa only [UniformEntryIdeal, mul_inv_rev, inv_inv, mul_assoc] using
      uniformEntryIdeal_upper_conj B O I a ha
        ((B.unipotentSubgroup k).inv_mem hg) hinverse

private theorem uniformPrincipal_lower_inv_conj
    {k : Type uF} [Field k] {n : ℕ} (B : GeneralLinear.BlockShape (n + 1))
    (O : Subring k) (I : Ideal O) (a : Fin B.length → kˣ)
    (ha : ∀ i j : Fin B.length, i < j → ((a i * (a j)⁻¹ : kˣ) : k) ∈ O)
    {g : GeneralLinear (n + 1) k} (hg : g ∈ B.oppositeUnipotentSubgroup k)
    (hK : g ∈ Conductor.principalCongruenceSubgroup O n I) :
    (B.blockScalar k a)⁻¹ * g * B.blockScalar k a ∈
      Conductor.principalCongruenceSubgroup O n I := by
  obtain ⟨hforward, hinverse⟩ :=
    (Conductor.mem_principalCongruenceSubgroup_iff O n I g).mp hK
  apply (Conductor.mem_principalCongruenceSubgroup_iff O n I _).mpr
  constructor
  · exact uniformEntryIdeal_lower_inv_conj B O I a ha hg hforward
  · simpa only [UniformEntryIdeal, mul_inv_rev, inv_inv, mul_assoc] using
      uniformEntryIdeal_lower_inv_conj B O I a ha
        ((B.oppositeUnipotentSubgroup k).inv_mem hg) hinverse

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

private theorem uniformWeak_ratio_mem_integers {n : ℕ} (B : GeneralLinear.BlockShape n)
    (T : F.TopologicalData) {a : Fin B.length → F.Carrierˣ}
    (ha : B.IsWeaklyContracting T a) (i j : Fin B.length) (hij : i < j) :
    ((a i * (a j)⁻¹ : F.Carrierˣ) : F.Carrier) ∈ T.Integers :=
  (T.normalizedAbs_le_one_iff_mem_integers _).mp (ha i j hij)

/-- Every identity neighbourhood contains one compact open subgroup with the
block Iwahori factorization for every block shape simultaneously. -/
theorem exists_compactOpenSubgroup_forall_hasBlockIwahoriFactorization
    {n : ℕ} (T : F.TopologicalData) :
    letI := T.topology
    ∀ {U : Set (GeneralLinear n F.Carrier)},
      U ∈ 𝓝 (1 : GeneralLinear n F.Carrier) →
      ∃ K : OpenSubgroup (GeneralLinear n F.Carrier),
        IsCompact (K : Set (GeneralLinear n F.Carrier)) ∧
        (K : Set (GeneralLinear n F.Carrier)) ⊆ U ∧
        ∀ B : GeneralLinear.BlockShape n, B.HasBlockIwahoriFactorization T K := by
  cases n with
  | zero =>
    let := T.topology
    intro U hU
    let K : OpenSubgroup (GeneralLinear 0 F.Carrier) := ⊤
    have hone (g : GeneralLinear 0 F.Carrier) : g = 1 := by
      apply Units.ext
      ext i
      exact Fin.elim0 i
    refine ⟨K, ?_, ?_, fun B => ?_⟩
    · have he : (K : Set (GeneralLinear 0 F.Carrier)) = {1} := by
        ext g
        simp [hone g, K]
      rw [he]
      exact isCompact_singleton
    · intro g _
      rw [hone g]
      exact mem_of_mem_nhds hU
    · constructor
      · constructor
        · intro x y _
          exact Subsingleton.elim _ _
        · intro g
          refine ⟨(1, 1, 1), ?_⟩
          apply Subtype.ext
          simp [hone g.val]
      · intro a _
        constructor
        · intro g _
          rw [hone g, hone (B.blockScalar F.Carrier a)]
          simp
        · intro g _
          rw [hone g, hone (B.blockScalar F.Carrier a)]
          simp
  | succ n =>
    let := T.topology
    let := T.valuativeRel
    let := T.localField
    intro U hU
    obtain ⟨a, ha, hKU⟩ :=
      Conductor.exists_pos_principalLevelOpenSubgroup_subset F.Carrier n hU
    refine ⟨Conductor.principalLevelOpenSubgroup F.Carrier n a,
      Conductor.isCompact_principalLevelOpenSubgroup F.Carrier n a, hKU, fun B => ?_⟩
    constructor
    · exact principalLevelSubgroup_iwahoriProduct_bijective F.Carrier n B a ha
    · intro s hs
      have hratio := uniformWeak_ratio_mem_integers B T hs
      constructor
      · intro g hg
        constructor
        · exact uniformPrincipal_upper_conj B T.Integers
            (IsLocalRing.maximalIdeal T.Integers ^ a) s hratio hg.2 hg.1
        · exact B.blockScalar_conj_mem_unipotentSubgroup F.Carrier s hg.2
      · intro g hg
        constructor
        · exact uniformPrincipal_lower_inv_conj B T.Integers
            (IsLocalRing.maximalIdeal T.Integers ^ a) s hratio hg.2 hg.1
        · exact B.blockScalar_inv_conj_mem_oppositeUnipotentSubgroup F.Carrier s hg.2

end Langlands.GeneralLinear.BlockShape

namespace Langlands.CuspidalSupport

open GeneralLinear

universe uF'

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF'} p} (T : F.TopologicalData)
  {n : ℕ} (B : BlockShape n)

/-- Every identity neighbourhood of the product Levi contains a product of compact
open subgroups, each with a block Iwahori factorization for every block shape of
its factor. -/
theorem exists_leviPiOpenSubgroup_subset_forall :
    letI := T.topology
    ∀ {U : Set (B.Levi F.Carrier)}, U ∈ 𝓝 (1 : B.Levi F.Carrier) →
      ∃ K : ∀ j, OpenSubgroup (GeneralLinear (B.size j) F.Carrier),
        (∀ j, IsCompact (K j : Set (GeneralLinear (B.size j) F.Carrier))) ∧
        (∀ j (S : BlockShape (B.size j)), S.HasBlockIwahoriFactorization T (K j)) ∧
        (leviPiOpenSubgroup T B K : Set (B.Levi F.Carrier)) ⊆ U := by
  let := T.topology
  intro U hU
  rw [nhds_pi, Filter.mem_pi'] at hU
  obtain ⟨I, O, hO, hOU⟩ := hU
  choose K hKc hKO hfac using fun j =>
    BlockShape.exists_compactOpenSubgroup_forall_hasBlockIwahoriFactorization T (hO j)
  refine ⟨K, hKc, hfac, ?_⟩
  intro g hg
  apply hOU
  intro j _
  exact hKO j ((mem_leviPiOpenSubgroup T B K g).mp hg j)

end Langlands.CuspidalSupport
