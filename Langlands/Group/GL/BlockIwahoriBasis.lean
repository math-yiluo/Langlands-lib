import Langlands.Group.GL.BlockIwahoriBasisStatement
import Langlands.Group.GL.PrincipalBlockFactorizationProof
import Langlands.Representation.Conductor.PrincipalCongruenceBasisProof

open Filter Topology

namespace Langlands.GeneralLinear.BlockShape

universe uF

private def EntryIdeal {k : Type*} [Field k] {n : ℕ}
    (O : Subring k) (I : Ideal O) (g : GeneralLinear n k) : Prop :=
  ∀ i j, ∃ x : O, x ∈ I ∧ (x : k) = g i j - (1 : Matrix (Fin n) (Fin n) k) i j

private theorem entryIdeal_upper_conj {k : Type*} [Field k] {n : ℕ}
    (B : GeneralLinear.BlockShape n) (O : Subring k) (I : Ideal O)
    (a : Fin B.length → kˣ)
    (ha : ∀ i j : Fin B.length, i < j → ((a i * (a j)⁻¹ : kˣ) : k) ∈ O)
    {g : GeneralLinear n k} (hg : g ∈ B.unipotentSubgroup k)
    (hentry : EntryIdeal O I g) :
    EntryIdeal O I (B.blockScalar k a * g * (B.blockScalar k a)⁻¹) := by
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

private theorem entryIdeal_lower_inv_conj {k : Type*} [Field k] {n : ℕ}
    (B : GeneralLinear.BlockShape n) (O : Subring k) (I : Ideal O)
    (a : Fin B.length → kˣ)
    (ha : ∀ i j : Fin B.length, i < j → ((a i * (a j)⁻¹ : kˣ) : k) ∈ O)
    {g : GeneralLinear n k} (hg : g ∈ B.oppositeUnipotentSubgroup k)
    (hentry : EntryIdeal O I g) :
    EntryIdeal O I ((B.blockScalar k a)⁻¹ * g * B.blockScalar k a) := by
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

private theorem principal_upper_conj
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
  · exact entryIdeal_upper_conj B O I a ha hg hforward
  · simpa only [EntryIdeal, mul_inv_rev, inv_inv, mul_assoc] using
      entryIdeal_upper_conj B O I a ha
        ((B.unipotentSubgroup k).inv_mem hg) hinverse

private theorem principal_lower_inv_conj
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
  · exact entryIdeal_lower_inv_conj B O I a ha hg hforward
  · simpa only [EntryIdeal, mul_inv_rev, inv_inv, mul_assoc] using
      entryIdeal_lower_inv_conj B O I a ha
        ((B.oppositeUnipotentSubgroup k).inv_mem hg) hinverse

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

private theorem weak_ratio_mem_integers {n : ℕ} (B : GeneralLinear.BlockShape n)
    (T : F.TopologicalData) {a : Fin B.length → F.Carrierˣ}
    (ha : B.IsWeaklyContracting T a) (i j : Fin B.length) (hij : i < j) :
    ((a i * (a j)⁻¹ : F.Carrierˣ) : F.Carrier) ∈ T.Integers :=
  (T.normalizedAbs_le_one_iff_mem_integers _).mp (ha i j hij)

private theorem blockIwahoriBasis_zero (B : GeneralLinear.BlockShape 0)
    (T : F.TopologicalData) : B.BlockIwahoriBasisStatement T := by
  let := T.topology
  intro U hU
  let K : OpenSubgroup (GeneralLinear 0 F.Carrier) := ⊤
  have hone (g : GeneralLinear 0 F.Carrier) : g = 1 := by
    apply Units.ext
    ext i
    exact Fin.elim0 i
  refine ⟨K, ?_, ?_, ?_⟩
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

/-- Every identity neighborhood contains a compact open subgroup with block
Iwahori factorization and both weak-chamber conjugation containments. -/
theorem blockIwahoriBasis
    {n : ℕ} (B : GeneralLinear.BlockShape n) (T : F.TopologicalData) :
    B.BlockIwahoriBasisStatement T := by
  cases n with
  | zero => exact blockIwahoriBasis_zero B T
  | succ n =>
    let := T.topology
    let := T.valuativeRel
    let := T.localField
    intro U hU
    obtain ⟨a, ha, hKU⟩ :=
      Conductor.exists_pos_principalLevelOpenSubgroup_subset F.Carrier n hU
    refine ⟨Conductor.principalLevelOpenSubgroup F.Carrier n a,
      Conductor.isCompact_principalLevelOpenSubgroup F.Carrier n a, hKU, ?_⟩
    constructor
    · exact principalLevelSubgroup_iwahoriProduct_bijective F.Carrier n B a ha
    · intro s hs
      have hratio := weak_ratio_mem_integers B T hs
      constructor
      · intro g hg
        constructor
        · exact principal_upper_conj B T.Integers
            (IsLocalRing.maximalIdeal T.Integers ^ a) s hratio hg.2 hg.1
        · exact B.blockScalar_conj_mem_unipotentSubgroup F.Carrier s hg.2
      · intro g hg
        constructor
        · exact principal_lower_inv_conj B T.Integers
            (IsLocalRing.maximalIdeal T.Integers ^ a) s hratio hg.2 hg.1
        · exact B.blockScalar_inv_conj_mem_oppositeUnipotentSubgroup F.Carrier s hg.2

/-- A usable neighborhood form of the block Iwahori basis theorem, for the
topology supplied by `T` and every natural rank. -/
theorem exists_compactOpenSubgroup_hasBlockIwahoriFactorization
    {n : ℕ} (B : GeneralLinear.BlockShape n) (T : F.TopologicalData) :
    letI := T.topology
    ∀ {U : Set (GeneralLinear n F.Carrier)},
      U ∈ 𝓝 (1 : GeneralLinear n F.Carrier) →
      ∃ K : OpenSubgroup (GeneralLinear n F.Carrier),
        IsCompact (K : Set (GeneralLinear n F.Carrier)) ∧
        (K : Set (GeneralLinear n F.Carrier)) ⊆ U ∧
        B.HasBlockIwahoriFactorization T K := by
  let := T.topology
  intro U hU
  exact blockIwahoriBasis B T U hU

end Langlands.GeneralLinear.BlockShape
