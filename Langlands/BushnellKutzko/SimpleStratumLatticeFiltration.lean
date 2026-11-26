import Langlands.BushnellKutzko.SimpleStratumLatticePropertiesStatement
import Langlands.BushnellKutzko.StratumEquivalenceCritical
import Langlands.BushnellKutzko.RefinementElementExactness
import Langlands.BushnellKutzko.LatticeChainLayerCommutation

/-! # Fractional centralizers and mixed adjoint lattices -/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko.SimpleStratumLattice

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
  (L : LatticeChain 𝒪[F] F V)

local notation "A" => Module.End F V
local notation "P" => L.endFiltration
local notation "Q" => centralizerLattice L
local notation "M" => mixedAdjointLattice L
local notation "N" => adjointLattice L
local notation "a" => adjointMap F
local notation "crit" => criticalExponent L

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Multiplication of submodules bounded by two filtration steps adds the depths. -/
theorem filtration_products (U W : Submodule 𝒪[F] A) {j k : ℤ}
    (hU : U ≤ P j) (hW : W ≤ P k) : U * W ≤ P (j + k) :=
  Submodule.mul_le.mpr fun _ hx _ hy => L.mul_mem_endFiltration (hU hx) (hW hy)

/-- The field normalization and filtration facts about a pure parameter used in the
lattice induction. The level is recorded by membership in `𝔓^{-n}`. -/
structure Parameter (n : ℤ) (b : A) : Prop where
  mem : b ∈ P (-n)
  inverse : ∀ m : ℤ, 1 ∈ Q b m * Q b (-m)
  criticalSet : elementAlgebra b = ⊥ ∨
    ((criticalIndexSet L b).Nonempty ∧ BddAbove (criticalIndexSet L b))

include L in
/-- Purity supplies the fractional inverse identity and the critical-index bounds. -/
theorem parameter_of_pure {S : Stratum 𝒪[F] F V} (hS : S.IsPure)
    (hL : S.chain.order = L.order) : Parameter L S.n S.b := by
  have hP := StratumEquivalence.endFiltration_eq_of_eq
    (show S.chain.endFiltration 0 = P 0 from congrArg Subalgebra.toSubmodule hL)
  let := S.chain.finiteDimensional
  have hmem := StratumEquivalence.mem_of_valuation_eq hS.2
  have hinv : ∀ m : ℤ, (1 : A) ∈ centralizerLattice S.chain S.b m *
      centralizerLattice S.chain S.b (-m) := by
    obtain ⟨hf, hu⟩ := hS.1
    let := hf.toField
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
    have h := one_mem_centralizerLattice_mul_neg S.chain hπ (elementGenerator S.b) hu
    rwa [subfieldEmbedding_elementGenerator S.b hf] at h
  have hset : elementAlgebra S.b = ⊥ ∨
      ((criticalIndexSet S.chain S.b).Nonempty ∧ BddAbove (criticalIndexSet S.chain S.b)) := by
    by_cases hb : elementAlgebra S.b = ⊥
    · exact Or.inl hb
    · exact Or.inr (StratumEquivalence.criticalIndexSet_nonempty_bddAbove hS hb)
  simp only [StratumEquivalence.centralizerLattice_congr hP] at hinv
  rw [StratumEquivalence.criticalIndexSet_congr hP] at hset
  exact ⟨hP ▸ hmem.1, hinv, hset⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The adjoint filtrations agree at sufficiently low depths under a stratum perturbation. -/
theorem mixed_eq_of_sub_mem {b c : A} {t j : ℤ} (h : c - b ∈ P (-t)) (hj : j ≤ -t)
    (m : ℤ) : M b m j = M c m j := by
  ext x
  simp only [mem_mixedAdjointLattice_iff]
  refine and_congr_right fun hx => ?_
  have hd : a c x - a b x ∈ P (m + j) := by
    have h₁ := L.mul_mem_endFiltration h hx
    have h₂ := L.mul_mem_endFiltration hx h
    rw [add_comm (-t) m] at h₁
    apply L.endFiltration_antitone (show m + j ≤ m + -t by omega)
    have heq : a c x - a b x = (c - b) * x - x * (c - b) := by
      simp only [StratumEquivalence.adjointMap_apply]
      noncomm_ring
    rw [heq]
    exact sub_mem h₁ h₂
  exact ⟨fun hb => by simpa only [sub_add_cancel] using add_mem hd hb,
    fun hc => by simpa only [sub_sub_cancel] using sub_mem hc hd⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Increasing the first index of a mixed adjoint lattice decreases the lattice. -/
theorem mixed_antitone_left (b : A) (j : ℤ) : Antitone (fun m => M b m j) := by
  intro m n h x hx
  exact (mem_mixedAdjointLattice_iff L b).mpr
    ⟨L.endFiltration_antitone h hx.1, L.endFiltration_antitone (by omega) hx.2⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- At the valuation bound of the parameter the mixed adjoint condition is automatic. -/
theorem mixed_eq_filtration {b : A} {j : ℤ} (hb : b ∈ P j) (m : ℤ) : M b m j = P m := by
  refine inf_le_left.antisymm fun x hx => ⟨hx, ?_⟩
  change a b x ∈ P (m + j)
  rw [StratumEquivalence.adjointMap_apply]
  exact sub_mem (by simpa only [add_comm] using L.mul_mem_endFiltration hb hx)
    (L.mul_mem_endFiltration hx hb)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- If the critical exponent is infinite below, the parameter acts by scalars. -/
theorem scalar_of_criticalExponent_bot {b : A} (h : crit b = ⊥) : elementAlgebra b = ⊥ := by
  by_contra hb
  simp [criticalExponent, hb] at h

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Every centralizer step for a scalar parameter is the corresponding full step. -/
theorem centralizer_eq_filtration {b : A} (hb : crit b = ⊥) (m : ℤ) : Q b m = P m := by
  have hmem : b ∈ (⊥ : Subalgebra F A) :=
    scalar_of_criticalExponent_bot L hb ▸ Algebra.self_mem_adjoin_singleton F b
  obtain ⟨c, rfl⟩ := Algebra.mem_bot.mp hmem
  refine inf_le_left.antisymm fun x hx => ⟨hx, ?_⟩
  change a (algebraMap F A c) x = 0
  rw [StratumEquivalence.adjointMap_apply, Algebra.commutes, sub_self]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The centralizer filtration is multiplicative. -/
theorem centralizer_mul_le (b : A) (m n : ℤ) : Q b m * Q b n ≤ Q b (m + n) := by
  apply Submodule.mul_le.mpr
  intro x hx y hy
  exact ⟨L.mul_mem_endFiltration hx.1 hy.1, by
    change a b (x * y) = 0
    have hx' : a b x = 0 := hx.2
    have hy' : a b y = 0 := hy.2
    rw [adjointMap_mul_left_of_ker b hx', hy', mul_zero]⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The identity belongs to the integral centralizer and to every adjoint lattice. -/
theorem one_mem_centralizer (b : A) : 1 ∈ Q b 0 := by
  refine ⟨L.order.one_mem, ?_⟩
  change a b 1 = 0
  rw [StratumEquivalence.adjointMap_apply, mul_one, one_mul, sub_self]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The fractional inverse identity upgrades the centralizer product inclusion to equality. -/
theorem centralizer_mul (b : A) (hinv : ∀ m : ℤ, 1 ∈ Q b m * Q b (-m)) (m n : ℤ) :
    Q b m * Q b n = Q b (m + n) := by
  refine (centralizer_mul_le L b m n).antisymm fun x hx => ?_
  have h : Q b (-m) * Q b (m + n) ≤ Q b n := by
    simpa only [← add_assoc, neg_add_cancel, zero_add] using centralizer_mul_le L b (-m) (m + n)
  have hx' := Submodule.mul_mem_mul (hinv m) hx
  rw [one_mul, mul_assoc] at hx'
  exact mul_le_mul_right h _ hx'

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Right multiplication by a fractional centralizer step shifts the mixed lattice by its depth. -/
theorem mixed_mul_centralizer (b : A) (hinv : ∀ m : ℤ, 1 ∈ Q b m * Q b (-m)) (m n j : ℤ) :
    M b n j * Q b m = M b (n + m) j := by
  have hmul (s t : ℤ) : M b s j * Q b t ≤ M b (s + t) j := by
    apply Submodule.mul_le.mpr
    intro x hx y hy
    refine ⟨L.mul_mem_endFiltration hx.1 hy.1, ?_⟩
    change a b (x * y) ∈ P (s + t + j)
    have hby : b * y = y * b := by
      have hy' : a b y = 0 := hy.2
      rwa [StratumEquivalence.adjointMap_apply, sub_eq_zero] at hy'
    have haxy : a b (x * y) = a b x * y := by
      simp only [StratumEquivalence.adjointMap_apply, sub_mul, mul_assoc, hby]
    rw [haxy, add_right_comm s t j]
    exact L.mul_mem_endFiltration hx.2 hy.1
  refine (hmul n m).antisymm fun x hx => ?_
  have h : M b (n + m) j * Q b (-m) ≤ M b n j := by
    simpa only [add_assoc, add_neg_cancel, add_zero] using hmul (n + m) (-m)
  have hone : (1 : A) ∈ Q b (-m) * Q b m := by simpa only [neg_neg] using hinv (-m)
  have hx' := Submodule.mul_mem_mul hx hone
  rw [mul_one, ← mul_assoc] at hx'
  exact mul_le_mul_left h _ hx'

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The mixed form of BK93 (1.4.9), obtained by stripping off one centralizer step
at a time above the critical exponent. -/
theorem mixed_eq_sup {n : ℤ} {b : A} (hb : Parameter L n b) {j : ℤ}
    (hcrit : crit b = (j : WithBot ℤ)) (m d : ℤ) (hd : 0 ≤ d) :
    M b m (j + d) = Q b m ⊔ M b (m + d) j := by
  have advance (k : ℤ) (hk : j ≤ k) : N b (k + 1) = Q b 0 ⊔ M b 1 k := by
    have hlt : crit b < ((k + 1 : ℤ) : WithBot ℤ) := by rw [hcrit, WithBot.coe_lt_coe]; omega
    have hle := StratumEquivalence.adjointLattice_le_of_criticalExponent_lt L
      (hb.criticalSet.imp_right And.right) (r := -(k + 1)) (by simpa only [neg_neg] using hlt)
      (k := k + 1) (by omega)
    refine le_antisymm (fun x hx => ?_) (sup_le (StratumEquivalence.centralizerLattice_le_adjointLattice L b _) ?_)
    · obtain ⟨q, hq, y, hy, rfl⟩ := Submodule.mem_sup.mp (hle hx)
      refine Submodule.mem_sup.mpr ⟨q, hq, y, ⟨hy, ?_⟩, rfl⟩
      have hq' : a b q = 0 := hq.2
      have hxy : a b (q + y) ∈ P (k + 1) := hx.2
      change a b y ∈ P (1 + k)
      simpa only [map_add, hq', zero_add, add_comm 1 k] using hxy
    · intro x hx
      exact ⟨L.endFiltration_antitone (by omega) hx.1, by
        simpa only [add_comm 1 k] using hx.2⟩
  have advanceMixed (p k : ℤ) (hk : j ≤ k) : M b p (k + 1) = Q b p ⊔ M b (p + 1) k := by
    rw [← add_zero p, ← centralizerLattice_mul_mixedAdjointLattice L b hb.inverse,
      mixedAdjointLattice_zero, advance k hk, Submodule.mul_sup, centralizer_mul L b hb.inverse,
      centralizerLattice_mul_mixedAdjointLattice L b hb.inverse, add_zero]
  have iter (d : ℕ) (p : ℤ) : M b p (j + d) = Q b p ⊔ M b (p + d) j := by
    induction d generalizing p with
    | zero =>
      simpa only [Nat.cast_zero, add_zero] using
        (sup_eq_right.mpr (centralizerLattice_le_mixedAdjointLattice L b p j)).symm
    | succ d ih =>
      rw [Nat.cast_succ, ← add_assoc, advanceMixed p _ (by omega), ih, ← sup_assoc,
        sup_eq_left.mpr (show Q b (p + 1) ≤ Q b p from
          inf_le_inf_right _ (L.endFiltration_antitone (by omega)))]
      congr 2
      omega
  simpa only [Int.toNat_of_nonneg hd] using iter d.toNat m

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Left and right stability under multiplication by another submodule. -/
def Bimodule (R X : Submodule 𝒪[F] A) : Prop := R * X ≤ X ∧ X * R ≤ X

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- An adjoint action on a lattice identifies the products by the two fractional centralizers
at a critical approximation (BK93 (3.1.3)). -/
theorem transfer_products {n : ℤ} {b c : A} (hb : Parameter L n b) (hc : Parameter L n c)
    {r : ℤ} (hsub : c - b ∈ P (-r)) {X : Submodule 𝒪[F] A}
    (hX : Bimodule (N c (-r)) X) (m : ℤ) :
    Q b m * X = Q c m * X ∧ X * Q b m = X * Q c m := by
  have hone : (1 : A) ∈ N c (-r) :=
    StratumEquivalence.centralizerLattice_le_adjointLattice L c _ (one_mem_centralizer L c)
  have hl : N c (-r) * X = X := hX.1.antisymm fun x hx =>
    one_mul x ▸ Submodule.mul_mem_mul hone hx
  have hr : X * N c (-r) = X := hX.2.antisymm fun x hx =>
    mul_one x ▸ Submodule.mul_mem_mul hx hone
  have hm := mixed_eq_of_sub_mem L hsub (le_refl (-r)) m
  have hm0 := mixed_eq_of_sub_mem L hsub (le_refl (-r)) 0
  simp only [mixedAdjointLattice_zero] at hm0
  constructor
  · calc
      Q b m * X = Q b m * (N c (-r) * X) := by rw [hl]
      _ = M b m (-r) * X := by
        rw [← mul_assoc, ← hm0, ← mixedAdjointLattice_zero L b,
          centralizerLattice_mul_mixedAdjointLattice L b hb.inverse, add_zero]
      _ = M c m (-r) * X := by rw [hm]
      _ = Q c m * X := by
        rw [← add_zero m, ← centralizerLattice_mul_mixedAdjointLattice L c hc.inverse,
          mixedAdjointLattice_zero, mul_assoc, hl, add_zero]
  · calc
      X * Q b m = (X * N c (-r)) * Q b m := by rw [hr]
      _ = X * M b m (-r) := by
        rw [mul_assoc, ← hm0, ← mixedAdjointLattice_zero L b,
          mixed_mul_centralizer L b hb.inverse, zero_add]
      _ = X * M c m (-r) := by rw [hm]
      _ = X * Q c m := by
        rw [← zero_add m, ← mixed_mul_centralizer L c hc.inverse,
          mixedAdjointLattice_zero, ← mul_assoc, hr, zero_add]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Fractional commutation implies invariance under the relative normalizer. -/
theorem conjugate_mem_iff {b : A} {X : Submodule 𝒪[F] A}
    (h : ∀ m : ℤ, Q b m * X = X * Q b m) (hX : X * Q b 0 ≤ X)
    {g : Aˣ} (hg : g ∈ relativeOrderNormalizer L b) (x : A) :
    ((g : A) * x * (↑g⁻¹ : A) ∈ X ↔ x ∈ X) := by
  have conjugate {v : Aˣ} (hv : v ∈ relativeOrderNormalizer L b) {y : A} (hy : y ∈ X) :
      (v : A) * y * (↑v⁻¹ : A) ∈ X := by
    let u : L.stabilizer := ⟨v, hv.2⟩
    let d := L.stabilizerValuation u
    have mem (w : L.stabilizer) : (w.val : A) ∈ P (L.stabilizerValuation w) :=
      L.mem_endFiltration.mpr fun i z hz => by
        rw [← L.map_lattice_stabilizer w i]
        exact Submodule.mem_map_of_mem hz
    have hq : (v : A) ∈ Q b d := ⟨mem u, by
      change a b (v : A) = 0
      rw [StratumEquivalence.adjointMap_apply, sub_eq_zero]
      exact hv.1⟩
    have hv' := (relativeOrderNormalizer L b).inv_mem hv
    have hq' : (↑v⁻¹ : A) ∈ Q b (-d) := by
      refine ⟨?_, ?_⟩
      · change (↑v⁻¹ : A) ∈ P (-d)
        simpa only [L.stabilizerValuation_inv, Subgroup.coe_inv, d, u] using mem u⁻¹
      · change a b (↑v⁻¹ : A) = 0
        rw [StratumEquivalence.adjointMap_apply, sub_eq_zero]
        exact hv'.1
    have hz := Submodule.mul_mem_mul (Submodule.mul_mem_mul hq hy) hq'
    rw [h d, mul_assoc] at hz
    exact hX (mul_le_mul_right (by simpa only [add_neg_cancel] using centralizer_mul_le L b d (-d)) X hz)
  refine ⟨fun hx => ?_, conjugate hg⟩
  have hx' := conjugate ((relativeOrderNormalizer L b).inv_mem hg) hx
  have heq : (↑g⁻¹ : A) * ((g : A) * x * (↑g⁻¹ : A)) * (g : A) = x := by
    rw [← mul_assoc (↑g⁻¹ : A), ← mul_assoc (↑g⁻¹ : A), Units.inv_mul, one_mul,
      mul_assoc, Units.inv_mul, mul_one]
  simpa only [inv_inv, heq] using hx'

end Langlands.BushnellKutzko.SimpleStratumLattice
