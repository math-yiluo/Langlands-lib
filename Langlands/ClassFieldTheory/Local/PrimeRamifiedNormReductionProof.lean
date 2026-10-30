import Langlands.ClassFieldTheory.Local.PrimeRamifiedNormReductionStatement
import Langlands.ClassFieldTheory.Local.PrimeRamifiedGradedNormProof
import Langlands.ClassFieldTheory.Local.PrimeRamificationArithmeticSupport
import Langlands.ClassFieldTheory.Local.NormOrderProof
import Langlands.ClassFieldTheory.Local.UnramifiedNormMembershipProof
import Mathlib.FieldTheory.Perfect

/-! Higher-unit norms and critical representatives for a prime ramified extension. -/

namespace Langlands.LocalClassField

namespace PrimeRamifiedNormReductionProof

universe u v

section Generic

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} {E : PadicField.{v} p}
  (T : F.TopologicalData) (S : E.TopologicalData)

/-- Completeness step: approximations to every depth give an exact preimage.
The sets of approximations are nested closed subsets of a compact filtration
group, and the filtration is separated. -/
theorem exists_eq_of_approximations (f : E.Carrierˣ →* F.Carrierˣ)
    (hf : let := T.topology; let := S.topology; Continuous f)
    (a n : ℕ) (y : F.Carrierˣ)
    (happrox : ∀ k : ℕ, ∃ x ∈ S.unitFiltration a,
      y * (f x)⁻¹ ∈ T.unitFiltration (n + k)) :
    ∃ x ∈ S.unitFiltration a, f x = y := by
  let := T.topology
  let := S.topology
  let := T.valuativeRel
  let := T.localField
  have hSclosed : IsClosed (S.unitFiltration a : Set E.Carrierˣ) :=
    S.isClosed_unitFiltration a
  have hScompact : IsCompact (S.unitFiltration a : Set E.Carrierˣ) :=
    S.isCompact_unitFiltration a
  let C : ℕ → Set E.Carrierˣ := fun k =>
    {x | x ∈ S.unitFiltration a ∧ y * (f x)⁻¹ ∈ T.unitFiltration (n + k)}
  have hCclosed (k : ℕ) : IsClosed (C k) := by
    have hT : IsClosed (T.unitFiltration (n + k) : Set F.Carrierˣ) :=
      T.isClosed_unitFiltration (n + k)
    exact hSclosed.inter (hT.preimage (continuous_const.mul hf.inv))
  have hCcompact : IsCompact (C 0) :=
    hScompact.of_isClosed_subset (hCclosed 0) (fun _ hx => hx.1)
  have hCstep (k : ℕ) : C (k + 1) ⊆ C k := by
    intro x hx
    exact ⟨hx.1, T.unitFiltration_antitone (Nat.le_succ (n + k)) hx.2⟩
  obtain ⟨x, hx⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C hCstep
      happrox hCcompact hCclosed
  have hxC (k : ℕ) : x ∈ C k := Set.mem_iInter.mp hx k
  have herr : y * (f x)⁻¹ = 1 := T.unitFiltration_separated _ (fun k =>
    T.unitFiltration_antitone (Nat.le_add_left k n) (hxC k).2)
  exact ⟨x, (hxC 0).1, (mul_inv_eq_one.mp herr).symm⟩

/-- Successive approximation: one-level corrections at every depth from `n`
combine into approximations to every depth inside one fixed group. -/
theorem approximations_of_steps (f : E.Carrierˣ →* F.Carrierˣ) (lev : ℕ → ℕ)
    (a n : ℕ) (hlev : ∀ k : ℕ, S.unitFiltration (lev (n + k)) ≤ S.unitFiltration a)
    (hstep : ∀ k : ℕ, ∀ w ∈ T.unitFiltration (n + k),
      ∃ z ∈ S.unitFiltration (lev (n + k)), w * (f z)⁻¹ ∈ T.unitFiltration (n + k + 1))
    (y : F.Carrierˣ) (hy : y ∈ T.unitFiltration n) (k : ℕ) :
    ∃ x ∈ S.unitFiltration a, y * (f x)⁻¹ ∈ T.unitFiltration (n + k) := by
  induction k with
  | zero => exact ⟨1, (S.unitFiltration a).one_mem, by simpa using hy⟩
  | succ k ih =>
    obtain ⟨x, hx, herr⟩ := ih
    obtain ⟨z, hz, hnew⟩ := hstep k _ herr
    refine ⟨x * z, (S.unitFiltration a).mul_mem hx (hlev k hz), ?_⟩
    rw [map_mul, mul_inv, ← mul_assoc]
    exact hnew

/-- A filtration-preserving continuous map with one-level corrections above `t`
maps the reindexed filtration onto the filtration of the target. -/
theorem map_eq_of_steps (f : E.Carrierˣ →* F.Carrierˣ)
    (hf : let := T.topology; let := S.topology; Continuous f)
    (ψ : ℕ → ℕ) (hψ : Monotone ψ) (t : ℕ)
    (hcont : ∀ n : ℕ, ∀ x ∈ S.unitFiltration (ψ n), f x ∈ T.unitFiltration n)
    (hstep : ∀ m : ℕ, t < m → ∀ w ∈ T.unitFiltration m,
      ∃ z ∈ S.unitFiltration (ψ m), w * (f z)⁻¹ ∈ T.unitFiltration (m + 1))
    (n : ℕ) (hn : t < n) :
    (S.unitFiltration (ψ n)).map f = T.unitFiltration n := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact hcont n x hx
  · intro y hy
    have happrox := approximations_of_steps T S f ψ (ψ n) n
      (fun k => S.unitFiltration_antitone (hψ (Nat.le_add_right n k)))
      (fun k w hw => hstep (n + k) (by omega) w hw) y hy
    obtain ⟨x, hx, hxy⟩ := exists_eq_of_approximations T S f hf (ψ n) n y happrox
    exact ⟨x, hx, hxy⟩

/-- One positive-level correction from a residue formula whose right side
attains every value of the residue map. -/
theorem exists_step_positive (f : E.Carrierˣ →* F.Carrierˣ)
    (r : T.ResidueField →+* S.ResidueField)
    (πF : F.Carrier) (hF : T.ord πF = 1) (πL : E.Carrier) (hL : S.ord πL = 1)
    (m a : ℕ) (hm : 0 < m) (ha : 0 < a) (φ : S.ResidueField → S.ResidueField)
    (hφ : ∀ c : T.ResidueField, ∃ d : S.ResidueField, φ d = r c)
    (hcont : ∀ x ∈ S.unitFiltration a, f x ∈ T.unitFiltration m)
    (hform : ∀ (x : S.unitFiltration a) (y : T.unitFiltration m),
      (y : F.Carrierˣ) = f x →
        r (T.residue (T.unitCoefficient πF hF m y)) =
          φ (S.residue (S.unitCoefficient πL hL a x)))
    (w : F.Carrierˣ) (hw : w ∈ T.unitFiltration m) :
    ∃ z ∈ S.unitFiltration a, w * (f z)⁻¹ ∈ T.unitFiltration (m + 1) := by
  let w' : T.unitFiltration m := ⟨w, hw⟩
  obtain ⟨d, hd⟩ := hφ (T.residue (T.unitCoefficient πF hF m w'))
  obtain ⟨z, hz⟩ := S.positiveUnitCoordinate_surjective πL hL a ha (Multiplicative.ofAdd d)
  have hzd : S.residue (S.unitCoefficient πL hL a z) = d := by
    rw [S.positiveUnitCoordinate_apply] at hz
    exact Multiplicative.ofAdd.injective hz
  let v : T.unitFiltration m := ⟨f z, hcont z z.2⟩
  have hv : T.residue (T.unitCoefficient πF hF m v) =
      T.residue (T.unitCoefficient πF hF m w') := by
    apply r.injective
    rw [hform z v rfl, hzd, hd]
  refine ⟨z, z.2, ?_⟩
  have hker : w' * v⁻¹ ∈ (T.positiveUnitCoordinate πF hF m hm).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, T.positiveUnitCoordinate_apply,
      T.positiveUnitCoordinate_apply, hv, mul_inv_cancel]
  rw [T.positiveUnitCoordinate_ker] at hker
  exact Subgroup.mem_subgroupOf.mp hker

/-- The level-zero correction from the residue-unit power formula. -/
theorem exists_step_zero (f : E.Carrierˣ →* F.Carrierˣ)
    (r : T.ResidueField →+* S.ResidueField) (ell : ℕ)
    (hsurj : ∀ c : S.ResidueFieldˣ, ∃ d : S.ResidueFieldˣ, d ^ ell = c)
    (hcont : ∀ x ∈ S.unitFiltration 0, f x ∈ T.unitFiltration 0)
    (hform : ∀ (x : S.unitFiltration 0) (y : T.unitFiltration 0),
      (y : F.Carrierˣ) = f x →
        Units.map r.toMonoidHom (T.zeroUnitCoordinate y) = S.zeroUnitCoordinate x ^ ell)
    (w : F.Carrierˣ) (hw : w ∈ T.unitFiltration 0) :
    ∃ z ∈ S.unitFiltration 0, w * (f z)⁻¹ ∈ T.unitFiltration 1 := by
  let w' : T.unitFiltration 0 := ⟨w, hw⟩
  obtain ⟨d, hd⟩ := hsurj (Units.map r.toMonoidHom (T.zeroUnitCoordinate w'))
  obtain ⟨z, hz⟩ := S.zeroUnitCoordinate_surjective d
  let v : T.unitFiltration 0 := ⟨f z, hcont z z.2⟩
  have hv : T.zeroUnitCoordinate v = T.zeroUnitCoordinate w' := by
    apply Units.map_injective (f := r.toMonoidHom) r.injective
    rw [hform z v rfl, hz, hd]
  refine ⟨z, z.2, ?_⟩
  have hker : w' * v⁻¹ ∈ T.zeroUnitCoordinate.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hv, mul_inv_cancel]
  rw [T.zeroUnitCoordinate_ker] at hker
  exact Subgroup.mem_subgroupOf.mp hker

/-- Finitely many one-level corrections from level zero reach level `t`. -/
theorem exists_mem_of_finite_steps (f : E.Carrierˣ →* F.Carrierˣ) (t : ℕ)
    (hstep : ∀ m : ℕ, m < t → ∀ w ∈ T.unitFiltration m,
      ∃ z : E.Carrierˣ, w * (f z)⁻¹ ∈ T.unitFiltration (m + 1))
    (y : F.Carrierˣ) (hy : y ∈ T.unitFiltration 0) :
    ∃ x : E.Carrierˣ, y * (f x)⁻¹ ∈ T.unitFiltration t := by
  have h : ∀ m : ℕ, m ≤ t → ∃ x : E.Carrierˣ, y * (f x)⁻¹ ∈ T.unitFiltration m := by
    intro m
    induction m with
    | zero => exact fun _ => ⟨1, by simpa using hy⟩
    | succ m ih =>
      intro hm
      obtain ⟨x, hx⟩ := ih (by omega)
      obtain ⟨z, hz⟩ := hstep m (by omega) _ hx
      refine ⟨x * z, ?_⟩
      rw [map_mul, mul_inv, ← mul_assoc]
      exact hz
  exact h t le_rfl

/-- The `p`th-power map of the actual finite residue field is surjective. -/
theorem exists_pow_char_eq (c : S.ResidueField) : ∃ d : S.ResidueField, d ^ p = c := by
  let := S.residueCharP
  have := S.finite_residueField
  obtain ⟨d, hd⟩ := surjective_frobenius S.ResidueField p c
  exact ⟨d, by simpa [frobenius_def] using hd⟩

/-- The `p`th-power map on the actual residue units is surjective. -/
theorem exists_units_pow_char_eq (c : S.ResidueFieldˣ) :
    ∃ d : S.ResidueFieldˣ, d ^ p = c := by
  obtain ⟨d, hd⟩ := exists_pow_char_eq S (c : S.ResidueField)
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [zero_pow (Fact.out : p.Prime).ne_zero] at hd
    exact c.ne_zero hd.symm
  exact ⟨Units.mk0 d hd0, Units.ext (by simpa using hd)⟩


end Generic

/-- The natural inverse-Herbrand index function of a single break is monotone. -/
theorem psi_monotone (t ell : ℕ) :
    Monotone (fun n : ℕ => if n ≤ t then n else t + ell * (n - t)) := by
  intro m n h
  dsimp only
  split_ifs with hm hn hn
  · exact h
  · omega
  · omega
  · exact Nat.add_le_add_left (Nat.mul_le_mul_left ell (Nat.sub_le_sub_right h t)) t

/-- From the break on, one more level in the base needs at least one more
level in the extension. -/
theorem psi_succ_le (t ell n : ℕ) (hell : 1 ≤ ell) (hn : t ≤ n) :
    (if n ≤ t then n else t + ell * (n - t)) + 1 ≤
      (if n + 1 ≤ t then n + 1 else t + ell * (n + 1 - t)) := by
  have h1 : n + 1 - t = n - t + 1 := by omega
  rw [h1, mul_add, mul_one]
  split_ifs with h2 h3 h3 <;> omega

/-- Above the break the extension index is positive. -/
theorem psi_pos (t ell n : ℕ) (hell : 1 ≤ ell) (hn : t < n) :
    0 < (if n ≤ t then n else t + ell * (n - t)) := by
  rw [ite_eq_right (by omega)]
  exact Nat.add_pos_right _ (Nat.mul_pos hell (by omega))

section Main

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (L : PadicField.{v} p)
  [Algebra F.Carrier L.Carrier] [IsScalarTower (Padic p) F.Carrier L.Carrier]
  [FiniteDimensional F.Carrier L.Carrier]

/-- Total ramification leaves the absolute residue degree unchanged. -/
theorem residueDegree_eq_of_totalRamification
    (hell : 0 < Module.finrank F.Carrier L.Carrier)
    (htot : L.canonicalTopologicalData.ramificationIndex =
      Module.finrank F.Carrier L.Carrier * F.canonicalTopologicalData.ramificationIndex) :
    L.canonicalTopologicalData.residueDegree = F.canonicalTopologicalData.residueDegree := by
  have h1 := F.canonicalTopologicalData.ramificationIndex_mul_residueDegree
  have h2 := L.canonicalTopologicalData.ramificationIndex_mul_residueDegree
  have h3 := Module.finrank_mul_finrank (Padic p) F.Carrier L.Carrier
  apply Nat.eq_of_mul_eq_mul_left
    (Nat.mul_pos hell F.canonicalTopologicalData.ramificationIndex_pos)
  calc Module.finrank F.Carrier L.Carrier * F.canonicalTopologicalData.ramificationIndex *
        L.canonicalTopologicalData.residueDegree
      = L.canonicalTopologicalData.ramificationIndex *
          L.canonicalTopologicalData.residueDegree := by rw [htot]
    _ = Module.finrank (Padic p) F.Carrier * Module.finrank F.Carrier L.Carrier := by
          rw [h2, h3]
    _ = Module.finrank F.Carrier L.Carrier * F.canonicalTopologicalData.ramificationIndex *
          F.canonicalTopologicalData.residueDegree := by
          rw [← h1]
          ring

/-- Under total ramification the determinant norm preserves normalized order. -/
theorem ord_normUnits_of_totalRamification
    (hell : 0 < Module.finrank F.Carrier L.Carrier)
    (htot : L.canonicalTopologicalData.ramificationIndex =
      Module.finrank F.Carrier L.Carrier * F.canonicalTopologicalData.ramificationIndex)
    (x : L.Carrierˣ) :
    F.canonicalTopologicalData.ord (normUnits F.Carrier L.Carrier x : F.Carrier) =
      L.canonicalTopologicalData.ord (x : L.Carrier) := by
  have h := residueDegree_mul_ord_relative_norm F L
    F.canonicalTopologicalData L.canonicalTopologicalData (x : L.Carrier)
  rw [residueDegree_eq_of_totalRamification F L hell htot] at h
  exact mul_left_cancel₀ (show (F.canonicalTopologicalData.residueDegree : ℤ) ≠ 0 by
    exact_mod_cast F.canonicalTopologicalData.residueDegree_pos.ne') h

/-- Valuation reduction: every field unit is a norm times a reduced integer
unit, once integer units can be reduced to level `t` modulo norms. -/
theorem exists_norm_mul_of_unit_reduction
    (hell : 0 < Module.finrank F.Carrier L.Carrier)
    (htot : L.canonicalTopologicalData.ramificationIndex =
      Module.finrank F.Carrier L.Carrier * F.canonicalTopologicalData.ramificationIndex)
    (t : ℕ)
    (hred : ∀ w ∈ F.canonicalTopologicalData.unitFiltration 0, ∃ y : L.Carrierˣ,
      w * (normUnits F.Carrier L.Carrier y)⁻¹ ∈ F.canonicalTopologicalData.unitFiltration t)
    (x : F.Carrierˣ) :
    ∃ y : L.Carrierˣ, ∃ z : F.canonicalTopologicalData.unitFiltration t,
      x = normUnits F.Carrier L.Carrier y * (z : F.Carrierˣ) := by
  let TF := F.canonicalTopologicalData
  let TL := L.canonicalTopologicalData
  let N := normUnits F.Carrier L.Carrier
  let uL : L.Carrierˣ := Units.mk0 TL.uniformizer
    (TL.coordinateUniformizer_ne_zero TL.uniformizer TL.ord_uniformizer)
  let k : ℤ := TF.ord (x : F.Carrier)
  let y0 : L.Carrierˣ := uL ^ k
  have hy0 : TF.ord (N y0 : F.Carrier) = k := by
    rw [ord_normUnits_of_totalRamification F L hell htot]
    change TL.ord ((uL ^ k : L.Carrierˣ) : L.Carrier) = k
    rw [Units.val_zpow_eq_zpow_val, TL.ord_zpow]
    change k * TL.ord TL.uniformizer = k
    rw [TL.ord_uniformizer, mul_one]
  let w : F.Carrierˣ := x * (N y0)⁻¹
  have hw : w ∈ TF.unitFiltration 0 := by
    apply TF.mem_unitFiltration_zero_of_ord_eq_zero
    change TF.ord ((x : F.Carrier) * ((N y0 : F.Carrierˣ)⁻¹ : F.Carrierˣ)) = 0
    rw [Units.val_inv_eq_inv_val, TF.ord_mul x.ne_zero (inv_ne_zero (N y0).ne_zero),
      TF.ord_inv, hy0]
    exact add_neg_cancel k
  obtain ⟨y1, hy1⟩ := hred w hw
  refine ⟨y0 * y1, ⟨w * (N y1)⁻¹, hy1⟩, ?_⟩
  change x = N (y0 * y1) * (x * (N y0)⁻¹ * (N y1)⁻¹)
  rw [map_mul]
  apply Units.ext
  simp only [Units.val_mul, Units.val_inv_eq_inv_val]
  field_simp

end Main

end PrimeRamifiedNormReductionProof

open PrimeRamifiedNormReductionProof

universe u v

/-- Higher-unit norm equalities above the break, at the break, and reduction of
every field unit to a norm times a unit of depth `t`. -/
theorem primeRamifiedNormReduction : PrimeRamifiedNormReduction.{u,v} := by
  intro p _ F L _ _ _ _ ell TF TL hell htot t hpat ψ N
  obtain ⟨-, hc0, hc1, hz, hcoef⟩ := primeRamifiedGradedNorm p F L hell htot t hpat
  obtain ⟨hbelow, -, habove⟩ :=
    hcoef TF.uniformizer TF.ord_uniformizer TL.uniformizer TL.ord_uniformizer
  have hell1 : 1 ≤ ell := hell.one_lt.le
  have hf : let := TF.topology; let := TL.topology; Continuous N := by
    let := TF.topology
    let := TL.topology
    exact (localNorm TF TL).continuous
  have hcont : ∀ n : ℕ, ∀ x ∈ TL.unitFiltration (ψ n), N x ∈ TF.unitFiltration n :=
    fun n x hx => hc0 n ⟨x, hx⟩
  have hcont_le : ∀ n : ℕ, n ≤ t → ∀ x ∈ TL.unitFiltration n, N x ∈ TF.unitFiltration n := by
    intro n hn x hx
    apply hcont n x
    change x ∈ TL.unitFiltration (if n ≤ t then n else t + ell * (n - t))
    rw [ite_eq_left hn]
    exact hx
  -- Clause 1: exact norms above the break.
  have hstep_above : ∀ m : ℕ, t < m → ∀ w ∈ TF.unitFiltration m,
      ∃ z ∈ TL.unitFiltration (ψ m), w * (N z)⁻¹ ∈ TF.unitFiltration (m + 1) := by
    intro m hm w hw
    obtain ⟨b, -, hb0, hb⟩ := habove m hm
    have hrb : PadicField.TopologicalData.relativeResidueMap TF TL (TF.residue b) ≠ 0 :=
      (map_ne_zero _).mpr hb0
    exact exists_step_positive TF TL N (PadicField.TopologicalData.relativeResidueMap TF TL)
      TF.uniformizer TF.ord_uniformizer TL.uniformizer TL.ord_uniformizer m (ψ m)
      (by omega) (psi_pos t ell m hell1 hm)
      (fun d => PadicField.TopologicalData.relativeResidueMap TF TL (TF.residue b) * d)
      (fun c => ⟨PadicField.TopologicalData.relativeResidueMap TF TL c /
          PadicField.TopologicalData.relativeResidueMap TF TL (TF.residue b),
        mul_div_cancel₀ _ hrb⟩)
      (hcont m) hb w hw
  have clause1 : ∀ n : ℕ, t < n →
      (TL.unitFiltration (ψ n)).map N = TF.unitFiltration n :=
    map_eq_of_steps TF TL N hf ψ (psi_monotone t ell) t hcont hstep_above
  -- Clause 2: exact norms one extension level higher, from the break on.
  have clause2 : ∀ n : ℕ, t ≤ n →
      (TL.unitFiltration (ψ n + 1)).map N = TF.unitFiltration (n + 1) := by
    intro n hn
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hc1 n ⟨x, hx⟩
    · rw [← clause1 (n + 1) (by omega)]
      exact Subgroup.map_mono (TL.unitFiltration_antitone (psi_succ_le t ell n hell1 hn))
  -- Clause 3: reduction of integer units below the break, then of the order.
  have hred : ∀ w ∈ TF.unitFiltration 0, ∃ y : L.Carrierˣ,
      w * (N y)⁻¹ ∈ TF.unitFiltration t := by
    intro w hw
    rcases Nat.eq_zero_or_pos t with ht | ht
    · refine ⟨1, ?_⟩
      rw [ht, map_one, inv_one, mul_one]
      exact hw
    have hellp : ell = p :=
      (lowerRamificationGroup_one_eq_top_iff_prime_degree F L hell htot).mp (by
        rw [hpat 1, ite_eq_left (show 1 ≤ t by omega)])
    refine exists_mem_of_finite_steps TF N t ?_ w hw
    intro m hm v hv
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · subst hm0
      obtain ⟨z, -, hz'⟩ := exists_step_zero TF TL N
        (PadicField.TopologicalData.relativeResidueMap TF TL) ell
        (fun c => by rw [hellp]; exact exists_units_pow_char_eq TL c)
        (hcont_le 0 (Nat.zero_le t)) hz v hv
      exact ⟨z, hz'⟩
    · obtain ⟨a, -, ha0, ha⟩ := hbelow m hm0 hm
      have hra : PadicField.TopologicalData.relativeResidueMap TF TL (TF.residue a) ≠ 0 :=
        (map_ne_zero _).mpr ha0
      obtain ⟨z, -, hz'⟩ := exists_step_positive TF TL N
        (PadicField.TopologicalData.relativeResidueMap TF TL)
        TF.uniformizer TF.ord_uniformizer TL.uniformizer TL.ord_uniformizer m m hm0 hm0
        (fun d => PadicField.TopologicalData.relativeResidueMap TF TL (TF.residue a) * d ^ p)
        (fun c => by
          obtain ⟨d, hd⟩ := exists_pow_char_eq TL
            (PadicField.TopologicalData.relativeResidueMap TF TL c /
              PadicField.TopologicalData.relativeResidueMap TF TL (TF.residue a))
          exact ⟨d, by rw [hd]; exact mul_div_cancel₀ _ hra⟩)
        (hcont_le m hm.le) ha v hv
      exact ⟨z, hz'⟩
  exact ⟨clause1, clause2,
    exists_norm_mul_of_unit_reduction F L hell.pos htot t hred⟩

end Langlands.LocalClassField
