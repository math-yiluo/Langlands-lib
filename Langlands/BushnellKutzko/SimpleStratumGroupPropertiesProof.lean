import Langlands.BushnellKutzko.SimpleStratumGroupPropertiesStatement
import Langlands.BushnellKutzko.SimpleStratumLatticePropertiesProof
import Langlands.BushnellKutzko.AdjointLatticeBounds
import Langlands.BushnellKutzko.NormalizerProof
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.GroupTheory.Commutator.Basic

/-! # The subgroup properties of a simple stratum (BK93 (3.1.14)–(3.1.15)) -/

open ValuativeRel
open scoped Pointwise commutatorElement

namespace Langlands.BushnellKutzko

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

/-- If an ambient order unit belongs to a subalgebra, its inverse belongs to that subalgebra.
A monic relation for the inverse in the finite order expresses it as a polynomial in the unit. -/
private theorem inv_mem_subalgebra (L : LatticeChain 𝒪[F] F V)
    (R : Subalgebra 𝒪[F] A) {g : G} (hg : g ∈ L.unitFiltration 0) (hgR : (g : A) ∈ R) :
    (↑g⁻¹ : A) ∈ R := by
  have hfg : L.order.toSubmodule.FG := L.endFiltration_zero_fg
  obtain ⟨p, hp, hroot⟩ := IsIntegral.of_mem_of_fg L.order hfg (↑g⁻¹ : A) hg.2.1
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ,
    hp.coeff_natDegree, map_one, one_mul] at hroot
  let d := p.natDegree
  let c (i : ℕ) : A := algebraMap 𝒪[F] A (p.coeff i)
  have hpow (i : ℕ) (hi : i ≤ d) : (↑g⁻¹ : A) ^ i * (g : A) ^ d = (g : A) ^ (d - i) := by
    calc
      _ = (↑g⁻¹ : A) ^ i * ((g : A) ^ i * (g : A) ^ (d - i)) := by
        rw [← pow_add, Nat.add_sub_of_le hi]
      _ = _ := by
        rw [← mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val,
          ← Units.val_mul, inv_pow, inv_mul_cancel, Units.val_one, one_mul]
  have hsum : (∑ i ∈ Finset.range d, c i * (g : A) ^ (d - i - 1)) + (↑g⁻¹ : A) = 0 := by
    calc
      _ = ((∑ i ∈ Finset.range d, c i * (↑g⁻¹ : A) ^ i) + (↑g⁻¹ : A) ^ d) *
            (g : A) ^ d * (↑g⁻¹ : A) := by
        rw [add_mul, add_mul, Finset.sum_mul, Finset.sum_mul]
        congr 1
        · apply Finset.sum_congr rfl
          intro i hi
          have hi' := Finset.mem_range.mp hi
          rw [mul_assoc (c i), hpow i hi'.le, show d - i = d - i - 1 + 1 by omega,
            pow_succ, mul_assoc (c i), Units.mul_inv_cancel_right]
          simp
        · rw [hpow d le_rfl, Nat.sub_self, pow_zero, one_mul]
      _ = 0 := by
        change ((∑ i ∈ Finset.range p.natDegree, _ ) + _) * _ * _ = 0
        rw [hroot, zero_mul, zero_mul]
  rw [eq_neg_of_add_eq_zero_right hsum]
  exact R.neg_mem (R.sum_mem fun i _ => R.mul_mem (R.algebraMap_mem _) (R.pow_mem hgR _))

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem mem_centralizerLattice_zero_iff (L : LatticeChain 𝒪[F] F V) (β : A) {g : G} :
    (g : A) ∈ centralizerLattice L β 0 ↔ (g : A) ∈ L.order ∧ g ∈ centralizerUnitGroup β := by
  change (g : A) ∈ L.endFiltration 0 ∧ β * (g : A) - (g : A) * β = 0 ↔ _
  rw [sub_eq_zero, ← L.mem_order_iff_mem_endFiltration]
  rfl

private theorem closure_order_units (L : LatticeChain 𝒪[F] F V)
    (R : Subalgebra 𝒪[F] A) (m : ℕ) :
    (Subgroup.closure {g : G | g ∈ L.unitFiltration m ∧ (g : A) ∈ R} : Set G) =
      {g : G | g ∈ L.unitFiltration m ∧ (g : A) ∈ R} := by
  apply Set.Subset.antisymm _ Subgroup.subset_closure
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => exact ⟨one_mem _, one_mem R⟩
  | mul x y _ _ hx hy => exact ⟨mul_mem hx.1 hy.1, R.mul_mem hx.2 hy.2⟩
  | inv x _ hx =>
    exact ⟨inv_mem hx.1, inv_mem_subalgebra L R (L.unitFiltration_antitone (Nat.zero_le m) hx.1) hx.2⟩

/-- An additive splitting by the relative order and a deep submodule gives a unit product. -/
private theorem order_units_mul_relative (L : LatticeChain 𝒪[F] F V) (β : A)
    (R : Subalgebra 𝒪[F] A) {I : Submodule 𝒪[F] A} {m : ℕ} {a : ℤ}
    (hR : R.toSubmodule = centralizerLattice L β 0 ⊔ I) (hI : I ≤ L.endFiltration a)
    (hm : (m : ℤ) ≤ a) :
    {g : G | g ∈ L.unitFiltration m ∧ (g : A) ∈ R} =
      (relativeUnitFiltration L β m : Set G) *
        {g : G | g ∈ L.unitFiltration a.toNat ∧ (g : A) ∈ R} := by
  have hma : m ≤ a.toNat := by omega
  have hac : (a.toNat : ℤ) = a := Int.toNat_of_nonneg (by omega)
  have hrelative {g : G} (hg : g ∈ relativeUnitFiltration L β m) : (g : A) ∈ R := by
    have hq := (mem_centralizerLattice_zero_iff L β).2 ⟨hg.2.1, hg.1⟩
    change (g : A) ∈ R.toSubmodule
    exact hR.symm ▸ ((le_sup_left : centralizerLattice L β 0 ≤ centralizerLattice L β 0 ⊔ I) hq)
  apply Set.Subset.antisymm
  · intro g hg
    have hgm : g ∈ L.unitFiltration m := hg.1
    have hgR : (g : A) ∈ R := hg.2
    by_cases heq : m = a.toNat
    · exact ⟨1, one_mem _, g, ⟨heq ▸ hgm, hgR⟩, one_mul g⟩
    have ha : 1 ≤ a.toNat := by omega
    have hdecomp : (g : A) ∈ centralizerLattice L β 0 ⊔ I := hR ▸ hgR
    obtain ⟨b, hb, x, hx, hbx⟩ := Submodule.mem_sup.mp hdecomp
    have hg0 := L.unitFiltration_antitone (Nat.zero_le m) hgm
    have hinv := L.mem_order_iff_mem_endFiltration.mp hg0.2.1
    have hx' := hI hx
    have hsmall : -(↑g⁻¹ : A) * x ∈ L.endFiltration (a.toNat : ℤ) := by
      rw [hac, neg_mul, neg_mem_iff]
      simpa only [zero_add] using L.mul_mem_endFiltration hinv hx'
    obtain ⟨e, he, hval⟩ := L.exists_mem_unitFiltration ha hsmall
    have hge : ((g * e : G) : A) = b := by
      rw [Units.val_mul, hval, mul_add, mul_one, neg_mul, mul_neg, Units.mul_inv_cancel_left]
      simp [← hbx, add_assoc]
    have hbg : g * e ∈ relativeUnitFiltration L β m :=
      ⟨(mem_centralizerLattice_zero_iff L β).1 (hge.symm ▸ hb) |>.2,
        mul_mem hgm (L.unitFiltration_antitone hma he)⟩
    have heR : (e : A) ∈ R := by
      have hxR : x ∈ R.toSubmodule :=
        hR.symm ▸ ((le_sup_right : I ≤ centralizerLattice L β 0 ⊔ I) hx)
      rw [hval]
      exact R.add_mem (R.one_mem) (R.mul_mem (R.neg_mem (inv_mem_subalgebra L R hg0 hgR)) hxR)
    have heinv := inv_mem_subalgebra L R (L.unitFiltration_antitone (Nat.zero_le _) he) heR
    exact ⟨g * e, hbg, e⁻¹, ⟨inv_mem he, heinv⟩, by simp [mul_assoc]⟩
  · rintro g ⟨b, hb, e, he, rfl⟩
    exact ⟨mul_mem hb.2 (L.unitFiltration_antitone hma he.1), R.mul_mem (hrelative hb) he.2⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem finiteCriticalDepth_of_tail_eq_nil (S : Stratum 𝒪[F] F V)
    (q : S.DefiningSequenceChoice) (h : q.tail = []) :
    finiteCriticalDepth S.chain S.n S.b = S.n := by
  have hs : q.steps = 0 := by
    simpa only [Stratum.DefiningSequenceChoice.tail, List.length_ofFn, List.length_nil] using
      congrArg List.length h
  have hlast : Fin.last q.steps = 0 := Fin.ext (by simpa using hs)
  have hterminal := q.isDefiningSequence.2.2.2.2.2.2.1
  rw [hlast, q.firstElement] at hterminal
  rcases hterminal with h | h <;> simp [finiteCriticalDepth, simpleCriticalDepth, h]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem simpleStratumLattices_split (S : Stratum 𝒪[F] F V) (q : S.DefiningSequenceChoice) :
    let L := S.chain
    let r := finiteCriticalDepth L S.n S.b
    ∃ IH IJ : Submodule 𝒪[F] A,
      simpleHLattice L S.n S.b q.tail = centralizerLattice L S.b 0 ⊔ IH ∧
      IH ≤ L.endFiltration (simpleHCutoff r) ∧
      simpleJLattice L S.n S.b q.tail = centralizerLattice L S.b 0 ⊔ IJ ∧
      IJ ≤ L.endFiltration (simpleJCutoff r) := by
  intro L r
  cases htail : q.tail with
  | nil =>
    have hr : r = S.n := finiteCriticalDepth_of_tail_eq_nil S q htail
    rw [hr]
    exact ⟨_, _, rfl, le_rfl, rfl, le_rfl⟩
  | cons γ tail =>
    exact ⟨simpleHLattice L S.n γ tail ⊓ L.endFiltration (simpleHCutoff r),
      simpleJLattice L S.n γ tail ⊓ L.endFiltration (simpleJCutoff r),
      rfl, inf_le_right, rfl, inf_le_right⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem order_units_iff_sub_one (L : LatticeChain 𝒪[F] F V)
    (R : Subalgebra 𝒪[F] A) (m : ℕ) (g : G) :
    (g ∈ L.unitFiltration m ∧ (g : A) ∈ R) ↔
      g ∈ L.unitFiltration m ∧ (g : A) - 1 ∈ R.toSubmodule ⊓ L.endFiltration m := by
  constructor
  · rintro ⟨hg, hgR⟩
    exact ⟨hg, R.sub_mem hgR R.one_mem, hg.2.2⟩
  · rintro ⟨hg, hgR, _⟩
    exact ⟨hg, by simpa only [sub_add_cancel] using R.add_mem hgR R.one_mem⟩

/-- To normalize a group cut out by an additive layer, preserve the layer by conjugation. -/
private theorem le_normalizer_of_layer (L : LatticeChain 𝒪[F] F V)
    {K H : Subgroup G} {m : ℕ} {M : Submodule 𝒪[F] A}
    (hK : K ≤ L.stabilizer)
    (hH : ∀ g : G, g ∈ H ↔ g ∈ L.unitFiltration m ∧ (g : A) - 1 ∈ M)
    (hM : ∀ g ∈ K, ∀ x ∈ M, (g : A) * x * (↑g⁻¹ : A) ∈ M) :
    K ≤ Subgroup.normalizer (H : Set G) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro g hg z hz
  have hgU : g ∈ Subgroup.normalizer (L.unitFiltration m : Set G) := by
    rw [(normalizer F V L).2.2.1 m]
    exact hK hg
  obtain ⟨hzU, hzM⟩ := (hH z).mp hz
  refine (hH _).mpr ⟨(Subgroup.mem_normalizer_iff.mp hgU z).mp hzU, ?_⟩
  simpa only [Units.val_mul, mul_sub, sub_mul, mul_one, Units.mul_inv] using
    hM g hg ((z : A) - 1) hzM

/-- The lattice properties of a simple stratum imply its subgroup properties. -/
private theorem simpleStratumGroupProperties_of_lattices
    (lattices : SimpleStratumLatticePropertiesStatement.{uF, uV}) :
    SimpleStratumGroupPropertiesStatement.{uF, uV} := by
  intro F _ _ _ _ V _ _ S hr hs q
  let EndV := Module.End F V
  let UnitsV := EndVˣ
  let L := S.chain
  let H := simpleHGroup L S.n S.b q.tail
  let J := simpleJGroup L S.n S.b q.tail
  let K := relativeOrderNormalizer L S.b
  let r := finiteCriticalDepth L S.n S.b
  obtain ⟨-, horders, -, hnorm, ⟨-, hproducts, hideal⟩, -⟩ := lattices F V S hr hs q
  obtain ⟨-, -, ⟨RH, hRH⟩, ⟨RJ, hRJ⟩, -, -, -, hlayers⟩ := horders
  have hH (m : ℕ) : (H m : Set UnitsV) = {g : UnitsV | g ∈ L.unitFiltration m ∧ (g : EndV) ∈ RH} := by
    unfold H simpleHGroup simpleHCarrier
    rw [← hRH]
    exact closure_order_units L RH m
  have hJ (m : ℕ) : (J m : Set UnitsV) = {g : UnitsV | g ∈ L.unitFiltration m ∧ (g : EndV) ∈ RJ} := by
    unfold J simpleJGroup simpleJCarrier
    rw [← hRJ]
    exact closure_order_units L RJ m
  have hHL (m : ℕ) (g : UnitsV) :
      g ∈ H m ↔ g ∈ L.unitFiltration m ∧ (g : EndV) - 1 ∈ simpleHLayer L S.n S.b q.tail m := by
    change g ∈ (H m : Set UnitsV) ↔ _
    rw [hH m, simpleHLayer, ← hRH]
    exact order_units_iff_sub_one L RH m g
  have hJL (m : ℕ) (g : UnitsV) :
      g ∈ J m ↔ g ∈ L.unitFiltration m ∧ (g : EndV) - 1 ∈ simpleJLayer L S.n S.b q.tail m := by
    change g ∈ (J m : Set UnitsV) ↔ _
    rw [hJ m, simpleJLayer, ← hRJ]
    exact order_units_iff_sub_one L RJ m g
  have hJval {g : UnitsV} (hg : g ∈ J 0) : (g : EndV) ∈ simpleJLattice L S.n S.b q.tail := by
    change g ∈ (J 0 : Set UnitsV) at hg
    rw [hJ 0] at hg
    rw [← hRJ]
    exact hg.2
  have hJanti : Antitone J := simpleJGroup_antitone L S.n S.b q.tail
  have hJ0 : J 0 ≤ L.unitFiltration 0 := simpleJGroup_le_unitFiltration L S.n S.b q.tail 0
  have hle (m : ℕ) : H m ≤ J m := by
    intro g hg
    obtain ⟨hgU, hgH⟩ := (hHL m g).mp hg
    exact (hJL m g).mpr ⟨hgU, (hlayers m).2.2 hgH⟩
  refine ⟨fun m => ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simpa only [simpleHCarrier, ← hRH, Subalgebra.mem_toSubmodule] using hH m
  · simpa only [simpleJCarrier, ← hRJ, Subalgebra.mem_toSubmodule] using hJ m
  · intro _
    obtain ⟨IH, IJ, hIH, hcutH, hIJ, hcutJ⟩ := simpleStratumLattices_split S q
    constructor
    · intro m hm
      change (H m : Set UnitsV) = (relativeUnitFiltration L S.b m : Set UnitsV) * ↑(H (simpleHCutoff r).toNat)
      rw [hH m, hH (simpleHCutoff r).toNat]
      exact order_units_mul_relative L S.b RH (hRH.trans hIH) hcutH hm
    · intro m hm
      change (J m : Set UnitsV) = (relativeUnitFiltration L S.b m : Set UnitsV) * ↑(J (simpleJCutoff r).toNat)
      rw [hJ m, hJ (simpleJCutoff r).toNat]
      exact order_units_mul_relative L S.b RJ (hRJ.trans hIJ) hcutJ hm
  · intro m
    have hK : K ≤ L.stabilizer := inf_le_right
    exact ⟨le_normalizer_of_layer L hK (hHL m) (fun g hg x hx => ((hnorm m).2 g hg x).1.mpr hx),
      le_normalizer_of_layer L hK (hJL m) (fun g hg x hx => ((hnorm m).2 g hg x).2.mpr hx)⟩
  · intro m
    refine ⟨hle m, (hle (m + 1)).trans (hJanti (Nat.zero_le _)), ?_⟩
    apply le_normalizer_of_layer L (hJ0.trans ((normalizer F V L).1 0).1) (hHL (m + 1))
    intro g hg x hx
    have hi := hideal (m + 1) (by omega)
    exact hi.2.2 (Submodule.mul_mem_mul (hi.2.1 (Submodule.mul_mem_mul (hJval hg) hx))
      (hJval (inv_mem hg)))
  · intro k l hk hl
    apply Subgroup.commutator_le.mpr
    intro g hg t ht
    have hg0 := hJanti (Nat.zero_le k) hg
    have ht0 := hJanti (Nat.zero_le l) ht
    have hcomm0 : ⁅g, t⁆ ∈ L.unitFiltration 0 := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem (hJ0 hg0) (hJ0 ht0)) (inv_mem (hJ0 hg0))) (inv_mem (hJ0 ht0))
    have hx := ((hJL k g).mp hg).2
    have hy := ((hJL l t).mp ht).2
    have hxy := sub_mem (hproducts k l hk hl (Submodule.mul_mem_mul hx hy))
      (by simpa only [Nat.add_comm] using hproducts l k hl hk (Submodule.mul_mem_mul hy hx))
    have hformula : (↑⁅g, t⁆ : EndV) - 1 =
        (((g : EndV) - 1) * ((t : EndV) - 1) - ((t : EndV) - 1) * ((g : EndV) - 1)) *
          (↑g⁻¹ : EndV) * (↑t⁻¹ : EndV) := by
      have he :
          ((g : EndV) - 1) * ((t : EndV) - 1) - ((t : EndV) - 1) * ((g : EndV) - 1) =
            (g : EndV) * (t : EndV) - (t : EndV) * (g : EndV) := by noncomm_ring
      rw [he, sub_mul, sub_mul]
      simp only [commutatorElement_def, Units.val_mul, Units.mul_inv_cancel_right, Units.mul_inv]
    have hc : (↑⁅g, t⁆ : EndV) - 1 ∈ simpleHLayer L S.n S.b q.tail (k + l) := by
      rw [hformula]
      have hi := hideal (k + l) (by omega)
      exact hi.2.2 (Submodule.mul_mem_mul (hi.2.2 (Submodule.mul_mem_mul hxy (hJval (inv_mem hg0))))
        (hJval (inv_mem ht0)))
    exact (hHL _ _).mpr ⟨⟨hcomm0.1, hcomm0.2.1, hc.2⟩, hc⟩

/-- The subgroup properties of a simple stratum, BK93 (3.1.14)–(3.1.15). -/
theorem simpleStratumGroupProperties : SimpleStratumGroupPropertiesStatement.{uF, uV} :=
  simpleStratumGroupProperties_of_lattices simpleStratumLatticeProperties

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- At positive depth, the lattice membership by itself implies ambient filtration membership. -/
private theorem mem_group_iff_of_pos (L : LatticeChain 𝒪[F] F V) (M : Submodule 𝒪[F] A)
    (P : Subgroup G) {m : ℕ} (hm : 1 ≤ m)
    (hP : (P : Set G) = {g : G | g ∈ L.unitFiltration m ∧ (g : A) ∈ M}) (g : G) :
    g ∈ P ↔ (g : A) - 1 ∈ M ⊓ L.endFiltration m := by
  have hone : (1 : A) ∈ M := by
    have h : (1 : G) ∈ {g : G | g ∈ L.unitFiltration m ∧ (g : A) ∈ M} := by
      rw [← hP]
      exact P.one_mem
    exact h.2
  change g ∈ (P : Set G) ↔ _
  rw [hP]
  constructor
  · intro hg
    exact ⟨M.sub_mem hg.2 hone, hg.1.2.2⟩
  · intro hg
    obtain ⟨u, hu, hval⟩ := L.exists_mem_unitFiltration hm hg.2
    have hug : u = g := Units.ext (by simpa only [add_sub_cancel, add_comm] using hval)
    exact ⟨hug ▸ hu, by simpa only [sub_add_cancel] using M.add_mem hg.1 hone⟩

/-- Positive-depth `H` membership is detected by subtracting one. -/
theorem simpleHGroup_mem_iff_of_pos
    (S : Stratum 𝒪[F] F V) (hr : S.r = 0) (hs : S.IsSimple) (q : S.DefiningSequenceChoice)
    {m : ℕ} (hm : 1 ≤ m) {g : G} :
    g ∈ simpleHGroup S.chain S.n S.b q.tail m ↔
      (g : A) - 1 ∈ simpleHLayer S.chain S.n S.b q.tail m :=
  mem_group_iff_of_pos S.chain _ _ hm ((simpleStratumGroupProperties F V S hr hs q).1 m).1 g

/-- Positive-depth `J` membership is detected by subtracting one. -/
theorem simpleJGroup_mem_iff_of_pos
    (S : Stratum 𝒪[F] F V) (hr : S.r = 0) (hs : S.IsSimple) (q : S.DefiningSequenceChoice)
    {m : ℕ} (hm : 1 ≤ m) {g : G} :
    g ∈ simpleJGroup S.chain S.n S.b q.tail m ↔
      (g : A) - 1 ∈ simpleJLayer S.chain S.n S.b q.tail m :=
  mem_group_iff_of_pos S.chain _ _ hm ((simpleStratumGroupProperties F V S hr hs q).1 m).2 g

end Langlands.BushnellKutzko
