import Langlands.BushnellKutzko.RefinementCentralizer
import Langlands.BushnellKutzko.RefinementElementExactness
import Langlands.BushnellKutzko.StratumApproximationReduction

/-! # Reflection of simplicity from a full-degree simple stratum

A comparison at any depth of simplicity, extending the top-depth assertion of
BK93 (2.2.2), printed pp. 52–53.
-/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko.PureApproximation

universe uF uV

/-- An equivalent stratum with the same chain and integers as a full-degree simple stratum
is simple and again has full generated-field degree. -/
def MaximalSimpleReflectionStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (V : Type uV) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (S T : Stratum 𝒪[F] F V), S.IsSimple → elementDegree F S.b = Module.finrank F V →
      T.chain = S.chain → T.n = S.n → T.r = S.r → S.Equivalent T →
      T.IsSimple ∧ elementDegree F T.b = Module.finrank F V

private theorem withBot_le_sub_one {a : WithBot ℤ} {k : ℤ} (h : a < (k : WithBot ℤ)) :
    a ≤ ((k - 1 : ℤ) : WithBot ℤ) := by
  cases a with
  | bot => exact bot_le
  | coe j =>
    have hj := WithBot.coe_lt_coe.mp h
    exact WithBot.coe_le_coe.mpr (by omega)

private theorem finrank_eq_one_of_full_degree {F V : Type*} [Field F] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (b : Module.End F V) (hf : IsField (elementAlgebra b))
    (h : elementDegree F b = Module.finrank F V) :
    letI := hf.toField
    Module.finrank (elementAlgebra b) V = 1 := by
  let : Field (elementAlgebra b) := hf.toField
  change Module.finrank F (elementAlgebra b) = _ at h
  have ht := Module.finrank_mul_finrank F (elementAlgebra b) V
  rw [← h] at ht
  have hp : 0 < Module.finrank F (elementAlgebra b) := Module.finrank_pos
  apply Nat.eq_of_mul_eq_mul_left hp
  rw [mul_one]
  exact ht

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
/-- Use adjoint exactness at the original simple element and field-line centralizer comparison. -/
theorem maximalSimpleReflection : MaximalSimpleReflectionStatement.{uF, uV} := by
  intro F _ _ _ _ V _ _ _ S T hS hdeg hc hn hr heq
  classical
  let A := S.chain
  let y := T.b
  obtain ⟨⟨hE, hA⟩, hval⟩ := hS.1
  let E : Type uV := elementAlgebra S.b
  let : Field E := hE.toField
  let : Nontrivial V := A.nontrivialSpace
  have hE1 : Module.finrank E V = 1 := finrank_eq_one_of_full_degree S.b hE hdeg
  let w : Module.Basis (Fin 1) E V := Module.basisUnique (Fin 1) hE1
  have hw : RelSplits (L := E) A w := by
    intro i c h j
    simpa only [Fin.sum_univ_one, Fin.eq_zero j] using h
  have hunit (j l : Fin 1) : matUnit F w j l = 1 := by
    simpa only [Fin.sum_univ_one, Fin.eq_zero j, Fin.eq_zero l] using (sum_matUnit_self (F := F) w)
  have hall (z : Module.End F V) (j l : Fin 1) :
      z * matUnit F w j l = matUnit F w j l * z := by rw [hunit, mul_one, one_mul]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have hdiff : S.b - y ∈ A.endFiltration (-S.r) := Stratum.sub_mem_of_equivalent heq
  have hks : criticalExponent A S.b ≤ ((-S.r - 1 : ℤ) : WithBot ℤ) :=
    withBot_le_sub_one hS.2
  have hnear (t : ℤ) (X : Module.End F V) (hX : X ∈ A.endFiltration t)
      (hXy : y * X - X * y ∈ A.endFiltration (t - S.r)) :
      ∃ Z : Module.End F V,
        (∀ a : E, Z * subfieldEmbedding F E V a = subfieldEmbedding F E V a * Z) ∧
        X - Z ∈ A.endFiltration (t + 1) := by
    have hleft := A.mul_mem_endFiltration hdiff hX
    have hright := A.mul_mem_endFiltration hX hdiff
    have hδ : (S.b - y) * X - X * (S.b - y) ∈ A.endFiltration (t - S.r) := by
      apply sub_mem
      · rw [show t - S.r = -S.r + t by ring]
        exact hleft
      · simpa only [sub_eq_add_neg] using hright
    have hbX : S.b * X - X * S.b ∈ A.endFiltration ((t + 1) + (-S.r - 1)) := by
      rw [show (t + 1) + (-S.r - 1) = t - S.r by ring]
      convert add_mem hXy hδ using 1
      noncomm_ring
    obtain ⟨Z, hz, hXZ⟩ := exists_commute_sub_mem A S.b hE hA hks (t + 1) X hbX
    refine ⟨Z, fun a => ?_, hXZ⟩
    have hzs : Commute Z S.b := (sub_eq_zero.mp hz).symm
    have ha : subfieldEmbedding F E V a ∈ elementAlgebra S.b := a.property
    exact (Algebra.commute_of_mem_adjoin_singleton_of_commute ha hzs).eq
  have hcore (t : ℤ) (X : Module.End F V) (hX : X ∈ A.endFiltration t) (hXy : Commute X y) :
      ∃ Z : Module.End F V,
        (∀ a : E, Z * subfieldEmbedding F E V a = subfieldEmbedding F E V a * Z) ∧
        X - Z ∈ A.endFiltration (t + 1) := by
    apply hnear t X hX
    rw [hXy.eq, sub_self]
    exact zero_mem _
  have hNy : NormalizingUnits A (elementAlgebra y) :=
    normalizingUnits_elementAlgebra A hπ hA hw 0 hcore (hall y)
  obtain ⟨hyF, hyN⟩ := isField_of_normalizingUnits A hNy
  -- Full degree follows from the surjective entry map.
  have hydeg : elementDegree F y = Module.finrank F V := by
    let K : Type uV := elementAlgebra y
    let : Field K := hyF.toField
    let f : K →ₗ[F] E := (lineProj F w 0) ∘ₗ (LinearMap.applyₗ (w 0)) ∘ₗ
      (elementAlgebra y).val.toLinearMap
    have hsurj : Function.Surjective f := by
      intro a
      obtain ⟨z, hz, ha⟩ := exists_mem_elementAlgebra_entry_eq A hπ hA hw 0 hcore (hall y) a
      exact ⟨⟨z, hz⟩, ha⟩
    have hlo := LinearMap.finrank_le_finrank_of_surjective hsurj
    have hhi : Module.finrank F K ≤ Module.finrank F V := by
      let : FiniteDimensional K V := Module.Finite.of_restrictScalars_finite F K V
      rw [← Module.finrank_mul_finrank F K V]
      exact Nat.le_mul_of_pos_right _ Module.finrank_pos
    change Module.finrank F E = Module.finrank F V at hdeg
    change Module.finrank F K = _
    rw [hdeg] at hlo
    exact le_antisymm hhi hlo
  -- The congruence changes no valuation at the strictly earlier initial level.
  have hyval : A.valuation y = ((-S.n : ℤ) : WithTop ℤ) := by
    have hb0 : S.b ≠ 0 := by
      intro h
      simp [h, LatticeChain.valuation] at hval
      exact WithTop.top_ne_coe hval
    obtain ⟨k, hk, hk'⟩ := exists_depth A hπ hb0
    have hkn : k = -S.n := WithTop.coe_injective
      ((A.valuation_eq_of_mem_of_notMem hk hk').symm.trans hval)
    subst k
    have hrn := S.r_lt_n
    have hb' := A.endFiltration_antitone (show -S.n + 1 ≤ -S.r by omega) hdiff
    apply A.valuation_eq_of_mem_of_notMem
    · have h := sub_mem hk (A.endFiltration_antitone (show -S.n ≤ -S.n + 1 by omega) hb')
      rwa [sub_sub_cancel] at h
    · intro h
      have hh := add_mem hb' h
      rw [sub_add_cancel] at hh
      exact hk' hh
  -- Approximation by the old field can be replaced by approximation by the new one.
  have hN : adjointLattice A y (-S.r) ≤ centralizerLattice A y 0 ⊔ A.endFiltration 1 := by
    intro X hX
    have hcom' : y * X - X * y ∈ A.endFiltration (-S.r) := hX.2
    have hcom : y * X - X * y ∈ A.endFiltration (0 - S.r) := by
      simpa only [zero_sub] using hcom'
    obtain ⟨Z, hz, hXZ⟩ := hnear 0 X hX.1 hcom
    rw [zero_add] at hXZ
    have hZ : Z ∈ Set.range (subfieldEmbedding F E V) := by
      refine ⟨w.repr (Z (w 0)) 0, ?_⟩
      have hdiag := diagonal_compress_of_commute w 0 (hall Z)
      rwa [compress_of_commute w 0 hz, diagonal_mulLeft] at hdiag
    have hZ0 : Z ∈ A.endFiltration 0 := by
      have hh := sub_mem hX.1 (A.endFiltration_antitone (show (0 : ℤ) ≤ 1 by decide) hXZ)
      rwa [sub_sub_cancel] at hh
    obtain ⟨Y, hY, hZY⟩ := approx_range_elementAlgebra A hπ hA hw 0 hcore (hall y) Z hZ 0 hZ0
    have hXY : X - Y ∈ A.endFiltration 1 := by
      simpa only [zero_add, sub_add_sub_cancel] using add_mem hXZ hZY
    have hY0 : Y ∈ A.endFiltration 0 := by
      have hh := sub_mem hX.1 (A.endFiltration_antitone (show (0 : ℤ) ≤ 1 by decide) hXY)
      rwa [sub_sub_cancel] at hh
    have hycomm : y * Y - Y * y = 0 :=
      sub_eq_zero.mpr (Algebra.commute_of_mem_adjoin_self hY).eq
    exact Submodule.mem_sup.mpr ⟨Y, ⟨hY0, hycomm⟩, X - Y, hXY, by abel⟩
  have hky : criticalExponent A y < ((-S.r : ℤ) : WithBot ℤ) := by
    by_cases h : elementAlgebra y = ⊥
    · unfold criticalExponent
      rw [ite_eq_left h]
      exact WithBot.bot_lt_coe _
    · obtain ⟨k, hk, hky⟩ := exists_isGreatest_criticalIndexSet A y hyF hyN h
      rw [hky, WithBot.coe_lt_coe]
      by_contra! hk'
      apply hk.1
      intro x hx
      exact hN ⟨hx.1, A.endFiltration_antitone hk' hx.2⟩
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, hydeg⟩
  · rw [hc]
    exact ⟨hyF, hyN⟩
  · rw [hc, hn]
    exact hyval
  · rw [hc, hr]
    exact hky

end Langlands.BushnellKutzko.PureApproximation
