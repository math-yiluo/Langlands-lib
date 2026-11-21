import Langlands.BaseChange.DifferentIdealComparison
import Langlands.LocalFactor.DeligneHenniartTopLayerDifferent
import Langlands.LocalFactor.Ramification.InductionProof

/-! # Ramification identities in a finite Artin conductor comparison -/

noncomputable section

open IsLocalRing ValuativeRel
open scoped Langlands.ClassFieldTheory.Local

namespace Langlands.BaseChange

open ClassFieldTheory.Local
open PadicField.TopologicalData Ramification.Padic
open LocalFactor.NonabelianSystem.DeligneHenniart.TopLayer

universe u v w

section Relative

variable {p : ℕ} [Fact p.Prime] {K : PadicField.{u} p} {L : PadicField.{v} p}
  [Algebra K.Carrier L.Carrier] [IsScalarTower (Padic p) K.Carrier L.Carrier]
  (T : K.TopologicalData) (S : L.TopologicalData)

private theorem relativeValuativeExtension :
    letI := T.valuativeRel
    letI := S.valuativeRel
    ValuativeExtension K.Carrier L.Carrier := by
  let := T.valuativeRel
  let := S.valuativeRel
  refine ⟨fun x y => ?_⟩
  rw [(valuation K.Carrier).vle_iff_le, (valuation L.Carrier).vle_iff_le]
  by_cases hy : y = 0
  · simp [hy]
  have hval : 0 < valuation K.Carrier y :=
    pos_iff_ne_zero.mpr ((map_ne_zero (valuation K.Carrier)).mpr hy)
  have hval' : 0 < valuation L.Carrier (algebraMap K.Carrier L.Carrier y) :=
    pos_iff_ne_zero.mpr ((map_ne_zero (valuation L.Carrier)).mpr ((map_ne_zero _).mpr hy))
  have hm := relative_mem_integers_iff T S (x / y)
  change valuation L.Carrier (algebraMap K.Carrier L.Carrier (x / y)) ≤ 1 ↔
    valuation K.Carrier (x / y) ≤ 1 at hm
  simpa only [map_div₀, div_le_one₀ hval, div_le_one₀ hval'] using hm

private theorem relativeContinuous :
    letI := T.topology
    letI := S.topology
    Continuous (algebraMap K.Carrier L.Carrier) := by
  let := T.topology
  let := S.topology
  let := T.valuativeRel
  let := S.valuativeRel
  let := T.localField
  let := S.localField
  let := T.moduleTopology
  let := S.moduleTopology
  exact IsModuleTopology.continuous_of_linearMap
    (IsScalarTower.toAlgHom (Padic p) K.Carrier L.Carrier).toLinearMap

private theorem lowerGroupOrder_eq_ramificationFactor [IsGalois K.Carrier L.Carrier] :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := S.topology
    letI := S.valuativeRel
    letI := S.localField
    letI := relativeValuativeExtension T S
    lowerGroupOrder S K.Carrier 0 = localRamificationFactor K.Carrier L.Carrier := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := S.topology
  let := S.valuativeRel
  let := S.localField
  let := relativeValuativeExtension T S
  let := relativeIntegerAlgebra T S
  let := integerAction S K.Carrier
  let : FiniteDimensional K.Carrier L.Carrier :=
    Module.Finite.of_restrictScalars_finite (Padic p) K.Carrier L.Carrier
  let := relativeIntegerFieldAlgebra (E := L) T
  let := (LocalClassField.NYLL.relativeIntegerStructure p K L T S).2
  let : Module.IsTorsionFree T.Integers S.Integers :=
    relativeIntegerAlgebra_isTorsionFree T S
  let : IsLocalHom (algebraMap T.Integers S.Integers) := relativeIntegerMap_isLocalHom T S
  let : IsGaloisGroup (L.Carrier ≃ₐ[K.Carrier] L.Carrier) T.Integers S.Integers :=
    isGaloisGroup_integers T S
  let : Algebra.IsIntegral T.Integers S.Integers := Algebra.IsIntegral.of_finite _ _
  let : Finite (maximalIdeal T.Integers).ResidueField := by
    let : Finite (T.Integers ⧸ maximalIdeal T.Integers) := T.finite_residueField
    exact Finite.of_surjective _ (Ideal.bijective_algebraMap_quotient_residueField _).2
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn
    (G := L.Carrier ≃ₐ[K.Carrier] L.Carrier) (maximalIdeal T.Integers) (maximalIdeal S.Integers)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ (maximalIdeal S.Integers)
    (L.Carrier ≃ₐ[K.Carrier] L.Carrier),
    ← LocalFactor.NonabelianSystem.DeligneHenniart.TopLayer.lowerRamificationGroup_zero_eq_inertia]
    at hcard
  rw [lowerGroupOrder, hcard, ← Ideal.ramificationIdx'_eq_ramificationIdx _ _
    (IsDiscreteValuationRing.not_a_field T.Integers)]
  have hmap : Ideal.map (algebraMap T.Integers S.Integers) (maximalIdeal T.Integers) =
      maximalIdeal S.Integers ^ localRamificationFactor K.Carrier L.Carrier :=
    map_maximalIdeal_eq_localRamificationFactor K.Carrier L.Carrier
  apply Ideal.ramificationIdx'_spec hmap.le
  rw [hmap]
  exact (((maximalIdeal S.Integers).pow_right_strictAnti
    (IsDiscreteValuationRing.not_a_field _) (maximalIdeal.isMaximal _).ne_top)
    (Nat.lt_succ_self _)).not_ge

end Relative

section Tower

variable {p : ℕ} [Fact p.Prime] {K : PadicField.{u} p} {E : PadicField.{v} p}
  {M : PadicField.{w} p}
  [Algebra K.Carrier E.Carrier] [Algebra K.Carrier M.Carrier] [Algebra E.Carrier M.Carrier]
  [IsScalarTower K.Carrier E.Carrier M.Carrier]
  [IsScalarTower (Padic p) K.Carrier E.Carrier]
  [IsScalarTower (Padic p) K.Carrier M.Carrier]
  [IsScalarTower (Padic p) E.Carrier M.Carrier]
  [IsGalois K.Carrier M.Carrier] [IsGalois E.Carrier M.Carrier]
  (TK : K.TopologicalData) (TE : E.TopologicalData) (TM : M.TopologicalData)

local notation "restrictToBase" =>
  AlgEquiv.restrictScalarsHom (S := E.Carrier) (A := M.Carrier) K.Carrier

/-- The index of the relative Galois group is the degree of the intermediate field. -/
theorem restrictScalars_range_index : (restrictToBase).range.index = Module.finrank K.Carrier E.Carrier := by
  let : FiniteDimensional K.Carrier E.Carrier :=
    Module.Finite.of_restrictScalars_finite (Padic p) K.Carrier E.Carrier
  let : FiniteDimensional K.Carrier M.Carrier :=
    Module.Finite.of_restrictScalars_finite (Padic p) K.Carrier M.Carrier
  let : FiniteDimensional E.Carrier M.Carrier :=
    Module.Finite.of_restrictScalars_finite (Padic p) E.Carrier M.Carrier
  have hcard : Nat.card (restrictToBase).range = Module.finrank E.Carrier M.Carrier :=
    (Nat.card_congr (MonoidHom.ofInjective (f := restrictToBase)
      (AlgEquiv.restrictScalarsHom_injective K.Carrier)).symm.toEquiv).trans
      (IsGalois.card_aut_eq_finrank E.Carrier M.Carrier)
  apply Nat.eq_of_mul_eq_mul_right (Module.finrank_pos (R := E.Carrier) (M := M.Carrier))
  rw [← hcard, Subgroup.index_mul_card, hcard, IsGalois.card_aut_eq_finrank,
    Module.finrank_mul_finrank]

/-- The residue degree of the intermediate extension is the relative Galois
index scaled by the quotient of the two inertia orders. -/
theorem residueDegree_eq_index_mul_inertia_ratio {f : ℕ}
    (hf : letI := TK.valuativeRel; letI := TE.valuativeRel;
      IsResidueDegree K.Carrier E.Carrier f) :
    (f : ℚ) = ((restrictToBase).range.index : ℚ) * lowerGroupOrder TM E.Carrier 0 /
      lowerGroupOrder TM K.Carrier 0 := by
  let := TK.topology
  let := TK.valuativeRel
  let := TK.localField
  let := TE.topology
  let := TE.valuativeRel
  let := TE.localField
  let := TM.topology
  let := TM.valuativeRel
  let := TM.localField
  let := relativeValuativeExtension TK TE
  let := relativeValuativeExtension TK TM
  let := relativeValuativeExtension TE TM
  let : FiniteDimensional K.Carrier M.Carrier :=
    Module.Finite.of_restrictScalars_finite (Padic p) K.Carrier M.Carrier
  let : FiniteDimensional E.Carrier M.Carrier :=
    Module.Finite.of_restrictScalars_finite (Padic p) E.Carrier M.Carrier
  have hres : localResidueDegree K.Carrier M.Carrier =
      f * localResidueDegree E.Carrier M.Carrier := by
    apply Nat.pow_right_injective (show 1 < Nat.card 𝓀[K.Carrier] from Finite.one_lt_card)
    change Nat.card 𝓀[K.Carrier] ^ _ = Nat.card 𝓀[K.Carrier] ^ _
    rw [← localResidue_card K.Carrier M.Carrier, localResidue_card E.Carrier M.Carrier,
      show Nat.card 𝓀[E.Carrier] = Nat.card 𝓀[K.Carrier] ^ f from hf, pow_mul]
  have hdK := localRamificationFactor_mul_residueDegree K.Carrier M.Carrier
    (relativeContinuous TK TM)
  have hdE := localRamificationFactor_mul_residueDegree E.Carrier M.Carrier
    (relativeContinuous TE TM)
  rw [← lowerGroupOrder_eq_ramificationFactor TK TM, hres,
    ← Module.finrank_mul_finrank K.Carrier E.Carrier M.Carrier,
    ← restrictScalars_range_index (K := K) (E := E) (M := M), ← hdE,
    ← lowerGroupOrder_eq_ramificationFactor TE TM, ← mul_assoc, ← mul_assoc] at hdK
  have hpos : 0 < localResidueDegree E.Carrier M.Carrier := Module.finrank_pos
  have h := Nat.eq_of_mul_eq_mul_right hpos hdK
  apply (eq_div_iff (ne_of_gt (show 0 < (lowerGroupOrder TM K.Carrier 0 : ℚ) by
    exact_mod_cast lowerGroupOrder_pos TM K.Carrier 0))).mpr
  rw [mul_comm (f : ℚ)]
  exact_mod_cast h

/-- The difference of the two finite lower-group order sums is the base
different exponent multiplied by the intermediate inertia order. -/
theorem sum_lowerGroupOrder_sub_eq_different {d N : ℕ}
    (hd : letI := TK.valuativeRel; letI := TE.valuativeRel;
      IsDifferentExponent K.Carrier E.Carrier d)
    (hN : lowerRamificationGroup TM K.Carrier N = ⊥) :
    (∑ i ∈ Finset.range N,
        ((lowerGroupOrder TM K.Carrier i : ℚ) - lowerGroupOrder TM E.Carrier i)) =
      (lowerGroupOrder TM E.Carrier 0 : ℚ) * d := by
  let := TK.topology
  let := TK.valuativeRel
  let := TK.localField
  let := TE.topology
  let := TE.valuativeRel
  let := TE.localField
  let := TM.topology
  let := TM.valuativeRel
  let := TM.localField
  let := relativeValuativeExtension TK TE
  let := relativeValuativeExtension TK TM
  let := relativeValuativeExtension TE TM
  let : CharZero K.Carrier := charZero_of_injective_algebraMap
    ((algebraMap (Padic p) K.Carrier).injective)
  let : FiniteDimensional K.Carrier E.Carrier :=
    Module.Finite.of_restrictScalars_finite (Padic p) K.Carrier E.Carrier
  let : FiniteDimensional K.Carrier M.Carrier :=
    Module.Finite.of_restrictScalars_finite (Padic p) K.Carrier M.Carrier
  let : FiniteDimensional E.Carrier M.Carrier :=
    Module.Finite.of_restrictScalars_finite (Padic p) E.Carrier M.Carrier
  have hN' : lowerRamificationGroup TM E.Carrier N = ⊥ := by
    rw [← lowerRamificationGroup_comap TM K.Carrier E.Carrier, hN, MonoidHom.comap_bot]
    exact (MonoidHom.ker_eq_bot_iff _).mpr (AlgEquiv.restrictScalarsHom_injective K.Carrier)
  have h := hd.differentIdeal_exponents_in_tower
    (relativeContinuous TK TE) (relativeContinuous TK TM) (relativeContinuous TE TM)
    (differentIdeal_eq_maximalIdeal_pow TK TM hN)
    (differentIdeal_eq_maximalIdeal_pow TE TM hN')
  rw [← lowerGroupOrder_eq_ramificationFactor TE TM] at h
  have hr := congrArg (fun n : ℕ => (n : ℚ)) h
  push_cast [Nat.cast_sub (lowerGroupOrder_one_le _ _ _)] at hr
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one] at hr ⊢
  linarith

end Tower

/-- The inertia and different identities for a common finite Galois tower. -/
def FiniteArtinTowerRamificationStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime]
    (K : PadicField.{u} p) (E : PadicField.{v} p) (M : PadicField.{w} p)
    [Algebra K.Carrier E.Carrier] [Algebra K.Carrier M.Carrier] [Algebra E.Carrier M.Carrier]
    [IsScalarTower K.Carrier E.Carrier M.Carrier]
    [IsScalarTower (Padic p) K.Carrier E.Carrier]
    [IsScalarTower (Padic p) K.Carrier M.Carrier]
    [IsScalarTower (Padic p) E.Carrier M.Carrier]
    [IsGalois K.Carrier M.Carrier] [IsGalois E.Carrier M.Carrier],
    ∀ (TK : K.TopologicalData) (TE : E.TopologicalData) (TM : M.TopologicalData),
      letI := TK.valuativeRel
      letI := TE.valuativeRel
      let H := (AlgEquiv.restrictScalarsHom (S := E.Carrier) (A := M.Carrier) K.Carrier).range
      (∀ f : ℕ, IsResidueDegree K.Carrier E.Carrier f →
        (f : ℚ) = (H.index : ℚ) * lowerGroupOrder TM E.Carrier 0 /
          lowerGroupOrder TM K.Carrier 0) ∧
      (∀ d N : ℕ, IsDifferentExponent K.Carrier E.Carrier d →
        lowerRamificationGroup TM K.Carrier N = ⊥ →
        (∑ i ∈ Finset.range N,
          ((lowerGroupOrder TM K.Carrier i : ℚ) - lowerGroupOrder TM E.Carrier i)) =
        (lowerGroupOrder TM E.Carrier 0 : ℚ) * d)

theorem finiteArtinTowerRamification : FiniteArtinTowerRamificationStatement.{u, v, w} := by
  intro p _ K E M _ _ _ _ _ _ _ _ _ TK TE TM
  exact ⟨fun _ hf => residueDegree_eq_index_mul_inertia_ratio TK TE TM hf,
    fun _ _ hd hN => sum_lowerGroupOrder_sub_eq_different TK TE TM hd hN⟩

end Langlands.BaseChange
