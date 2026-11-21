import Langlands.BaseChange.PadicUnramifiedNormFactors
import Langlands.BaseChange.PadicNormPullbackConductor
import Langlands.BaseChange.TraceAdditiveConductor
import Langlands.LocalField.SuppliedPadicNormalization
import Langlands.LocalFactor.Abelian.Laurent
import Langlands.LocalFactor.Abelian.Scaling

/-! # Rank-one Euler factors and epsilon exponents at auxiliary places -/

noncomputable section

open scoped BigOperators
open Polynomial

namespace Langlands.BaseChange

open HarmonicAnalysis LocalClassField ClassFieldTheory.Local
open LocalFactor.PadicAbelian (epsilonExponent lFactor lPolynomial spectralVariable)

universe u v

section NormCharacters

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
  [Algebra F.Carrier E.Carrier] [FiniteDimensional F.Carrier E.Carrier]
  [IsAbelianGalois F.Carrier E.Carrier]

/-- The norm-trivial characters of a finite abelian p-adic extension are
the complex characters of its norm quotient. There are as many as the degree. -/
theorem card_of_mem_iff_isNormTrivial
    (A : Finset (F.Carrierˣ →* ℂˣ)) (hA : ∀ κ, κ ∈ A ↔ IsNormTrivial E.Carrier κ) :
    A.card = Module.finrank F.Carrier E.Carrier := by
  let H := normSubgroup F.Carrier E.Carrier
  have hindex : H.index = Module.finrank F.Carrier E.Carrier :=
    NormUnitImage.normSubgroup_index_eq_finrank F E
  let : H.FiniteIndex := Subgroup.finiteIndex_iff.mpr (hindex.trans_ne Module.finrank_pos.ne')
  let exponent := Monoid.exponent (F.Carrierˣ ⧸ H)
  have hexponent : exponent ≠ 0 := Monoid.exponent_ne_zero_of_finite (G := F.Carrierˣ ⧸ H)
  let : NeZero exponent := ⟨hexponent⟩
  let : HasEnoughRootsOfUnity ℂ exponent :=
    ⟨⟨_, Complex.isPrimitiveRoot_exp exponent hexponent⟩, rootsOfUnity.isCyclic ℂ exponent⟩
  let e : A ≃ (F.Carrierˣ ⧸ H →* ℂˣ) :=
    { toFun := fun κ => QuotientGroup.lift H κ.val (by
        rintro _ ⟨y, rfl⟩
        exact (hA _).mp κ.property y)
      invFun := fun κ => ⟨κ.comp (QuotientGroup.mk' H), (hA _).mpr (fun x => by
        change κ (QuotientGroup.mk (normUnits F.Carrier E.Carrier x)) = 1
        rw [(QuotientGroup.eq_one_iff _).mpr (show normUnits F.Carrier E.Carrier x ∈ H from
          ⟨x, rfl⟩), map_one])⟩
      left_inv := fun κ => Subtype.ext (MonoidHom.ext fun _ => rfl)
      right_inv := fun κ => MonoidHom.ext (fun q => by
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
        rfl) }
  have hcard : Nat.card A = A.card := Nat.card_eq_fintype_card.trans (Fintype.card_coe A)
  rw [← hcard, Nat.card_congr e,
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (F.Carrierˣ ⧸ H) ℂ]
  exact hindex

end NormCharacters

section EulerAndTrace

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} {E : PadicField.{v} p}
  [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
  [FiniteDimensional F.Carrier E.Carrier]
  (T : F.TopologicalData) (S : E.TopologicalData)

private theorem lFactor_eq_inverse_eval {K : PadicField p} (U : K.TopologicalData) :
    letI := U.topology
    ∀ (χ : Quasicharacter K.Carrier) (z : ℂ),
      lFactor U χ z = ((lPolynomial U χ).eval (spectralVariable U z))⁻¹ := by
  let := U.topology
  intro χ z
  by_cases h : U.multiplicativeConductor χ = 0 <;>
    simp [lFactor, LocalFactor.PadicAbelian.lFactorAt, lPolynomial, h]

/-- The rank-one Euler denominator comparison gives equality of the actual
Euler values at the same spectral argument over the two fields. -/
theorem prod_lFactor_unramifiedNormTwists {f : ℕ}
    (hf : letI := T.valuativeRel; letI := S.valuativeRel; IsResidueDegree F.Carrier E.Carrier f) :
    letI := T.topology
    letI := S.topology
    ∀ (χ : Quasicharacter F.Carrier), T.IsUnramifiedCharacter χ.toMonoidHom →
    ∀ (A : Finset (F.Carrierˣ →* ℂˣ)), (∀ κ, κ ∈ A ↔ IsNormTrivial E.Carrier κ) →
    ∀ (ξ : A → Quasicharacter F.Carrier),
      (∀ κ, (ξ κ).toMonoidHom = κ.val * χ.toMonoidHom) →
      ∀ z : ℂ, (∏ κ : A, lFactor T (ξ κ) z) = lFactor S (χ.comp (localNorm T S)) z := by
  let := T.topology
  let := S.topology
  intro χ hχ A hA ξ hξ z
  have hq : S.residueCardinality = T.residueCardinality ^ f := hf
  have hz : spectralVariable S z = spectralVariable T z ^ f := by
    rw [spectralVariable, spectralVariable, hq, Nat.cast_pow, Real.log_pow,
      Complex.ofReal_mul, Complex.ofReal_natCast, ← Complex.exp_nat_mul]
    congr 1
    ring
  have h := congrArg (Polynomial.eval (spectralVariable T z))
    (prod_lPolynomial_unramifiedNormTwists T S hf χ hχ A hA ξ hξ)
  rw [eval_prod, expand_eval, ← hz] at h
  simp_rw [lFactor_eq_inverse_eval]
  rw [Finset.prod_inv_distrib, h]

/-- The relative trace changes additive conductors by the ramification
and different contributions, expressed after multiplication by the residue degree. -/
theorem residueDegree_mul_additiveConductor_of_trace {f d : ℕ}
    (hf : letI := T.valuativeRel; letI := S.valuativeRel; IsResidueDegree F.Carrier E.Carrier f)
    (hd : letI := T.valuativeRel; letI := S.valuativeRel; IsDifferentExponent F.Carrier E.Carrier d) :
    letI := T.topology
    letI := S.topology
    ∀ [IsModuleTopology F.Carrier E.Carrier]
      (ψF : UnitaryAdditiveCharacter F.Carrier) (ψE : UnitaryAdditiveCharacter E.Carrier),
      (∀ x : E.Carrier, ψE x = ψF (Algebra.trace F.Carrier E.Carrier x)) →
        (f : ℤ) * S.additiveConductor ψE =
          (Module.finrank F.Carrier E.Carrier : ℤ) * T.additiveConductor ψF + (f : ℤ) * d := by
  let := T.topology
  let := S.topology
  let := T.valuativeRel
  let := S.valuativeRel
  let := T.localField
  let := S.localField
  intro _ ψF ψE htrace
  let a := T.uniformizerUnit ^ (-T.additiveConductor ψF)
  let b := Units.map (algebraMap F.Carrier E.Carrier : F.Carrier →* E.Carrier) a
  have ha : T.ord (a : F.Carrier) = -T.additiveConductor ψF := by
    change T.ord ((T.uniformizerUnit ^ (-T.additiveConductor ψF) : F.Carrierˣ) : F.Carrier) = _
    rw [Units.val_zpow_eq_zpow_val, T.ord_zpow, T.uniformizerUnit_val, T.ord_uniformizer, mul_one]
  have hab := ord_localNorm_eq_residueDegree_mul T S hf b
  change T.ord (Algebra.norm F.Carrier (algebraMap F.Carrier E.Carrier (a : F.Carrier))) =
    (f : ℤ) * S.ord (b : E.Carrier) at hab
  rw [Algebra.norm_algebraMap, ← zpow_natCast, T.ord_zpow, ha] at hab
  have hzero : T.toLocalFieldData.additiveConductor (ψF.scale a) = 0 := by
    rw [T.toLocalFieldData_additiveConductor, T.additiveConductor_scale, ha, add_neg_cancel]
  have hscaled (x : E.Carrier) : (ψE.scale b) x =
      (ψF.scale a) (Algebra.trace F.Carrier E.Carrier x) := by
    simp only [UnitaryAdditiveCharacter.scale_apply, htrace]
    change ψF (Algebra.trace F.Carrier E.Carrier
      (algebraMap F.Carrier E.Carrier (a : F.Carrier) * x)) =
      ψF ((a : F.Carrier) * Algebra.trace F.Carrier E.Carrier x)
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  have h := IsDifferentExponent.additiveConductor_of_trace hd (ψF.scale a) (ψE.scale b) hzero hscaled
  change S.toLocalFieldData.additiveConductor (ψE.scale b) = _ at h
  rw [S.toLocalFieldData_additiveConductor, S.additiveConductor_scale] at h
  linear_combination (f : ℤ) * h + hab

end EulerAndTrace

/-- At a field extension of an auxiliary finite place, each unramified base
character gives matching rank-one Euler values and matching finite epsilon
exponents after summing the norm-trivial twists. -/
def PadicNormTwistFactorComparisonStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [FiniteDimensional F.Carrier E.Carrier] [IsAbelianGalois F.Carrier E.Carrier]
    (T : F.TopologicalData) (S : E.TopologicalData),
    letI := T.topology
    letI := S.topology
    letI := T.valuativeRel
    letI := S.valuativeRel
    ∀ [IsModuleTopology F.Carrier E.Carrier] (f d : ℕ),
      IsResidueDegree F.Carrier E.Carrier f → IsDifferentExponent F.Carrier E.Carrier d →
      ∀ (ψF : UnitaryAdditiveCharacter F.Carrier) (ψE : UnitaryAdditiveCharacter E.Carrier),
        (∀ x : E.Carrier, ψE x = ψF (Algebra.trace F.Carrier E.Carrier x)) →
      ∀ (χ : Quasicharacter F.Carrier), T.IsUnramifiedCharacter χ.toMonoidHom →
      ∀ (A : Finset (F.Carrierˣ →* ℂˣ)), (∀ κ, κ ∈ A ↔ IsNormTrivial E.Carrier κ) →
        ∃ ξ : A → Quasicharacter F.Carrier,
          (∀ κ, (ξ κ).toMonoidHom = κ.val * χ.toMonoidHom) ∧
          (∀ z : ℂ, (∏ κ : A, lFactor T (ξ κ) z) = lFactor S (χ.comp (localNorm T S)) z) ∧
          (∑ κ : A, epsilonExponent T (ξ κ) ψF) =
            (f : ℤ) * epsilonExponent S (χ.comp (localNorm T S)) ψE

theorem padicNormTwistFactorComparison : PadicNormTwistFactorComparisonStatement.{u, v} := by
  intro p _ F E _ _ _ _ T S
  let := T.topology
  let := S.topology
  let := T.valuativeRel
  let := S.valuativeRel
  let := T.localField
  let := S.localField
  intro _ f d hf hd ψF ψE htrace χ hχ A hA
  obtain ⟨a, ha, hsum⟩ := padicNormPullbackConductor p F E T S χ f d hf hd A hA
  choose ξ hξ hlevel using (fun κ : A => ha κ.val κ.property)
  refine ⟨ξ, hξ, prod_lFactor_unramifiedNormTwists T S hf χ hχ A hA ξ hξ, ?_⟩
  let η := χ.comp (localNorm T S)
  have hav (κ : A) : T.multiplicativeConductor (ξ κ) = a κ.val := by
    have h : T.toLocalFieldData.multiplicativeConductor (ξ κ) = a κ.val := hlevel κ
    simpa only [T.toLocalFieldData_multiplicativeConductor] using h
  have hsumNat : (∑ κ : A, T.multiplicativeConductor (ξ κ)) =
      f * (S.multiplicativeConductor η + d) := by
    calc
      _ = ∑ κ : A, a κ.val := Finset.sum_congr rfl (fun κ _ => hav κ)
      _ = ∑ κ ∈ A, a κ := Finset.sum_coe_sort A a
      _ = _ := hsum.trans (by
        change f * (S.toLocalFieldData.multiplicativeConductor η + d) = _
        rw [S.toLocalFieldData_multiplicativeConductor])
  have hsumInt : (∑ κ : A, (T.multiplicativeConductor (ξ κ) : ℤ)) =
      (f : ℤ) * ((S.multiplicativeConductor η : ℤ) + (d : ℤ)) := by
    exact_mod_cast hsumNat
  have hcard := card_of_mem_iff_isNormTrivial F E A hA
  have hcond := residueDegree_mul_additiveConductor_of_trace T S hf hd ψF ψE htrace
  change (∑ κ : A, epsilonExponent T (ξ κ) ψF) = (f : ℤ) * epsilonExponent S η ψE
  simp only [epsilonExponent, Finset.sum_add_distrib, hsumInt, Finset.sum_const,
    Finset.card_univ, Fintype.card_coe, hcard, nsmul_eq_mul]
  linear_combination -hcond

end Langlands.BaseChange
