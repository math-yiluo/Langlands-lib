import Langlands.Geometry.Building.TorusFiltration.WeilUnitReduction
import Langlands.BruhatTits.IntegralModels.InducedTorusShallowModel
import Mathlib.Algebra.CharP.Lemmas

/-! # Positive-depth reductions of the induced unit models -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.Geometry.Building Langlands.LocalField
open Langlands.LocalGalois.Separable
open scoped NNReal TensorProduct CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4000
set_option quotPrecheck false

namespace Langlands.BruhatTits.IntegralModels.InducedTorusShallow

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local notation "O" => fixedFieldIntegers F
local notation "K" => inertiaFixedField F
local notation "κ" => IsLocalRing.ResidueField O
local notation "Ω" => SeparableClosure F
local notation "ν" => algebraicExtensionAddValuation F Ω
local notation "π" => baseUniformizer F

private local instance integerDVR : IsDiscreteValuationRing O :=
  fixedFieldIntegersIsDVR_of_valuesFromBase F (fixedFieldValuesFromBase F)

private theorem baseUniformizer_mem_maximalIdeal : π ∈ IsLocalRing.maximalIdeal O := by
  apply (Valuation.mem_maximalIdeal_iff _ (fixedFieldValuation F)).mpr
  change sepClosureValuation F ((π : K) : Ω) < 1
  refine lt_of_not_ge fun h => ?_
  have hle := (logAdditiveValuation_le_iff (sepClosureValuation F) (localLogScale F)
    (localLogScale_pos F) ((π : K) : Ω) 1).mpr (by simpa only [map_one] using h)
  change ν ((π : K) : Ω) ≤ ν 1 at hle
  rw [baseUniformizer_value, AddValuation.map_one] at hle
  exact (not_le_of_gt zero_lt_one) hle

section Factors

variable {I : Type u} [Fintype I]
  (E : I → IntermediateField (inertiaFixedField F) (SeparableClosure F))
  [∀ i, FiniteDimensional (inertiaFixedField F) (E i)]

local notation "C" => productIntegers F E
local notation "J" => depthIdeal F E

private abbrev depthPairs (r : ℝ≥0) := WeilCongruence.pairs O (J r)

local notation "D" => depthPairs F E

omit [Fintype I] [∀ i, FiniteDimensional K (E i)] in
private theorem mem_depthIdeal_succ_iff (r : ℝ≥0) (z : C) :
    z ∈ J (r + 1) ↔ ∃ b ∈ J r, algebraMap O C π * b = z := by
  let a (i : I) : E i := algebraMap K (E i) (π : K)
  have hval (i : I) : ν (a i : Ω) = 1 := baseUniformizer_value F
  have ha (i : I) : a i ≠ 0 := by
    intro h
    have hv := hval i
    simp [h] at hv
  have hscale (b : C) (i : I) :
      ν (((algebraMap O C π * b : C) i : E i) : Ω) =
        ν ((b i : E i) : Ω) + 1 := by
    change ν ((a i : Ω) * ((b i : E i) : Ω)) = _
    rw [AddValuation.map_mul, hval, add_comm]
  constructor
  · intro hz
    let b' (i : I) : E i := (z i : E i) / a i
    have hmul (i : I) : a i * b' i = z i := by
      dsimp only [b']
      rw [mul_comm, div_mul_cancel₀ _ (ha i)]
    have hb' (i : I) : ((r : ℝ) : WithTop ℝ) ≤ ν (b' i : Ω) := by
      have he : ν ((z i : E i) : Ω) = 1 + ν (b' i : Ω) := by
        rw [← hmul i]
        change ν ((a i : Ω) * (b' i : Ω)) = _
        rw [AddValuation.map_mul, hval]
      have hi := (mem_depthIdeal F E (r + 1) z).mp hz i
      rw [he] at hi
      exact (WithTop.add_le_add_iff_left (by simp : (1 : WithTop ℝ) ≠ ⊤)).mp
        (by simpa only [NNReal.coe_add, NNReal.coe_one, WithTop.coe_add, WithTop.coe_one,
          add_comm ((r : ℝ) : WithTop ℝ) 1] using hi)
    let b (i : I) : ConnectedImage.integers F (E i) :=
      ⟨b' i, (geometricValue_nonneg_iff F _).mp
        ((show (0 : WithTop ℝ) ≤ ((r : ℝ) : WithTop ℝ) by
          exact_mod_cast (show 0 ≤ r from zero_le)).trans (hb' i))⟩
    refine ⟨b, (mem_depthIdeal F E r b).mpr hb', funext fun i => Subtype.ext (hmul i)⟩
  · rintro ⟨b, hb, rfl⟩
    apply (mem_depthIdeal F E (r + 1) _).mpr
    intro i
    rw [hscale, NNReal.coe_add, NNReal.coe_one, WithTop.coe_add, WithTop.coe_one]
    exact add_le_add_left ((mem_depthIdeal F E r b).mp hb i) 1

omit [Fintype I] [∀ i, FiniteDimensional K (E i)] in
private theorem pair_mem_maximalIdeal_of_second_mem (r : ℝ≥0) (z : D r)
    (h₁ : WeilCongruence.first O (J r) z = 0)
    (h₂ : WeilCongruence.second O (J r) z ∈ J (r + 1)) :
    z ∈ (IsLocalRing.maximalIdeal O).map (algebraMap O (D r)) := by
  obtain ⟨b, hb, he⟩ := (mem_depthIdeal_succ_iff F E r _).mp h₂
  let d : D r := ⟨(0, b), (WeilCongruence.mem_pairs O (J r) _).mpr (by simpa using hb)⟩
  have hd : algebraMap O (D r) π * d = z := by
    apply Subtype.ext
    apply Prod.ext
    · change π * 0 = (z : O × C).1
      rw [mul_zero]
      exact h₁.symm
    · exact he
  rw [← hd]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (baseUniformizer_mem_maximalIdeal F))

omit [Fintype I] [∀ i, FiniteDimensional K (E i)] in
private theorem positiveDepth_pair_pow_nilpotent (r : ℝ≥0) (hr : 0 < r)
    {p : ℕ} (hp : Nat.Prime p) (z : D r) (hz : WeilCongruence.first O (J r) z = 0) :
    ∃ n : ℕ, z ^ (p ^ n) ∈ (IsLocalRing.maximalIdeal O).map (algebraMap O (D r)) := by
  have hr' : 0 < (r : ℝ) := by exact_mod_cast hr
  have hp' : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (((r : ℝ) + 1) / (r : ℝ)) hp'
  refine ⟨n, pair_mem_maximalIdeal_of_second_mem F E r _ ?_ ?_⟩
  · rw [map_pow, hz, zero_pow (pow_ne_zero _ hp.ne_zero)]
  · have hb := (WeilCongruence.mem_pairs O (J r) (z : O × C)).mp z.property
    change (z : O × C).1 = 0 at hz
    rw [hz, map_zero, sub_zero] at hb
    rw [map_pow, mem_depthIdeal]
    intro i
    change ((↑(r + 1) : ℝ) : WithTop ℝ) ≤ ν ((((z : O × C).2 i : E i) : Ω) ^ (p ^ n))
    rw [AddValuation.map_pow]
    have hl : ((↑(r + 1) : ℝ) : WithTop ℝ) ≤ (p ^ n) • (((r : ℝ) : WithTop ℝ)) := by
      rw [← WithTop.coe_nsmul, WithTop.coe_le_coe, nsmul_eq_mul, Nat.cast_pow,
        NNReal.coe_add, NNReal.coe_one]
      exact ((div_lt_iff₀ hr').mp hn).le
    exact hl.trans (nsmul_le_nsmul_right ((mem_depthIdeal F E r _).mp hb i) _)

/-- At strictly positive shallow depth the residue of each integral section
of the factor model is killed by a power of the residue characteristic. -/
theorem modelOfFactors_reduction_pPower (r : ℝ≥0) (hr : 0 < r) (hr₁ : r < 1)
    {p : ℕ} [Fact p.Prime] [CharP κ p]
    (x : (modelOfFactors F E r hr₁).integralSections) :
    ∃ n : ℕ, ((modelOfFactors F E r hr₁).reduction x) ^ (p ^ n) = 1 := by
  change rationalPoints (WeilCongruence.group O (J r)) at x
  let w := WeilCongruence.sectionUnit O (J r) x
  have hw : WeilCongruence.first O (J r) ((w : D r) - 1) = 0 := by
    rw [map_sub, map_one, WeilCongruence.first_sectionUnit, sub_self]
  obtain ⟨n, hn⟩ := positiveDepth_pair_pow_nilpotent F E r hr (Fact.out : Nat.Prime p) _ hw
  let T := κ ⊗[O] (D r)
  let a : T →+* κ := (Algebra.TensorProduct.rid O κ κ).toRingHom.comp
    (Algebra.TensorProduct.map (AlgHom.id O κ) (WeilCongruence.first O (J r))).toRingHom
  let : Nontrivial T := a.domain_nontrivial
  let : CharP T p := CharP.of_ringHom_of_ne_zero (algebraMap κ T) p
    (Fact.out : Nat.Prime p).ne_zero
  let t : D r →ₐ[O] T := Algebra.TensorProduct.includeRight
  have ht (b : D r) : t b = 0 ↔ b ∈ (IsLocalRing.maximalIdeal O).map (algebraMap O (D r)) := by
    change (1 : κ) ⊗ₜ[O] b = 0 ↔ _
    rw [Langlands.Algebra.IdealTensorRelation.one_tmul_eq_zero_iff, Ideal.smul_top_eq_map]
    rfl
  have hpow := (ht _).mpr hn
  refine ⟨n, ?_⟩
  rw [← map_pow]
  change baseChangeSectionHom (IntegralModel.residueBaseMap O) _ (x ^ (p ^ n)) = 1
  apply (WeilCongruence.reduction_eq_one_iff O (J r) _).mpr
  change (WeilCongruence.sectionUnit O (J r) (x ^ (p ^ n)) : D r) - 1 ∈ _
  suffices hpw : WeilCongruence.sectionUnit O (J r) (x ^ (p ^ n)) = w ^ (p ^ n) by
    rw [hpw, Units.val_pow_eq_pow_val]
    apply (ht _).mp
    rw [map_sub, map_pow, map_one]
    simpa only [map_pow, map_sub, map_one,
      sub_pow_char_pow (t (w : D r)) 1 n (p := p), one_pow] using hpow
  unfold WeilCongruence.sectionUnit
  rw [map_pow, map_pow]
  rfl

end Factors

set_option maxHeartbeats 3600000 in
/-- An induced torus admits a smooth model of its shallow geometric-character
subgroup whose special-fibre sections are killed by powers of the residue
characteristic. -/
theorem exists_model_reduction_pPower
    (R : CommGroupScheme (Spec (CommRingCat.of K)))
    (r : ℝ≥0) (hR : IsInducedTorus R) (hr : 0 < r) (hr₁ : r < 1)
    {p : ℕ} [Fact p.Prime] [CharP κ p] :
    ∃ M : IntegralModel O K R.toGrp, M.IsSmooth ∧
      M.integralPoints = localGeometricCharacterCongruence F R r ∧
      ∀ x : M.integralSections, ∃ n : ℕ, (M.reduction x) ^ (p ^ n) = 1 := by
  classical
  let S := localTorusSplittingData F R hR.isTorus
  obtain ⟨n, E, ⟨e⟩⟩ := inducedTorusWeilDecomposition K S.L R S.splits hR
  let I := ULift.{u} (Fin n)
  let q : I ≃ Fin n := Equiv.ulift
  let LtoOmega := IsScalarTower.toAlgHom K S.L Ω
  let fields (i : I) := (E (q i)).map LtoOmega
  let j (i : I) : E (q i) ≃ₐ[K] fields i := (E (q i)).equivMap LtoOmega
  let : ∀ i, Algebra K (E (q i)) := fun i => (E (q i)).toSubalgebra.algebra
  let : ∀ i, Module K (E (q i)) := fun i =>
    @Algebra.toModule _ _ _ _ (E (q i)).toSubalgebra.algebra
  let : ∀ i, SMul K (E (q i)) := fun i => (E (q i)).toSubalgebra.algebra.toSMul
  let : ∀ i, Algebra K (fields i) := fun i => (fields i).toSubalgebra.algebra
  let : ∀ i, Module K (fields i) := fun i => @Algebra.toModule _ _ _ _ (fields i).toSubalgebra.algebra
  let : ∀ i, SMul K (fields i) := fun i => (fields i).toSubalgebra.algebra.toSMul
  let A₀ : Algebra K (∀ i : Fin n, E i) := Pi.algebra _ _
  let A₁ : Algebra K (∀ i : I, E (q i)) := Pi.algebra _ _
  let A₂ : Algebra K (∀ i : I, fields i) := Pi.algebra _ _
  let : Module K (∀ i : Fin n, E i) := @Algebra.toModule _ _ _ _ A₀
  let : Module K (∀ i : I, E (q i)) := @Algebra.toModule _ _ _ _ A₁
  let : Module K (∀ i : I, fields i) := @Algebra.toModule _ _ _ _ A₂
  let : SMul K (∀ i : Fin n, E i) := A₀.toSMul
  let : SMul K (∀ i : I, E (q i)) := A₁.toSMul
  let : SMul K (∀ i : I, fields i) := A₂.toSMul
  let : ∀ i, FiniteDimensional K (E i) := fun i => IntermediateField.finiteDimensional_left (E i)
  let : ∀ i, FiniteDimensional K (fields i) := fun i => Module.Finite.equiv (j i).toLinearEquiv
  let : Module.Finite K (∀ i : Fin n, E i) := Module.Finite.pi
  let : Module.Finite K (∀ i : I, fields i) := Module.Finite.pi
  let : Module.Projective K (∀ i : Fin n, E i) :=
    Module.Projective.of_basis (Module.Basis.ofVectorSpace K _)
  let : Module.Projective K (∀ i : I, fields i) :=
    Module.Projective.of_basis (Module.Basis.ofVectorSpace K _)
  let reindex : (∀ i : Fin n, E i) ≃ₐ[K] (∀ i : I, E (q i)) :=
    (AlgEquiv.piCongrLeft K (fun i : Fin n => E i) q).symm
  let eB := reindex.trans (AlgEquiv.piCongrRight j)
  let W := WeilGm.commGroupScheme (CommRingCat.of K) (∀ i : I, fields i)
  let eW : R ≅ W := e ≪≫ WeilGm.commCongrIso eB
  let d : W.toGrp ≅ R.toGrp :=
    { hom := CommGroupScheme.groupHom eW.inv
      inv := CommGroupScheme.groupHom eW.hom
      hom_inv_id := congrArg CommGroupScheme.groupHom eW.inv_hom_id
      inv_hom_id := congrArg CommGroupScheme.groupHom eW.hom_inv_id }
  let N := modelOfFactors F fields r hr₁
  have hPow : ∀ x : N.integralSections, ∃ m : ℕ, (N.reduction x) ^ (p ^ m) = 1 :=
    @modelOfFactors_reduction_pPower F _ _ _ _ I _ fields _ r hr hr₁ p _ _
  let M : IntegralModel O K R.toGrp := { N with genericIso := N.genericIso ≪≫ d }
  let hM : N.Iso M d :=
    { iso := CategoryTheory.Iso.refl _
      generic_comm := by simp [M] }
  refine ⟨M, modelOfFactors_smooth F fields r hr₁, ?_, ?_⟩
  · rw [← hM.map_integralPoints, modelOfFactors_integralPoints F fields r hr hr₁]
    apply le_antisymm (map_extendedCharacterCongruence_le K Ω ν W.toGrp d.hom r)
    intro x hx
    have h := map_extendedCharacterCongruence_le K Ω ν R.toGrp d.inv r ⟨x, hx, rfl⟩
    refine ⟨rationalPoints.map d.inv x, h, ?_⟩
    simp only [rationalPoints.map_apply, Category.assoc, ← Grp.comp_hom_hom,
      d.inv_hom_id, Grp.id_hom_hom, Category.comp_id]
  · change ∀ x : N.integralSections, ∃ m : ℕ, (N.reduction x) ^ (p ^ m) = 1
    exact hPow

end Langlands.BruhatTits.IntegralModels.InducedTorusShallow
