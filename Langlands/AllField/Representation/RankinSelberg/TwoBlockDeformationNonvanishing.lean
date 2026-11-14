import Langlands.Representation.RankinSelberg.TwoBlockDeformationNonvanishing
import Langlands.AllField.Group.GL.BlockIwahoriBasis
import Langlands.AllField.Group.GL.BlockIwahoriDefinitionsSupplement
import Langlands.AllField.Representation.RankinSelberg.TwoBlockJacquetData
import Langlands.AllField.Representation.RankinSelberg.TwoBlockWhittakerDeformationStatement
/-!
# A section of the two-block induction with nonzero Jacquet value at the identity

Let `σ_1, σ_2` be smooth representations of `GL_(m_1+1)(F)` and `GL_(m_2+1)(F)` and
let `ℓ_1, ℓ_2` be nonzero linear functionals on their spaces. This module constructs a
section `f` of the actual lower induction `I(σ_1 ⊗ σ_2)` such that `x ↦ f(u(x))` has
compact support on the upper radical and the Jacquet integral
`J(f)(1) = ∫ ⟨f(u(x)), ℓ_1 ⊗ ℓ_2⟩ ψ(x_(m_1,0)) dx` of JPSS (4.6.2) is nonzero.

The section is supported on `Q̄ K`, for a compact open subgroup `K` with a block Iwahori
factorization `K = (K ∩ Ū)(K ∩ M)(K ∩ U)`, with value `v_1 ⊗ v_2` at the identity, where
`ℓ_i(v_i) ≠ 0`. Since `Q̄ ∩ U = 1`, its restriction to the upper radical is
`u(x) ↦ (v_1 ⊗ v_2) 1[u(x) ∈ K]`, so `J(f)(1) = ℓ_1(v_1) ℓ_2(v_2) μ{x : u(x) ∈ K}`.
-/

noncomputable section

open MeasureTheory Topology

namespace Langlands.AllField.RankinSelberg.TwoBlockDeformation
open Langlands.RankinSelberg.TwoBlockDeformation hiding character_eq_one_mem_nhds exists_deformed_section_jacquetFunction_one_ne_zero exists_section_jacquetFunction_one_ne_zero isSmooth_twoBlockDeformedBlocks
open Langlands.AllField.RankinSelberg.TwoBlockDeformation
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.RankinSelberg.TwoBlockJacquet hiding IsAbsIntegrable IsAbsIntegrableAt Sections inducedRep integrand integrand_add integrand_apply integrand_def integrand_inducedRep integrand_smul jacquetFunction jacquetFunction_add jacquetFunction_apply jacquetFunction_def jacquetFunction_inducedRep jacquetFunction_smul scalarSection scalarSection_add scalarSection_covariant scalarSection_def scalarSection_inducedRep scalarSection_one scalarSection_smul sectionEval sectionEval_add sectionEval_smul sectionEval_zero
open Langlands.AllField.RankinSelberg.TwoBlockJacquet

universe uF uW uR

section Character

variable (F : Type uF) [Field F]

/-- A unitary additive character of a p-adic field is trivial near `0`. -/
theorem character_eq_one_mem_nhds [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F) :
    {y : F | ψ.complex y = 1} ∈ 𝓝 (0 : F) := by
  have harc : (1 : Circle) ∈ Circle.centeredArc (Real.pi / 2) := by
    rw [Circle.mem_centeredArc (by linarith [Real.pi_pos])]
    simp [Real.pi_pos]
  have hU : ψ.toAddChar ⁻¹' Circle.centeredArc (Real.pi / 2) ∈ 𝓝 (0 : F) :=
    ψ.continuous_toFun.continuousAt.preimage_mem_nhds
      ((Circle.isOpen_centeredArc _).mem_nhds (by simpa using harc))
  obtain ⟨S, hS, hSU⟩ :=
    (IsLinearTopology.hasBasis_open_submodule
      (ValuativeRel.valuation F).integer (M := F)).mem_iff.mp hU
  filter_upwards [hS.mem_nhds S.zero_mem] with y hy
  have he : ψ.toAddChar y = 1 := by
    apply Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two
    intro n _
    have hn := hSU (S.toAddSubgroup.nsmul_mem hy n)
    change ψ.toAddChar (n • y) ∈ Circle.centeredArc (Real.pi / 2) at hn
    rwa [AddChar.map_nsmul_eq_pow] at hn
  change ((ψ.toAddChar y : Circle) : ℂ) = 1
  rw [he, Circle.coe_one]

end Character

section Blocks


end Blocks

section Radical


end Radical

section Nonvanishing

variable (F : Type uF) [Field F]
variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

/-- For smooth blocks and nonzero functionals `ℓ_i`, some section of the actual lower
induction has compactly supported restriction to the upper radical and nonzero
Jacquet value `J(f)(1)`, for every Borel additive Haar measure on the rectangular
coordinates. -/
theorem exists_section_jacquetFunction_one_ne_zero [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    (ψ : UnitaryAdditiveCharacter F)
    (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
    (hσ : ∀ i, IsSmooth (σ i))
    (ell : ∀ i, W i →ₗ[ℂ] ℂ) (hell : ∀ i, ell i ≠ 0) :
    ∀ [BorelSpace (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F)]
      (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F)) [μ.IsAddHaarMeasure],
      ∃ f : Sections F h σ,
        HasCompactSupport (fun x => sectionEval F h σ f (upperRadical h F x)) ∧
          jacquetFunction ψ ell μ f 1 ≠ 0 := by
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup (t + 1)
  intro _ μ _
  let B := succBlockShape m h
  let P := B.oppositeParabolic F
  let τ := twist (T.oppositeParabolicHalfModulus B)
    ((B.blockTensor σ).comp (B.oppositeLeviProjection F))
  -- Vectors `v_i` with `ℓ_i(v_i) ≠ 0` and open stabilizers `H_i`.
  have hex : ∀ i, ∃ v : W i, ell i v ≠ 0 := by
    intro i
    by_contra hne
    exact hell i (LinearMap.ext fun w => not_not.mp (not_exists.mp hne w))
  choose v hv using hex
  choose H hH using fun i => hσ i (v i)
  -- An open set of `Q̄` on which the inducing data fixes `v_1 ⊗ v_2`.
  let S : Set (B.Levi F) :=
    Set.univ.pi fun i => ((H i : Set (GeneralLinear (m i + 1) F)))
  have hS : IsOpen S := isOpen_set_pi Set.finite_univ fun i _ => (H i).isOpen
  let OP : Set P := (B.oppositeLeviProjection F) ⁻¹' S ∩
    ((T.oppositeParabolicHalfModulus B).ker : Set P)
  have hOP : IsOpen OP :=
    (hS.preimage (T.oppositeBlockLeviProjection B).continuous).inter
      (T.isOpen_ker_oppositeParabolicHalfModulus B)
  obtain ⟨O, hO, hOeq⟩ := isOpen_induced_iff.mp hOP
  have h1O : (1 : GeneralLinear (t + 1) F) ∈ O := by
    have h1 : (1 : P) ∈ OP := by
      refine ⟨?_, (T.oppositeParabolicHalfModulus B).ker.one_mem⟩
      intro i _
      rw [map_one]
      exact (H i).one_mem
    rw [← hOeq] at h1
    exact h1
  -- The corner entry `x_(m_1, 0)` has `ψ = 1` near the identity.
  have hcont : Continuous fun g : GeneralLinear (t + 1) F =>
      g (B.index 0 (Fin.last (m 0))) (B.index 1 0) :=
    (continuous_apply (B.index 1 0)).comp
      (Matrix.GeneralLinearGroup.continuous_apply _ continuous_id (B.index 0 (Fin.last (m 0))))
  have h10 : (1 : GeneralLinear (t + 1) F) (B.index 0 (Fin.last (m 0))) (B.index 1 0)
      = 0 := by
    have he := upperRadical_index_zero_one h F 0 (Fin.last (m 0)) 0
    rwa [upperRadical_zero] at he
  have hcorner : {g : GeneralLinear (t + 1) F |
      ψ.complex (g (B.index 0 (Fin.last (m 0))) (B.index 1 0)) = 1} ∈
        𝓝 (1 : GeneralLinear (t + 1) F) := by
    have hmem : {y : F | ψ.complex y = 1} ∈
        𝓝 ((1 : GeneralLinear (t + 1) F) (B.index 0 (Fin.last (m 0))) (B.index 1 0)) := by
      rw [h10]
      exact character_eq_one_mem_nhds F ψ
    exact hcont.continuousAt.preimage_mem_nhds hmem
  -- A compact open subgroup with Iwahori factorization inside both neighborhoods.
  obtain ⟨K, hKc, hKU, hKI⟩ :=
    (Langlands.AllField.GeneralLinear.BlockShape.exists_compactOpenSubgroup_hasBlockIwahoriFactorization B) T
      (Filter.inter_mem (hO.mem_nhds h1O) hcorner)
  have hw : PiTensorProduct.tprod ℂ v ∈
      fixedVectors τ (Induction.conjOpenSubgroup P K 1).toSubgroup := by
    intro q
    have hqK : ((q : P) : GeneralLinear (t + 1) F) ∈ K := by
      simpa using Induction.mem_conjOpenSubgroup.mp q.property
    have hqO : (q : P) ∈ OP := by
      rw [← hOeq]
      exact (hKU hqK).1
    obtain ⟨hqS, hqker⟩ := hqO
    change ((T.oppositeParabolicHalfModulus B (q : P) : ℂˣ) : ℂ) •
      B.blockTensor σ (B.oppositeLeviProjection F (q : P))
        (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ v
    rw [MonoidHom.mem_ker.mp hqker, Units.val_one, one_smul, BlockShape.blockTensor_tprod]
    congr 1
    funext i
    exact hH i ⟨_, hqS i (Set.mem_univ i)⟩
  let s := Induction.compactDoubleCosetSection P τ K hKc 1 (PiTensorProduct.tprod ℂ v) hw
  let f : Sections F h σ := s.val
  -- The restriction of `f` to the upper radical.
  have hval_mem : ∀ y ∈ K, sectionEval F h σ f y = PiTensorProduct.tprod ℂ v := by
    intro y hy
    have he := Induction.compactDoubleCosetSection_apply P τ K hKc 1
      (PiTensorProduct.tprod ℂ v) hw 1 ⟨y, hy⟩
    simp only [OneMemClass.coe_one, one_mul, map_one, Module.End.one_apply] at he
    exact he
  have hval_not : ∀ x, upperRadical h F x ∉ K →
      sectionEval F h σ f (upperRadical h F x) = 0 := by
    intro x hx
    by_contra hne
    obtain ⟨l, hl, he⟩ := Induction.compactDoubleCosetSection_support_subset P τ K hKc 1
      (PiTensorProduct.tprod ℂ v) hw ⟨_, hne, rfl⟩
    have hp : upperRadical h F x * (1 * l)⁻¹ ∈ P :=
      QuotientGroup.rightRel_apply.mp (Quotient.exact he)
    rw [one_mul] at hp
    exact hx (mem_of_mem_unipotentSubgroup_of_mul_inv_mem B F K.toSubgroup
      hKI.1.2 (upperRadical_mem_unipotentSubgroup h F x) hl hp)
  have hker : ∀ x, upperRadical h F x ∈ K → ψ.complex (x (Fin.last (m 0)) 0) = 1 := by
    intro x hx
    have he := (hKU hx).2
    simp only [Set.mem_ofPred_eq] at he
    rwa [upperRadical_index_zero_one] at he
  -- The level set `L = {x : u(x) ∈ K}`.
  let L : Set (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F) :=
    {x | upperRadical h F x ∈ K}
  have hLopen : IsOpen L := K.isOpen.preimage (continuous_upperRadical h F)
  have hLclosed : IsClosed L := K.isClosed.preimage (continuous_upperRadical h F)
  have hLcompact : IsCompact L := by
    let E : GeneralLinear (t + 1) F →
        Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F :=
      fun g => Matrix.of fun i j => g (B.index 0 i) (B.index 1 j)
    have hE : Continuous E := continuous_matrix fun i j =>
      (continuous_apply (B.index 1 j)).comp
        (Matrix.GeneralLinearGroup.continuous_apply _ continuous_id (B.index 0 i))
    refine (hKc.image hE).of_isClosed_subset hLclosed ?_
    intro x hx
    refine ⟨_, hx, ?_⟩
    ext i j
    exact upperRadical_index_zero_one h F x i j
  have h0L : (0 : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F) ∈ L := by
    change upperRadical h F 0 ∈ K
    rw [upperRadical_zero]
    exact K.one_mem
  have hint : integrand ψ ell f 1 = L.indicator (fun _ => ∏ i, ell i (v i)) := by
    funext x
    rw [integrand_apply, mul_one]
    by_cases hx : upperRadical h F x ∈ K
    · rw [Set.indicator_of_mem (show x ∈ L from hx), hval_mem _ hx, tensorContraction_tprod,
        hker x hx, mul_one]
    · rw [Set.indicator_of_notMem (show x ∉ L from hx), hval_not x hx, map_zero, zero_mul]
  refine ⟨f, HasCompactSupport.intro' hLcompact hLclosed fun x hx => hval_not x hx, ?_⟩
  rw [jacquetFunction_def, hint, integral_indicator_const _ hLopen.measurableSet]
  have hpos : μ L ≠ 0 := (hLopen.measure_pos μ ⟨0, h0L⟩).ne'
  have hfin : μ L ≠ ⊤ := hLcompact.measure_lt_top.ne
  refine smul_ne_zero ?_ (Finset.prod_ne_zero_iff.mpr fun i _ => hv i)
  rw [measureReal_def]
  exact ENNReal.toReal_ne_zero.mpr ⟨hpos, hfin⟩

/-- The deformed blocks `σ_u` of blocks of full standard Whittaker type are smooth. -/
theorem isSmooth_twoBlockDeformedBlocks [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
    (hσ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i)) (u : ℂ) :
    ∀ i, IsSmooth (twoBlockDeformedBlocks F m σ u i) := by
  intro i
  exact (isSmooth_twist_iff _ _
    ((⟨⟩ : LocalFieldData F).isOpen_ker_determinantComplexPower _ _)).mpr (hσ i).1.1

/-- For blocks of full standard Whittaker type, every deformation `ρ_u` has a section
with compactly supported restriction to the upper radical and nonzero Jacquet value at
the identity, for any nonzero functionals `ℓ_i` on the block spaces. -/
theorem exists_deformed_section_jacquetFunction_one_ne_zero [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    (ψ : UnitaryAdditiveCharacter F)
    (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
    (hσ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i))
    (ell : ∀ i, W i →ₗ[ℂ] ℂ) (hell : ∀ i, ell i ≠ 0) (u : ℂ) :
    ∀ [BorelSpace (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F)]
      (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F)) [μ.IsAddHaarMeasure],
      ∃ f : Sections F h (twoBlockDeformedBlocks F m σ u),
        HasCompactSupport (fun x => sectionEval F h (twoBlockDeformedBlocks F m σ u) f
          (upperRadical h F x)) ∧
          jacquetFunction ψ ell μ f 1 ≠ 0 :=
  exists_section_jacquetFunction_one_ne_zero F h ψ (twoBlockDeformedBlocks F m σ u)
    (isSmooth_twoBlockDeformedBlocks F ψ σ hσ u) ell hell

end Nonvanishing

end Langlands.AllField.RankinSelberg.TwoBlockDeformation
