import Langlands.Representation.RankinSelberg.AdjacentRankJacquetCovariance
import Langlands.Representation.Induction.CompactLocalSection
import Langlands.Group.GL.OppositeBlockIntersection
import Langlands.Group.GL.BlockIwahoriBasis
import Langlands.Representation.Tensor.Finite
import Langlands.Representation.Smooth.Transfer.PullbackProof
import Langlands.Representation.Twist.SmoothProof

/-! Nonvanishing of the actual adjacent Jacquet functional by a compact local section. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Topology Matrix

namespace Langlands.RankinSelberg.AdjacentJacquet

open GeneralLinear HarmonicAnalysis Whittaker

universe uF uV

section Algebra

variable {K : Type uF} [Field K] {r : ℕ}

private theorem castAdd_one_eq_castSucc {n : ℕ} (i : Fin n) :
    Fin.castAdd 1 i = i.castSucc := Fin.ext rfl

private theorem natAdd_zero_eq_last (n : ℕ) :
    Fin.natAdd n (0 : Fin 1) = Fin.last n := Fin.ext (Nat.add_zero n)

/-- Last-column extraction in the exact ambient rank. -/
def columnCoordinate (g : GeneralLinear (r + 2) K) : Fin (r + 1) → K :=
  fun i => g i.castSucc (Fin.last (r + 1))

@[simp] theorem columnCoordinate_upperColumn (x : Fin (r + 1) → K) :
    columnCoordinate (upperColumn x) = x := by
  funext i
  exact upperColumn_castSucc_last x i

@[simp] theorem upperColumn_zero :
    upperColumn (0 : Fin (r + 1) → K) = 1 := by
  apply Units.ext
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;>
    refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp [Matrix.one_apply, Ne.symm (Fin.castSucc_ne_last _)]

/-- The literal upper columns constitute the upper radical of the lower shape. -/
theorem upperColumn_mem_radical (x : Fin (r + 1) → K) :
    upperColumn x ∈ (adjacentRankLowerShape r).unipotentSubgroup K := by
  rw [BlockShape.mem_unipotentSubgroup_iff, BlockShape.mem_parabolic_iff]
  constructor
  · intro i j a b hji
    fin_cases i <;> fin_cases j
    · exact False.elim (lt_irrefl _ hji)
    · exact False.elim (by exact (by decide : ¬ (1 : Fin 2) < 0) hji)
    · change upperColumn x ((adjacentRankLowerShape r).index 1 a)
        ((adjacentRankLowerShape r).index 0 b) = 0
      change Fin 1 at a
      change Fin (r + 1) at b
      simp only [adjacentRankLowerShape,
        Shahidi.twoBlocks_index_first (Nat.succ_pos r) (Nat.succ_pos 0),
        Shahidi.twoBlocks_index_second (Nat.succ_pos r) (Nat.succ_pos 0),
        castAdd_one_eq_castSucc]
      simpa only [Subsingleton.elim a (0 : Fin 1), natAdd_zero_eq_last]
        using upperColumn_last_castSucc x b
    · exact False.elim (lt_irrefl _ hji)
  · intro i a b
    fin_cases i
    · change upperColumn x ((adjacentRankLowerShape r).index 0 a)
        ((adjacentRankLowerShape r).index 0 b) = _
      change Fin (r + 1) at a b
      simp only [adjacentRankLowerShape,
        Shahidi.twoBlocks_index_first (Nat.succ_pos r) (Nat.succ_pos 0),
        castAdd_one_eq_castSucc]
      exact upperColumn_castSucc_castSucc x a b
    · change upperColumn x ((adjacentRankLowerShape r).index 1 a)
        ((adjacentRankLowerShape r).index 1 b) = _
      change Fin 1 at a b
      simp only [adjacentRankLowerShape,
        Shahidi.twoBlocks_index_second (Nat.succ_pos r) (Nat.succ_pos 0)]
      simp [Subsingleton.elim a (0 : Fin 1), Subsingleton.elim b (0 : Fin 1),
        natAdd_zero_eq_last]

/-- A radical element is exactly the upper column given by its entries. -/
theorem eq_upperColumn_of_mem_radical {g : GeneralLinear (r + 2) K}
    (hg : g ∈ (adjacentRankLowerShape r).unipotentSubgroup K) :
    g = upperColumn (columnCoordinate g) := by
  rw [BlockShape.mem_unipotentSubgroup_iff, BlockShape.mem_parabolic_iff] at hg
  obtain ⟨hp, hd⟩ := hg
  have h00 (a b : Fin (r + 1)) : g a.castSucc b.castSucc = if a = b then 1 else 0 := by
    have h := hd (0 : Fin 2) a b
    change g ((adjacentRankLowerShape r).index 0 a)
      ((adjacentRankLowerShape r).index 0 b) = if a = b then 1 else 0 at h
    simpa only [adjacentRankLowerShape,
      Shahidi.twoBlocks_index_first (Nat.succ_pos r) (Nat.succ_pos 0),
      castAdd_one_eq_castSucc]
      using h
  have h10 (b : Fin (r + 1)) : g (Fin.last (r + 1)) b.castSucc = 0 := by
    have h := hp (1 : Fin 2) (0 : Fin 2) (0 : Fin 1) b (by decide : (0 : Fin 2) < 1)
    change g ((adjacentRankLowerShape r).index 1 (0 : Fin 1))
      ((adjacentRankLowerShape r).index 0 b) = _ at h
    simpa only [adjacentRankLowerShape,
      Shahidi.twoBlocks_index_first (Nat.succ_pos r) (Nat.succ_pos 0),
      Shahidi.twoBlocks_index_second (Nat.succ_pos r) (Nat.succ_pos 0),
      castAdd_one_eq_castSucc, natAdd_zero_eq_last]
      using h
  have h11 : g (Fin.last (r + 1)) (Fin.last (r + 1)) = 1 := by
    have h := hd (1 : Fin 2) (0 : Fin 1) (0 : Fin 1)
    change g ((adjacentRankLowerShape r).index 1 (0 : Fin 1))
      ((adjacentRankLowerShape r).index 1 (0 : Fin 1)) = _ at h
    simpa only [adjacentRankLowerShape,
      Shahidi.twoBlocks_index_second (Nat.succ_pos r) (Nat.succ_pos 0),
      natAdd_zero_eq_last, ite_true]
      using h
  apply Units.ext
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;>
    refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp [h00, h10, h11, columnCoordinate]

variable [TopologicalSpace K]

theorem continuous_columnCoordinate :
    Continuous (columnCoordinate (K := K) (r := r)) :=
  continuous_pi fun _ => (GeneralLinear.entry _ _).continuous

variable [IsTopologicalRing K]

theorem continuous_upperColumn :
    Continuous (upperColumn (K := K) (r := r)) :=
  (Shahidi.continuous_upper (r + 1) 1 K).comp
    (continuous_pi fun _ => continuous_pi fun _ => continuous_apply _)

end Algebra

section Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance jacquetNonzeroTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance jacquetNonzeroValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance jacquetNonzeroLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance jacquetNonzeroT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance jacquetNonzeroSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance jacquetNonzeroSigmaCompact : SigmaCompactSpace F.Carrier :=
  F.canonicalTopologicalData.sigmaCompactSpace
local instance jacquetNonzeroNonarchRing : NonarchimedeanRing F.Carrier := by
  convert! ValuativeRel.nonarchimedeanRing F.Carrier
  exact Valuation.toTopologicalSpace_eq _
local instance jacquetNonzeroMeasurable : MeasurableSpace F.Carrier := borel _
local instance jacquetNonzeroBorel : BorelSpace F.Carrier := ⟨rfl⟩

variable (ψ : UnitaryAdditiveCharacter F.Carrier) {r : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
  (ℓ : glFunctionals ψ r σ) (χ : Quasicharacter F.Carrier)

include ψ in
/-- The exact normalized tensor-valued inducing action is smooth. -/
theorem inducing_isSmooth (hσ : IsSmooth σ) :
    IsSmooth (Padic.adjacentRankLowerTensorRepresentation F σ χ) := by
  have hf : ∀ i : Fin 2,
      IsSmooth (Shahidi.pairFamily σ (rankOneExtensionCharacter.{uF, uV} F χ) i) := by
    intro i
    fin_cases i
    · exact hσ
    · exact rankOneExtensionCharacter_isSmooth F ψ χ
  exact (isSmooth_twist_iff _ _
    (F.canonicalTopologicalData.isOpen_ker_oppositeParabolicHalfModulus
      (adjacentRankLowerShape r))).2
    (isSmooth_comp _ (F.canonicalTopologicalData.oppositeBlockLeviProjection
      (adjacentRankLowerShape r)).continuous (FiniteTensor.isSmooth_external _ hf))

/-- The negative Jacquet phase is trivial on an open neighborhood of zero. -/
theorem phase_eq_one_neighborhood :
    ∃ O : Set (Fin (r + 1) → F.Carrier), IsOpen O ∧ 0 ∈ O ∧
      ∀ x ∈ O, ψ.complex (-x (Fin.last r)) = 1 := by
  have : NonarchimedeanGroup (Multiplicative F.Carrier) :=
    { is_nonarchimedean := by
        intro U hU
        obtain ⟨H, hH⟩ := NonarchimedeanAddGroup.is_nonarchimedean
          (Multiplicative.ofAdd ⁻¹' U) hU
        exact ⟨{
          toSubgroup := {
            carrier := {x | x.toAdd ∈ H}
            one_mem' := H.zero_mem
            mul_mem' := H.add_mem
            inv_mem' := H.neg_mem
          }
          isOpen' := H.isOpen
        }, hH⟩ }
  let θ : Multiplicative F.Carrier →* ℂˣ :=
    Circle.toUnits.comp ψ.toAddChar.toMonoidHom
  have hθ : Continuous θ := by
    apply Units.continuous_iff.mpr
    constructor
    · exact ψ.continuous_complex
    · change Continuous (fun x : F.Carrier => (ψ.complex x)⁻¹)
      have hc : Continuous (fun x : F.Carrier => ψ.complex (-x)) :=
        ψ.continuous_complex.comp continuous_neg
      simpa only [AddChar.map_neg_eq_inv] using hc
  have hker := isOpen_ker_of_continuous_complex_character θ hθ
  let O : Set (Fin (r + 1) → F.Carrier) :=
    (fun x => Multiplicative.ofAdd (-x (Fin.last r))) ⁻¹' (θ.ker : Set _)
  refine ⟨O, hker.preimage (continuous_apply _).neg, ?_, ?_⟩
  · change θ (Multiplicative.ofAdd (-(0 : Fin (r + 1) → F.Carrier) (Fin.last r))) = 1
    simp
  · intro x hx
    exact congrArg Units.val hx

/-- A compact local section has the prescribed constant kernel near zero,
with the phase killed on its full cell support. -/
theorem exists_constantKernel_section (hσ : IsSmooth σ) (v : V) :
    ∃ (L : Set (Fin (r + 1) → F.Carrier))
      (f : (inducedRepresentation F σ χ).asModule),
      IsOpen L ∧ IsCompact L ∧ 0 ∈ L ∧
      integrand F ψ σ ℓ χ f 1 = L.indicator (fun _ => ℓ.val v) := by
  classical
  let T := F.canonicalTopologicalData
  let := T.generalLinearTopologicalGroup (r + 2)
  let B := adjacentRankLowerShape r
  let P := B.oppositeParabolic F.Carrier
  let G := GeneralLinear (r + 2) F.Carrier
  let τ := Padic.adjacentRankLowerTensorRepresentation F σ χ
  let z := (adjacentRankLowerTensorCoordinates V).symm v
  obtain ⟨O, hO, hO0, hphase⟩ := phase_eq_one_neighborhood F ψ (r := r)
  obtain ⟨H, hH⟩ := inducing_isSmooth F ψ σ χ hσ z
  obtain ⟨O', hO'open, hO'⟩ := isOpen_induced_iff.mp H.isOpen
  let U : Set G := O' ∩ columnCoordinate ⁻¹' O
  have hU : U ∈ 𝓝 (1 : G) := by
    refine IsOpen.mem_nhds (hO'open.inter (hO.preimage continuous_columnCoordinate)) ?_
    constructor
    · have h1 : (1 : P) ∈ (Subtype.val ⁻¹' O' : Set P) := by
        rw [hO']
        exact H.one_mem
      exact h1
    · change columnCoordinate (1 : G) ∈ O
      rw [← upperColumn_zero, columnCoordinate_upperColumn]
      exact hO0
  obtain ⟨K, hKc, hKU, hKfac⟩ :=
    B.exists_compactOpenSubgroup_hasBlockIwahoriFactorization T hU
  have hfac : ∀ g ∈ K, ∃ q ∈ P, ∃ n ∈ K,
      n ∈ B.unipotentSubgroup F.Carrier ∧ g = q * n := by
    intro g hg
    obtain ⟨⟨l, m, n⟩, hlmn⟩ :=
      (BlockShape.HasBlockIwahoriFactorization.bijective _ _ hKfac).2 ⟨g, hg⟩
    have he : l.val * m.val * n.val = g := congrArg Subtype.val hlmn
    exact ⟨l.val * m.val,
      P.mul_mem (B.oppositeUnipotentSubgroup_le_oppositeParabolic F.Carrier l.property.2)
        (B.leviSubgroup_le_oppositeParabolic F.Carrier m.property.2),
      n.val, n.property.1, n.property.2, he.symm⟩
  let L : Set (Fin (r + 1) → F.Carrier) := upperColumn ⁻¹' (K : Set G)
  have hLopen : IsOpen L := K.isOpen.preimage continuous_upperColumn
  have hLclosed : IsClosed L := K.isClosed.preimage continuous_upperColumn
  have hL0 : (0 : Fin (r + 1) → F.Carrier) ∈ L := by
    change upperColumn 0 ∈ K
    rw [upperColumn_zero]
    exact K.one_mem
  have hLsub : L ⊆ columnCoordinate '' (K : Set G) :=
    fun x hx => ⟨upperColumn x, hx, columnCoordinate_upperColumn x⟩
  have hLcompact : IsCompact L :=
    (hKc.image continuous_columnCoordinate).of_isClosed_subset hLclosed hLsub
  have hLO : L ⊆ O := by
    intro x hx
    have h := (hKU hx).2
    change columnCoordinate (upperColumn x) ∈ O at h
    rwa [columnCoordinate_upperColumn] at h
  have hz : z ∈ fixedVectors τ (Induction.conjOpenSubgroup P K 1).toSubgroup := by
    rintro ⟨q, hq⟩
    have hqK : (q : G) ∈ K := by
      simpa using Induction.mem_conjOpenSubgroup.mp hq
    have hqH : q ∈ H := by
      have h1 : q ∈ (Subtype.val ⁻¹' O' : Set P) := (hKU hqK).1
      rw [hO'] at h1
      exact h1
    exact hH ⟨q, hqH⟩
  let s := Induction.compactDoubleCosetSection P τ K hKc 1 z hz
  have key : ∀ g : G, Induction.eval P τ s.val g ≠ 0 →
      ∃ q ∈ P, ∃ n ∈ K, n ∈ B.unipotentSubgroup F.Carrier ∧ g = q * n := by
    intro g hg
    have hmem : Induction.quotientMap P g ∈
        Induction.quotientSupport P (Induction.eval P τ s.val) := ⟨g, hg, rfl⟩
    obtain ⟨k, hk, hkk⟩ :=
      Induction.compactDoubleCosetSection_support_subset P τ K hKc 1 z hz hmem
    have hr : g * (1 * k)⁻¹ ∈ P := QuotientGroup.rightRel_apply.mp (Quotient.exact hkk)
    obtain ⟨q₀, hq₀, n, hnK, hnN, hkeq⟩ := hfac k hk
    refine ⟨g * k⁻¹ * q₀, P.mul_mem (by simpa using hr) hq₀, n, hnK, hnN, ?_⟩
    subst hkeq
    group
  have hcell : ∀ x, x ∉ L → Induction.eval P τ s.val (upperColumn x) = 0 := by
    intro x hx
    by_contra hne
    obtain ⟨q, hq, n, hnK, hnN, he⟩ := key _ hne
    have hqN : q ∈ B.unipotentSubgroup F.Carrier := by
      have hqeq : q = upperColumn x * n⁻¹ := by
        rw [he]
        group
      rw [hqeq]
      exact (B.unipotentSubgroup F.Carrier).mul_mem (upperColumn_mem_radical x)
        ((B.unipotentSubgroup F.Carrier).inv_mem hnN)
    have hq1 := B.eq_one_of_mem_oppositeParabolic_of_mem_unipotentSubgroup
      F.Carrier hq hqN
    apply hx
    change upperColumn x ∈ K
    rw [he, hq1, one_mul]
    exact hnK
  refine ⟨L, s.val, hLopen, hLcompact, hL0, ?_⟩
  funext x
  change ℓ.val (adjacentRankLowerTensorCoordinates V
      (Induction.eval P τ s.val (upperColumn x * 1))) *
    ψ.complex (-x (Fin.last r)) = L.indicator (fun _ => ℓ.val v) x
  rw [mul_one]
  by_cases hx : x ∈ L
  · have hs := Induction.compactDoubleCosetSection_apply P τ K hKc 1 z hz 1
      ⟨upperColumn x, hx⟩
    simp only [OneMemClass.coe_one, one_mul, map_one] at hs
    rw [hs, hphase x (hLO hx), mul_one, Set.indicator_of_mem hx]
    exact congrArg ℓ.val ((adjacentRankLowerTensorCoordinates V).apply_symm_apply v)
  · rw [hcell x hx, map_zero, map_zero, zero_mul, Set.indicator_of_notMem hx]

/-- For any base character and supplied Haar, the actual Jacquet functional
is nonzero whenever its all-section convergence premise holds. -/
theorem functional_ne_zero (ν : AdditiveHaarMeasure F.Carrier)
    (hσ : IsSmooth σ) (hℓ : ℓ.val ≠ 0)
    (hI : ∀ (f : (inducedRepresentation F σ χ).asModule)
      (g : GeneralLinear (r + 2) F.Carrier),
      Integrable (integrand F ψ σ ℓ χ f g) (rowMeasure ν (r + 1))) :
    (functional F ψ σ ℓ χ ν hI).val ≠ 0 := by
  classical
  have hex : ∃ v, ℓ.val v ≠ 0 := by
    by_contra h
    apply hℓ
    ext v
    exact not_not.mp (not_exists.mp h v)
  obtain ⟨v, hv⟩ := hex
  obtain ⟨L, f, hLo, hLc, hL0, hf⟩ :=
    exists_constantKernel_section F ψ σ ℓ χ hσ v
  let μ := rowMeasure ν (r + 1)
  have hpos : 0 < μ L := hLo.measure_pos μ ⟨0, hL0⟩
  have hfin : μ L < ⊤ := hLc.measure_lt_top
  have hreal : 0 < μ.real L := ENNReal.toReal_pos hpos.ne' hfin.ne
  have hval : (functional F ψ σ ℓ χ ν hI).val f =
      (μ.real L : ℂ) * ℓ.val v := by
    change (∫ x, integrand F ψ σ ℓ χ f 1 x ∂μ) = _
    rw [hf, integral_indicator_const _ hLo.measurableSet, Complex.real_smul]
  intro hzero
  have hne : (μ.real L : ℂ) * ℓ.val v ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hreal.ne') hv
  apply hne
  rw [← hval, hzero, LinearMap.zero_apply]

/-- The actual adjacent Jacquet functional bundled with its nonvanishing proof. -/
def nonzeroFunctional (ν : AdditiveHaarMeasure F.Carrier)
    (hσ : IsSmooth σ) (hℓ : ℓ.val ≠ 0)
    (hI : ∀ (f : (inducedRepresentation F σ χ).asModule)
      (g : GeneralLinear (r + 2) F.Carrier),
      Integrable (integrand F ψ σ ℓ χ f g) (rowMeasure ν (r + 1))) :
    {J : glFunctionals ψ (r + 1) (inducedRepresentation F σ χ) // J.val ≠ 0} :=
  ⟨functional F ψ σ ℓ χ ν hI, functional_ne_zero F ψ σ ℓ χ ν hσ hℓ hI⟩

end Padic

end Langlands.RankinSelberg.AdjacentJacquet
