import Langlands.Representation.RankinSelberg.AdjacentRankJacquetLinear
import Langlands.Group.GL.RankMaps

/-! Standard Whittaker covariance for the actual adjacent lower Jacquet integral. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Matrix
open scoped BigOperators

namespace Langlands.RankinSelberg.AdjacentJacquet

open GeneralLinear HarmonicAnalysis Whittaker

universe uF uV

section Algebra

variable {K : Type uF} [Field K] {r : ℕ}

/-- The actual leading unipotent block of an ambient upper-unipotent element. -/
def unipotentHead (n : upperUnipotent (r + 2) K) : GeneralLinear (r + 1) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    (n.val.val.submatrix Fin.castSucc Fin.castSucc) (by
      rw [Matrix.det_of_isUpperTriangular]
      · simp
      · intro i j hij
        exact n.property.1 (Fin.castSucc_lt_castSucc_iff.mpr hij))

@[simp] theorem unipotentHead_apply (n : upperUnipotent (r + 2) K)
    (i j : Fin (r + 1)) : unipotentHead n i j = n.val i.castSucc j.castSucc := rfl

/-- The leading block retains upper unipotence in exactly rank r+1. -/
theorem unipotentHead_mem (n : upperUnipotent (r + 2) K) :
    unipotentHead n ∈ upperUnipotent (r + 1) K :=
  ⟨fun _ _ hij => n.property.1 (Fin.castSucc_lt_castSucc_iff.mpr hij),
    fun i => n.property.2 i.castSucc⟩

/-- The last ambient column above the diagonal. -/
def unipotentColumn (n : upperUnipotent (r + 2) K) : Fin (r + 1) → K :=
  fun i => n.val i.castSucc (Fin.last (r + 1))

/-- The exact lower-parabolic diagonal block diag(a,1). -/
abbrev lowerBlock (a : GeneralLinear (r + 1) K) : GeneralLinear (r + 2) K :=
  rankInclusion 1 a

@[simp] theorem lowerBlock_castSucc_castSucc (a : GeneralLinear (r + 1) K)
    (i j : Fin (r + 1)) : lowerBlock a i.castSucc j.castSucc = a i j :=
  blockSum_apply_left a 1 i j

@[simp] theorem lowerBlock_castSucc_last (a : GeneralLinear (r + 1) K)
    (i : Fin (r + 1)) : lowerBlock a i.castSucc (Fin.last (r + 1)) = 0 :=
  blockSum_apply_left_right a 1 i 0

@[simp] theorem lowerBlock_last_castSucc (a : GeneralLinear (r + 1) K)
    (j : Fin (r + 1)) : lowerBlock a (Fin.last (r + 1)) j.castSucc = 0 :=
  blockSum_apply_right_left a 1 0 j

@[simp] theorem lowerBlock_last_last (a : GeneralLinear (r + 1) K) :
    lowerBlock a (Fin.last (r + 1)) (Fin.last (r + 1)) = 1 :=
  blockSum_apply_right a 1 0 0

/-- The diagonal block belongs to the host's exact opposite parabolic. -/
def lowerBlockParabolic (a : GeneralLinear (r + 1) K) :
    (adjacentRankLowerShape r).oppositeParabolic K :=
  ⟨lowerBlock a, by
    rw [BlockShape.mem_oppositeParabolic_iff]
    intro i j x y hij
    fin_cases i <;> fin_cases j
    · exact False.elim (lt_irrefl _ hij)
    · change lowerBlock a ((adjacentRankLowerShape r).index 0 x)
        ((adjacentRankLowerShape r).index 1 y) = 0
      simp only [adjacentRankLowerShape,
        Shahidi.twoBlocks_index_first (Nat.succ_pos r) (Nat.succ_pos 0),
        Shahidi.twoBlocks_index_second (Nat.succ_pos r) (Nat.succ_pos 0)]
      exact blockSum_apply_left_right a 1 x y
    · exact False.elim (by exact (by decide : ¬ (1 : Fin 2) < 0) hij)
    · exact False.elim (lt_irrefl _ hij)⟩

@[simp] theorem lowerBlockParabolic_largeProjection (a : GeneralLinear (r + 1) K) :
    adjacentRankLowerLargeProjection (lowerBlockParabolic a) = a := by
  apply Units.ext
  ext i j
  rw [adjacentRankLowerLargeProjection_apply]
  exact lowerBlock_castSucc_castSucc a i j

/-- Diagonal embedding preserves upper unipotence. -/
theorem lowerBlock_mem (a : upperUnipotent (r + 1) K) :
    lowerBlock a.val ∈ upperUnipotent (r + 2) K := by
  constructor
  · intro i j
    refine Fin.lastCases ?_ (fun i => ?_) i <;>
      refine Fin.lastCases ?_ (fun j => ?_) j
    · intro hij
      exact False.elim (lt_irrefl _ hij)
    · intro _
      exact lowerBlock_last_castSucc _ _
    · intro hij
      exact False.elim (not_lt_of_ge (Fin.le_last _) hij)
    · intro hij
      simpa only [lowerBlock_castSucc_castSucc] using
        a.property.1 (Fin.castSucc_lt_castSucc_iff.mp hij)
  · intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · exact lowerBlock_last_last _
    · simpa only [lowerBlock_castSucc_castSucc] using a.property.2 i

/-- Additive upper columns multiply by adding their column parameters. -/
theorem upperColumn_mul (x y : Fin (r + 1) → K) :
    upperColumn x * upperColumn y = upperColumn (x + y) := by
  apply Units.ext
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;>
    refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_castSucc, add_comm]

/-- Moving an upper column past the lower diagonal block multiplies its parameter. -/
theorem lowerBlock_mul_upperColumn (a : GeneralLinear (r + 1) K)
    (x : Fin (r + 1) → K) :
    lowerBlock a * upperColumn x = upperColumn (a.val *ᵥ x) * lowerBlock a := by
  apply Units.ext
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;>
    refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_castSucc, Matrix.mulVec, dotProduct]

/-- Every ambient upper-unipotent matrix has its literal head/column factorization. -/
theorem unipotent_decomposition (n : upperUnipotent (r + 2) K) :
    n.val = upperColumn (unipotentColumn n) * lowerBlock (unipotentHead n) := by
  apply Units.ext
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;>
    refine Fin.lastCases ?_ (fun j => ?_) j
  · trans 1
    · exact n.property.2 (Fin.last (r + 1))
    · simp [Matrix.mul_apply, Fin.sum_univ_castSucc]
  · trans 0
    · exact n.property.1 (Fin.castSucc_lt_last j)
    · simp [Matrix.mul_apply, Fin.sum_univ_castSucc]
  · simp [Matrix.mul_apply, Fin.sum_univ_castSucc, unipotentColumn]
  · simp [Matrix.mul_apply, Fin.sum_univ_castSucc]

/-- The affine column substitution in the actual Jacquet kernel. -/
def unipotentShift (n : upperUnipotent (r + 2) K) (x : Fin (r + 1) → K) :
    Fin (r + 1) → K :=
  ((unipotentHead n)⁻¹).val *ᵥ (x + unipotentColumn n)

/-- Literal upper-column factorization for right multiplication by n. -/
theorem upperColumn_mul_unipotent (n : upperUnipotent (r + 2) K)
    (x : Fin (r + 1) → K) :
    upperColumn x * n.val =
      lowerBlock (unipotentHead n) * upperColumn (unipotentShift n x) := by
  rw [lowerBlock_mul_upperColumn, unipotentShift, Matrix.mulVec_mulVec,
    ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec,
    unipotent_decomposition n, ← mul_assoc, upperColumn_mul]

/-- The last coordinate of a column is fixed by every upper-unipotent matrix. -/
theorem unipotent_mulVec_last (a : upperUnipotent (r + 1) K) (x : Fin (r + 1) → K) :
    (a.val.val *ᵥ x) (Fin.last r) = x (Fin.last r) := by
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]
  have hz (i : Fin r) : a.val (Fin.last r) i.castSucc = 0 :=
    a.property.1 (Fin.castSucc_lt_last i)
  simp [hz]

/-- The affine shift adds exactly the bottom entry of the last ambient column. -/
theorem unipotentShift_last (n : upperUnipotent (r + 2) K) (x : Fin (r + 1) → K) :
    unipotentShift n x (Fin.last r) = x (Fin.last r) + unipotentColumn n (Fin.last r) := by
  exact unipotent_mulVec_last ⟨_, inv_mem (unipotentHead_mem n)⟩ _

/-- The adjacent superdiagonal sum splits into the head and last-column terms. -/
theorem unipotent_superdiagonal_sum (n : upperUnipotent (r + 2) K) :
    ∑ i : Fin (r + 1), n.val i.castSucc i.succ =
      (∑ i : Fin r, unipotentHead n i.castSucc i.succ) +
        unipotentColumn n (Fin.last r) := by
  rw [Fin.sum_univ_castSucc]
  congr 1

/-- The standard ambient character has the same literal head/column splitting. -/
theorem standardCharacter_split [TopologicalSpace K] (ψ : UnitaryAdditiveCharacter K)
    (n : upperUnipotent (r + 2) K) :
    (standardCharacter ψ (r + 1) n : ℂ) =
      (standardCharacter ψ r ⟨_, unipotentHead_mem n⟩ : ℂ) *
        ψ.complex (unipotentColumn n (Fin.last r)) := by
  rw [standardCharacter_apply, standardCharacter_apply,
    unipotent_superdiagonal_sum, AddChar.map_add_eq_mul]

end Algebra

section Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance jacquetCovarianceTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance jacquetCovarianceValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance jacquetCovarianceLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance jacquetCovarianceT2 : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2
local instance jacquetCovarianceSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance jacquetCovarianceSigmaCompact : SigmaCompactSpace F.Carrier :=
  F.canonicalTopologicalData.sigmaCompactSpace
local instance jacquetCovarianceMeasurable : MeasurableSpace F.Carrier := borel _
local instance jacquetCovarianceBorel : BorelSpace F.Carrier := ⟨rfl⟩

variable {r : ℕ}

/-- The affine unipotent substitution preserves the supplied additive row Haar. -/
theorem measurePreserving_unipotentShift (ν : AdditiveHaarMeasure F.Carrier)
    (n : upperUnipotent (r + 2) F.Carrier) :
    MeasurePreserving (unipotentShift n) (rowMeasure ν (r + 1))
      (rowMeasure ν (r + 1)) := by
  have he : unipotentShift n =
      AdjacentDoubleIntegral.columnHomeomorph F (unipotentHead n)⁻¹ ∘
        (Homeomorph.addRight (unipotentColumn n)) := rfl
  rw [he]
  refine MeasurePreserving.comp
    ⟨(AdjacentDoubleIntegral.columnHomeomorph F _).continuous.measurable, ?_⟩
    (measurePreserving_add_right _ _)
  change (rowMeasure ν (r + 1)).map (fun x => ((unipotentHead n)⁻¹).val *ᵥ x) = _
  rw [AdjacentDoubleIntegral.rowMeasure_map_mulVec F ν,
    unipotent_det ⟨_, inv_mem (unipotentHead_mem n)⟩, map_one, inv_one, one_smul]

/-- The same literal substitution is a measurable embedding. -/
theorem measurableEmbedding_unipotentShift
    (n : upperUnipotent (r + 2) F.Carrier) :
    MeasurableEmbedding (unipotentShift n) :=
  (AdjacentDoubleIntegral.columnHomeomorph F _).measurableEmbedding.comp
    (Homeomorph.addRight _).measurableEmbedding

variable (ψ : UnitaryAdditiveCharacter F.Carrier)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
  (ℓ : glFunctionals ψ r σ) (χ : Quasicharacter F.Carrier)

local notation "ρ" => inducedRepresentation F σ χ

/-- The lower normalized inducing action is exactly σ(a) on a unipotent
head block: both determinant weights are one. -/
theorem tensorCoordinates_lowerBlock_action
    (a : upperUnipotent (r + 1) F.Carrier)
    (z : PiTensorProduct ℂ (Shahidi.pairCarrier V (ULift.{uV} ℂ))) :
    adjacentRankLowerTensorCoordinates V
      (Padic.adjacentRankLowerTensorRepresentation F σ χ (lowerBlockParabolic a.val) z) =
        σ a.val (adjacentRankLowerTensorCoordinates V z) := by
  have he := LinearMap.congr_fun
    ((Padic.adjacentRankLowerInducingCoordinates F σ χ).isIntertwining'
      (lowerBlockParabolic a.val)) z
  change adjacentRankLowerTensorCoordinates V
      (Padic.adjacentRankLowerTensorRepresentation F σ χ (lowerBlockParabolic a.val) z) =
    Padic.adjacentRankLowerCompactRepresentation F σ χ (lowerBlockParabolic a.val)
      (adjacentRankLowerTensorCoordinates V z) at he
  rw [he]
  have hd : GeneralLinear.determinant a.val = 1 := Units.ext (unipotent_det a)
  have hb : GeneralLinear.determinant (lowerBlock a.val) = 1 :=
    Units.ext (unipotent_det ⟨_, lowerBlock_mem a⟩)
  change (((adjacentRankDeterminantWeight F.canonicalTopologicalData χ
      (r + 2) ((r + 1 : ℕ) / 2)).toMonoidHom (lowerBlock a.val) *
        ((adjacentRankDeterminantWeight F.canonicalTopologicalData χ
          (r + 1) ((r + 2 : ℕ) / 2)).toMonoidHom
            (adjacentRankLowerLargeProjection (lowerBlockParabolic a.val)))⁻¹ : ℂˣ) : ℂ) •
      σ (adjacentRankLowerLargeProjection (lowerBlockParabolic a.val))
        (adjacentRankLowerTensorCoordinates V z) = _
  simp only [lowerBlockParabolic_largeProjection, adjacentRankDeterminantWeight_apply,
    PadicField.TopologicalData.determinantComplexPower,
    PadicField.TopologicalData.determinantUnramifiedCharacter, MonoidHom.comp_apply,
    hd, hb, map_one,
    mul_one, inv_one, Units.val_one, one_smul]

/-- Left multiplication by a unipotent lower diagonal block acts through the
specified original-carrier Whittaker functional. -/
theorem sectionCoefficient_lowerBlock
    (f : (ρ).asModule) (a : upperUnipotent (r + 1) F.Carrier)
    (g : GeneralLinear (r + 2) F.Carrier) :
    sectionCoefficient F ψ σ ℓ χ f (lowerBlock a.val * g) =
      (standardCharacter ψ r a : ℂ) * sectionCoefficient F ψ σ ℓ χ f g := by
  unfold sectionCoefficient
  rw [show lowerBlock a.val = (lowerBlockParabolic a.val).val from rfl]
  rw [Induction.eval_covariant, tensorCoordinates_lowerBlock_action]
  exact ℓ.property a _

/-- The literal kernel transforms by the standard ambient character and the
measure-preserving affine column substitution. -/
theorem integrand_unipotent_mul
    (f : (ρ).asModule) (n : upperUnipotent (r + 2) F.Carrier)
    (g : GeneralLinear (r + 2) F.Carrier) (x : Fin (r + 1) → F.Carrier) :
    integrand F ψ σ ℓ χ f (n.val * g) x =
      (standardCharacter ψ (r + 1) n : ℂ) *
        integrand F ψ σ ℓ χ f g (unipotentShift n x) := by
  unfold integrand
  rw [← mul_assoc, upperColumn_mul_unipotent, mul_assoc,
    sectionCoefficient_lowerBlock F ψ σ ℓ χ f ⟨_, unipotentHead_mem n⟩,
    standardCharacter_split, unipotentShift_last]
  have hp : ψ.complex (unipotentColumn n (Fin.last r)) *
      ψ.complex (-(x (Fin.last r) + unipotentColumn n (Fin.last r))) =
        ψ.complex (-x (Fin.last r)) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    abel
  rw [← hp]
  ring

/-- Integration of the exact substitution gives standard Whittaker covariance.
This equality of totalized integrals needs no added convergence premise. -/
theorem integral_unipotent_mul (ν : AdditiveHaarMeasure F.Carrier)
    (f : (ρ).asModule) (n : upperUnipotent (r + 2) F.Carrier)
    (g : GeneralLinear (r + 2) F.Carrier) :
    integral F ψ σ ℓ χ ν f (n.val * g) =
      (standardCharacter ψ (r + 1) n : ℂ) * integral F ψ σ ℓ χ ν f g := by
  unfold integral
  simp_rw [integrand_unipotent_mul]
  rw [integral_const_mul,
    (measurePreserving_unipotentShift F ν n).integral_comp
      (measurableEmbedding_unipotentShift F n)]

/-- Under actual all-section integrability, the scalar Jacquet integral at the
identity is a standard Whittaker functional on the exact host induction. -/
def functional (ν : AdditiveHaarMeasure F.Carrier)
    (hI : ∀ (f : (ρ).asModule) (g : GeneralLinear (r + 2) F.Carrier),
      Integrable (integrand F ψ σ ℓ χ f g) (rowMeasure ν (r + 1))) :
    glFunctionals ψ (r + 1) (ρ) :=
  ⟨integralLinear F ψ σ ℓ χ ν hI 1, by
    intro n f
    change integral F ψ σ ℓ χ ν ((ρ) n.val f) 1 =
      (standardCharacter ψ (r + 1) n : ℂ) * integral F ψ σ ℓ χ ν f 1
    rw [integral_right, one_mul]
    simpa only [mul_one] using integral_unipotent_mul F ψ σ ℓ χ ν f n 1⟩

/-- Every coefficient of this single original-carrier functional is the literal
Jacquet integral at that ambient group element. -/
theorem functional_coefficient (ν : AdditiveHaarMeasure F.Carrier)
    (hI : ∀ (f : (ρ).asModule) (g : GeneralLinear (r + 2) F.Carrier),
      Integrable (integrand F ψ σ ℓ χ f g) (rowMeasure ν (r + 1)))
    (f : (ρ).asModule) (g : GeneralLinear (r + 2) F.Carrier) :
    (functional F ψ σ ℓ χ ν hI).val ((ρ) g f) =
      integral F ψ σ ℓ χ ν f g :=
  integralLinear_coefficient F ψ σ ℓ χ ν hI f g

end Padic

end Langlands.RankinSelberg.AdjacentJacquet
