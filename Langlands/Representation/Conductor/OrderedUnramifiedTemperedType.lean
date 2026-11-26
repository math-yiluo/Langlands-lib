import Langlands.Representation.Unramified.UnitaryPrincipalSeriesBlocks
import Langlands.AllField.Representation.RankinSelberg.TemperedTypeLFactorProof
import Langlands.AllField.Representation.RankinSelberg.RankOneWhittakerTypeProof
import Langlands.AllField.Representation.Conductor.UnramifiedPrincipalSeriesInduction
import Langlands.Representation.Conductor.OrderedUnramifiedRankOneBlocks
import Langlands.Representation.Conductor.OrderedUnramifiedProductComparison
import Langlands.AllField.Representation.Induction.SingleBlockSupplement

/-!
# Unramified principal series as standard modules of unitary rank-one blocks

Over a nonarchimedean local field `F`, with a uniformizer `ϖ` and residue cardinality `q`,
write the unramified character `χ_z` with `χ_z(ϖ) = z` as `χ_w ν^v`, where `w = z / |z|`
has norm one and `|z| = q^(-v)`. The unitary unramified characters of `GL_1(F)` are
irreducible and tempered. For `x` with `|x_1| ≤ ⋯ ≤ |x_(n+1)|` the exponents are
antitone, so the blocks `χ_(w_j)` with exponents `v_j` form a tempered-type datum whose
standard module is `I(x)`.
-/

noncomputable section

namespace Langlands.Conductor.OrderedUnramifiedTemperedType

open Langlands.GeneralLinear Langlands.HarmonicAnalysis Langlands.Whittaker
open Langlands.Conductor.UnramifiedPrincipalSeries
open Langlands.AllField.RankinSelberg
open scoped NNReal

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

section Center

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The center of `GL_1(F)` is the whole group. -/
theorem center_generalLinear_one : Subgroup.center (GeneralLinear 1 F) = ⊤ := by
  refine top_unique fun g _ => Subgroup.mem_center_iff.mpr fun h => ?_
  apply Units.ext
  ext i j
  fin_cases i
  fin_cases j
  simp [Matrix.mul_apply, mul_comm]

instance : Subsingleton (GeneralLinear 1 F ⧸ Subgroup.center (GeneralLinear 1 F)) :=
  Langlands.Unramified.subsingleton_centralQuotient_one F

end Center

section RankOne

open OrderedUnramifiedRankOneBlocks

variable {ϖ : Fˣ} (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation F) ϖ)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem norm_character_eq_one {w : ℂˣ} (hw : ‖(w : ℂ)‖ = 1) (a : Fˣ) :
    ‖(character hϖ w a : ℂ)‖ = 1 := by
  rw [character_apply, Units.val_zpow_eq_zpow_val, norm_zpow, hw, one_zpow]

/-- A unitary unramified character of `GL_1(F)` is tempered. -/
theorem rankOneBlock_tempered {w : ℂˣ} (hw : ‖(w : ℂ)‖ = 1) :
    IsTemperedRepresentation (rankOneBlock hϖ w).obj.representation := by
  have := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup 1
  let : MeasurableSpace (GeneralLinear 1 F ⧸ Subgroup.center (GeneralLinear 1 F)) := borel _
  have : BorelSpace (GeneralLinear 1 F ⧸ Subgroup.center (GeneralLinear 1 F)) := ⟨rfl⟩
  intro μ hμ
  let χ : GeneralLinear 1 F →* ℂˣ := (character hϖ w).comp (determinant (n := 1))
  have hopen : IsOpen (χ.ker : Set (GeneralLinear 1 F)) :=
    (isOpen_ker_character hϖ w).preimage (determinantContinuous (n := 1) (R := F)).continuous
  let c : UnitaryCentralCharacter (rankOneBlock hϖ w).obj.representation :=
    { character := χ.comp (Subgroup.center (GeneralLinear 1 F)).subtype
      isOpen_ker := hopen.preimage continuous_subtype_val
      norm_eq_one := fun z => norm_character_eq_one hϖ hw _
      acts := fun z v => rfl }
  refine ⟨(rankOneBlock hϖ w).property.2.1, c, fun ℓ v ε _ => ?_⟩
  have hconst : c.coefficientNorm ℓ v = fun _ => c.coefficientNorm ℓ v 1 :=
    funext fun y => congrArg _ (Subsingleton.elim y 1)
  rw [hconst]
  exact MeasureTheory.memLp_const _

/-- The rank-one block is of Whittaker type for every additive character. -/
theorem rankOneBlock_whittaker (ψ : UnitaryAdditiveCharacter F) (w : ℂˣ) :
    IsOfRankWhittakerType ψ (rankOneBlock hϖ w).obj.representation := by
  have h := Langlands.AllField.RankinSelberg.rankOneCharacter_isOfWhittakerType F ψ
    (Langlands.AllField.Conductor.UnramifiedPrincipalSeries.quasicharacter hϖ w)
  let e : (Langlands.RankinSelberg.rankOneCharacter (character hϖ w)).Equiv
      (rankOneBlock hϖ w).obj.representation :=
    { toLinearEquiv := ULift.moduleEquiv.symm
      isIntertwining' := fun g => by
        ext
        rfl }
  exact (isOfRankWhittakerType_succ ψ _).mpr
    (Langlands.RankinSelberg.IsOfWhittakerType.of_equiv h e)

end RankOne

section Splitting

/-- The norm-one part `z / |z|` of a nonzero complex number. -/
def unitaryPart (z : ℂˣ) : ℂˣ :=
  Units.mk0 ((z : ℂ) / (‖(z : ℂ)‖ : ℂ))
    (div_ne_zero z.ne_zero (by exact_mod_cast (norm_ne_zero_iff.mpr z.ne_zero)))

theorem norm_unitaryPart (z : ℂˣ) : ‖((unitaryPart z : ℂˣ) : ℂ)‖ = 1 := by
  have h : ‖(z : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr z.ne_zero
  simp only [unitaryPart, Units.val_mk0, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_norm, div_self h]

/-- The real exponent `v` with `|z| = q^(-v)`. -/
def realExponent (q : ℕ) (z : ℂˣ) : ℝ := -Real.logb q ‖(z : ℂ)‖

theorem realExponent_antitone {q : ℕ} (hq : 1 < q) {n : ℕ} {x : Fin n → ℂˣ}
    (hx : Monotone (fun i => ‖(x i : ℂ)‖)) : Antitone (fun i => realExponent q (x i)) := by
  intro i j hij
  have hq' : (1 : ℝ) < q := by exact_mod_cast hq
  simp only [realExponent, neg_le_neg_iff]
  exact Real.logb_le_logb_of_le hq' (norm_pos_iff.mpr (x i).ne_zero) (hx hij)

variable {ϖ : Fˣ} (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation F) ϖ)

/-- `χ_z = χ_(z/|z|) · |·|^v` with `|z| = q^(-v)`. -/
theorem character_unitaryPart_mul {q : ℕ} (hq : IsResidueCardinality (F := F) q)
    (z : ℂˣ) (a : Fˣ) :
    (character hϖ (unitaryPart z) a : ℂ) *
        ((((⟨⟩ : LocalFieldData F).normalizedAbs (a : F)) ^ (realExponent q z) : ℝ) : ℂ) =
      (character hϖ z a : ℂ) := by
  have hq1 : 1 < q := by
    have := (LocalFieldData.ofInstances F).residueCardinality_gt_one
    rwa [AllField.RankinSelberg.residueCardinality_ofInstances, ← hq] at this
  have hq0 : (0 : ℝ) < q := by exact_mod_cast lt_trans Nat.zero_lt_one hq1
  have hz : 0 < ‖(z : ℂ)‖ := norm_pos_iff.mpr z.ne_zero
  have habs := Langlands.AllField.Conductor.UnramifiedPrincipalSeries.normalizedAbs_units hϖ hq a
  change (character hϖ (unitaryPart z) a : ℂ) *
      ((((LocalFieldData.ofInstances F).normalizedAbs (a : F)) ^ (realExponent q z) : ℝ) : ℂ) =
    (character hϖ z a : ℂ)
  rw [habs]
  set k := ord hϖ a
  have hreal : (((q : ℝ) ^ (-k)) ^ (realExponent q z) : ℝ) = ‖(z : ℂ)‖ ^ k := by
    rw [← Real.rpow_intCast, ← Real.rpow_mul hq0.le, realExponent]
    rw [show ((-k : ℤ) : ℝ) * -Real.logb q ‖(z : ℂ)‖ = Real.logb q ‖(z : ℂ)‖ * k by
      push_cast; ring]
    rw [Real.rpow_mul hq0.le, Real.rpow_logb hq0 (by exact_mod_cast hq1.ne') hz,
      Real.rpow_intCast]
  rw [hreal, character_apply, character_apply, Units.val_zpow_eq_zpow_val,
    Units.val_zpow_eq_zpow_val]
  simp only [unitaryPart, Units.val_mk0, Complex.ofReal_zpow]
  rw [div_zpow, div_mul_cancel₀]
  exact zpow_ne_zero _ (by exact_mod_cast hz.ne')

theorem one_lt_of_isResidueCardinality {q : ℕ} (hq : IsResidueCardinality (F := F) q) :
    1 < q := by
  have := (LocalFieldData.ofInstances F).residueCardinality_gt_one
  rwa [AllField.RankinSelberg.residueCardinality_ofInstances, ← hq] at this

end Splitting

section Datum

open OrderedUnramifiedRankOneBlocks
open Langlands.AllField.Conductor.UnramifiedPrincipalSeries (borelBlocks blocks)

variable {ϖ : Fˣ} (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation F) ϖ)
  (n : ℕ) {q : ℕ} (hq : IsResidueCardinality (F := F) q)

/-- The unramified principal series `I(x)` with `|x_1| ≤ ⋯ ≤ |x_(n+1)|` as a datum of
unitary rank-one blocks `χ_(x_j / |x_j|)` with the antitone exponents `v_j`,
`|x_j| = q^(-v_j)`. -/
def unramifiedDatum (x : Fin (n + 1) → ℂˣ) (hx : Monotone (fun i => ‖(x i : ℂ)‖)) :
    TemperedTypeDatum.{uF, uF} (F := F) (n + 1) where
  shape := borelBlocks n
  blocks j := (rankOneBlock hϖ (unitaryPart (x j))).obj
  irreducible j := (rankOneBlock hϖ (unitaryPart (x j))).property.1
  tempered j := rankOneBlock_tempered hϖ (norm_unitaryPart (x j))
  whittaker ψ j := rankOneBlock_whittaker hϖ ψ (unitaryPart (x j))
  exponent j := realExponent q (x j)
  antitone := realExponent_antitone (one_lt_of_isResidueCardinality hq) hx

/-- The twisted block `χ_(x_j / |x_j|) ν^(v_j)` is the rank-one character `χ_(x_j)`. -/
def unramifiedDatum_twistedBlockEquiv (x : Fin (n + 1) → ℂˣ)
    (hx : Monotone (fun i => ‖(x i : ℂ)‖)) (j : Fin (borelBlocks n).length) :
    ((unramifiedDatum hϖ n hq x hx).twistedBlock j).representation.Equiv
      (blocks hϖ n x j) where
  toLinearEquiv := ULift.moduleEquiv
  isIntertwining' g := by
    ext v
    change ((determinantPowerCharacter 1 (realExponent q (x j)) g : ℂˣ) : ℂ) *
        ((character hϖ (unitaryPart (x j)) (determinant g) : ℂ) * v.down) =
      (character hϖ (x j) (determinant g) : ℂ) * v.down
    rw [← mul_assoc, mul_comm ((determinantPowerCharacter 1 _ g : ℂˣ) : ℂ),
      ← character_unitaryPart_mul hϖ hq (x j) (determinant g)]
    rfl

/-- The standard module of `unramifiedDatum` is `I(x)`. -/
def unramifiedDatum_standardModuleEquiv (x : Fin (n + 1) → ℂˣ)
    (hx : Monotone (fun i => ‖(x i : ℂ)‖)) :
    (unramifiedDatum hϖ n hq x hx).standardModule.Equiv (principalSeries hϖ n hq x) :=
  ((⟨⟩ : LocalFieldData F).normalizedProductInducedEquiv (borelBlocks n)
    (unramifiedDatum_twistedBlockEquiv hϖ n hq x hx)).trans
    (Langlands.AllField.Conductor.UnramifiedPrincipalSeries.principalSeriesEquiv
      hϖ n hq x).symm

/-- The one-block datum of the character `χ_z` of `GL_1(F)`. -/
abbrev pointDatum (z : ℂˣ) : TemperedTypeDatum.{uF, uF} (F := F) (0 + 1) :=
  unramifiedDatum hϖ 0 hq (fun _ => z) (fun _ _ _ => le_rfl)

/-- The standard module of the one-block datum of `χ_z` is the rank-one character
`χ_z ∘ det`. -/
def pointDatum_standardModuleEquiv (z : ℂˣ) :
    (pointDatum hϖ hq z).standardModule.Equiv
      (Langlands.RankinSelberg.rankOneCharacter (character hϖ z)) := by
  have hB : (borelBlocks 0).length = 1 := rfl
  have hsmooth : ∀ i, IsSmooth ((pointDatum hϖ hq z).twistedBlock i).representation :=
    fun i => ((pointDatum hϖ hq z).twistedBlock i).isSmooth
  refine ((⟨⟩ : LocalFieldData F).singleBlockNormalizedProductEquiv (borelBlocks 0) hB
    _ hsmooth ⟨0, Nat.zero_lt_one⟩).trans ?_
  refine Representation.Equiv.trans ?_
    (unramifiedDatum_twistedBlockEquiv hϖ 0 hq (fun _ => z) (fun _ _ _ => le_rfl)
      ⟨0, Nat.zero_lt_one⟩)
  apply equivOfRepresentationEq
  ext g v
  have hφ : (GeneralLinear.reindex (R := F)
      (finCongr ((borelBlocks 0).singleBlock_size hB ⟨0, Nat.zero_lt_one⟩))).symm g = g := by
    apply Units.ext
    ext i j
    fin_cases i
    fin_cases j
    rfl
  exact congrArg
    (fun h => (((pointDatum hϖ hq z).twistedBlock ⟨0, Nat.zero_lt_one⟩).representation h) v) hφ

end Datum

end Langlands.Conductor.OrderedUnramifiedTemperedType
