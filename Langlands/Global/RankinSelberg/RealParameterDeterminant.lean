import Langlands.Global.RankinSelberg.RealJacquetConventionReduction
import Langlands.Global.RankinSelberg.RealPlaceMinusOneAction
import Langlands.Global.RankinSelberg.RealPlaceEqualReflection

/-! # Determinants and compact central action for real parameters -/

noncomputable section
universe u

open scoped Classical Matrix.Norms.Operator
open Langlands.LocalFactor.Archimedean Langlands.Weil.Archimedean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

namespace Langlands.Global.RankinSelbergGlobal.RealJacquet

theorem realSign_sq (a : ℝˣ) : realSign a ^ 2 = 1 := by
  have h : ((a : ℝ) / |(a : ℝ)|) ^ 2 = 1 := by
    rw [div_pow, sq_abs, div_self (pow_ne_zero 2 a.ne_zero)]
  apply Units.ext
  simp only [Units.val_pow_eq_pow_val, coe_realSign, Units.val_one]
  exact_mod_cast h

theorem complexNorm_realToComplex (a : ℝˣ) :
    complexNorm (realToComplex a) = a ^ 2 := by
  apply Units.ext
  simp [complexNorm_apply, realToComplex, Complex.normSq_ofReal, pow_two]

theorem complexConjugation_realToComplex (a : ℝˣ) :
    complexConjugation (realToComplex a) = realToComplex a := by
  apply Units.ext
  change starRingEnd ℂ ((a : ℝ) : ℂ) = ((a : ℝ) : ℂ)
  simp

theorem determinant_append (ds es : List RealBlock) (a : ℝˣ) :
    determinant (ds ++ es) a = determinant ds a * determinant es a := by
  simp only [determinant, List.map_append, List.prod_append]

/-- The determinant identity for the explicit tensor decomposition, at every real unit. -/
theorem determinant_tensor (d e : RealBlock) (a : ℝˣ) :
    determinant (d.tensor e) a = d.determinant a ^ e.rank * e.determinant a ^ d.rank := by
  cases d with
  | character c =>
    cases e with
    | character b =>
      simp [determinant, RealBlock.tensor, RealBlock.determinant, RealBlock.rank,
        RealCharacterData.mul]
    | induced b =>
      simp only [determinant, RealBlock.tensor, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil, mul_one, RealBlock.determinant, RealBlock.rank,
        pow_one, ComplexCharacterData.realInducedDeterminant, ComplexCharacterData.twistReal,
        ContinuousMonoidHom.mul_apply, ContinuousMonoidHom.coe_comp, Function.comp_apply,
        complexNorm_realToComplex, map_pow]
      ac_rfl
  | induced c =>
    cases e with
    | character b =>
      simp only [determinant, RealBlock.tensor, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil, mul_one, RealBlock.determinant, RealBlock.rank,
        pow_one, ComplexCharacterData.realInducedDeterminant, ComplexCharacterData.twistReal,
        ContinuousMonoidHom.mul_apply, ContinuousMonoidHom.coe_comp, Function.comp_apply,
        complexNorm_realToComplex, map_pow]
      ac_rfl
    | induced b =>
      simp only [determinant, RealBlock.tensor, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil, mul_one, RealBlock.determinant, RealBlock.rank,
        ComplexCharacterData.realInducedDeterminant, ComplexCharacterData.mul,
        ComplexCharacterData.conj, ContinuousMonoidHom.mul_apply,
        ContinuousMonoidHom.coe_comp, Function.comp_apply, complexConjugation_realToComplex]
      calc
        _ = realSign a ^ 2 *
            (c.character (realToComplex a) ^ 2 * b.character (realToComplex a) ^ 2) := by
          simp only [pow_two]
          ac_rfl
        _ = _ := by rw [mul_pow, mul_pow, realSign_sq, one_mul, one_mul, one_mul]

theorem determinant_flatMap_tensor (d : RealBlock) (es : List RealBlock) (a : ℝˣ) :
    determinant (es.flatMap d.tensor) a =
      d.determinant a ^ realRank es * determinant es a ^ d.rank := by
  induction es with
  | nil => simp [determinant, realRank]
  | cons e es ih =>
    rw [List.flatMap_cons, determinant_append, determinant_tensor, ih, realRank_cons]
    simp only [determinant, List.map_cons, List.prod_cons, pow_add, mul_pow]
    simp only [mul_comm, mul_left_comm, mul_assoc]

/-- The explicit pair presentation has the tensor determinant. -/
theorem determinant_realPairBlocks (ds es : List RealBlock) (a : ℝˣ) :
    determinant (realPairBlocks ds es) a =
      determinant ds a ^ realRank es * determinant es a ^ realRank ds := by
  induction ds with
  | nil => simp [realPairBlocks, determinant, realRank]
  | cons d ds ih =>
    rw [realPairBlocks, List.flatMap_cons, ← realPairBlocks, determinant_append,
      determinant_flatMap_tensor, ih, realRank_cons]
    simp only [determinant, List.map_cons, List.prod_cons, mul_pow, pow_add]
    simp only [mul_comm, mul_left_comm, mul_assoc]

end Langlands.Global.RankinSelbergGlobal.RealJacquet

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.Archimedean Langlands.Automorphic

namespace RealJacquet

theorem induced_position_minusOne (d : ComplexCharacterData) :
    realInducedFirstCharacter d (-1) * realInducedSecondCharacter d (-1) =
      (d.realInducedDeterminant (-1) : ℂ) := by
  have hw : (-1 : ℂ) ^ d.weight = (-1 : ℂ) ^ d.weight.natAbs := by
    simp [neg_one_zpow_eq_ite, neg_one_pow_eq_ite]
  simp [realInducedFirstCharacter, realInducedSecondCharacter,
    ComplexCharacterData.coe_realInducedDeterminant, d.character_eq,
    realToComplex, hw, pow_succ]

theorem prod_position_minusOne (ds : List RealBlock) :
    (∏ i : Fin (realRank ds), realPositionCharacter ds i (-1)) =
      (determinant ds (-1) : ℂ) := by
  induction ds with
  | nil => simp [determinant]
  | cons d ds ih =>
    cases d with
    | character c =>
      change (∏ i : Fin (1 + realRank ds),
          realPositionCharacter (.character c :: ds) i (-1)) =
        (c.character (-1) : ℂ) * (determinant ds (-1) : ℂ)
      rw [Nat.add_comm 1 (realRank ds), Fin.prod_univ_succ]
      simp only [Fin.val_zero, Fin.val_succ, realPositionCharacter, ih, determinant,
        RealBlock.determinant]
    | induced c =>
      change (∏ i : Fin (2 + realRank ds),
          realPositionCharacter (.induced c :: ds) i (-1)) =
        (c.realInducedDeterminant (-1) : ℂ) * (determinant ds (-1) : ℂ)
      rw [Nat.add_comm 2 (realRank ds), Fin.prod_univ_succ, Fin.prod_univ_succ]
      simp only [Fin.val_zero, Fin.val_succ, realPositionCharacter, ih, determinant,
        RealBlock.determinant]
      rw [← mul_assoc, induced_position_minusOne]

theorem principalSeriesCharacter_minusOne (ds : List RealBlock) :
    principalSeriesCharacter ℝ (realRank ds) (realPositionCharacter ds) (fun _ => -1) =
      (determinant ds (-1) : ℂ) := by
  simpa [principalSeriesCharacter] using prod_position_minusOne ds

/-- Central covariance follows from the standard module's principal-series law. -/
theorem standard_mul_minusOne {n : ℕ} (ds : List RealBlock) (hr : realRank ds = n)
    (f : realStandardKFinite n ds) (g : Langlands.GeneralLinear n ℝ) :
    f.val (g * -1) = (determinant ds (-1) : ℂ) * f.val g := by
  subst n
  have hd : GeneralLinear.Iwasawa.diagonalUnits
      (fun _ : Fin (realRank ds) => (-1 : ℝˣ)) =
      (-1 : Langlands.GeneralLinear (realRank ds) ℝ) := by
    apply Units.ext
    simp only [GeneralLinear.Iwasawa.diagonalUnits_val, Units.val_neg, Units.val_one]
    ext i j
    by_cases hij : i = j <;> simp [hij]
  have h := f.property.1.1.2 (fun _ => -1) 1 g
  rw [hd, OneMemClass.coe_one, mul_one, principalSeriesCharacter_minusOne] at h
  simpa only [neg_one_mul, mul_neg_one] using h

end RealJacquet

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

local instance (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance {n : ℕ} (S : OperatorRealization F n) : AddCommGroup S.Space :=
  Submodule.addCommGroup _

set_option maxHeartbeats 1000000 in
/-- A nonzero standard vector detects the compact scalar through the parameter injection. -/
theorem realMinusOneScalar_eq_parameter_of_nonzero {r : ℕ}
    (T : CuspidalOperatorRealization F r)
    (v : {v : NumberField.InfinitePlace F // v.IsReal}) (ds : List RealBlock)
    (hds : T.realization.HasRealPlaceParameter v ds)
    (f : realStandardKFinite (r + 1) ds) (hf : f ≠ 0) :
    realMinusOneScalar T v = (RealJacquet.determinant ds (-1) : ℂ) := by
  obtain ⟨hr, A, hA, hK, hL⟩ := hds
  let k : unitaryCompact ℝ (r + 1) :=
    ⟨-1, (-1 : Matrix.unitaryGroup (Fin (r + 1)) ℝ).property⟩
  obtain ⟨hfk, he⟩ := hK k f
  have hfun : (⟨_, hfk⟩ : realStandardKFinite (r + 1) ds) =
      (RealJacquet.determinant ds (-1) : ℂ) • f := by
    apply Subtype.ext
    funext g
    exact RealJacquet.standard_mul_minusOne ds hr f g
  change A ⟨_, hfk⟩ = T.realization.realPlaceCompactRepresentation v (-1) (A f) at he
  have hv : (RealJacquet.determinant ds (-1) : ℂ) • A f =
      realMinusOneScalar T v • A f := by
    calc
      _ = A ((RealJacquet.determinant ds (-1) : ℂ) • f) := (A.map_smul _ _).symm
      _ = A ⟨_, hfk⟩ := congrArg A hfun.symm
      _ = T.realization.realPlaceCompactRepresentation v (-1) (A f) := he
      _ = _ := realMinusOneScalar_action T v (A f)
  have hAf : A f ≠ 0 := fun h => hf (hA (h.trans A.map_zero.symm))
  exact ((smul_left_injective ℂ hAf) hv).symm

/-- Every real standard module has a nonzero compact-finite function. This is the
remaining representation-theoretic prerequisite for the central comparison. -/
def RealStandardKFiniteNonzeroStatement : Prop :=
  ∀ ds : List RealBlock, ∃ f : realStandardKFinite (realRank ds) ds, f ≠ 0

theorem realPairCentralCompatibility_of_standardNonzero
    (hN : RealStandardKFiniteNonzeroStatement) : RealPairCentralCompatibilityStatement.{u} := by
  intro F _ _ _ r t T T' v ds es hds hes
  have hfd : ∃ f : realStandardKFinite (r + 1) ds, f ≠ 0 := by
    rw [← hds.1]
    exact hN ds
  have hfe : ∃ f : realStandardKFinite (t + 1) es, f ≠ 0 := by
    rw [← hes.1]
    exact hN es
  obtain ⟨f, hf⟩ := hfd
  obtain ⟨g, hg⟩ := hfe
  have hd := realMinusOneScalar_eq_parameter_of_nonzero T v ds hds f hf
  have he := realMinusOneScalar_eq_parameter_of_nonzero T' v es hes g hg
  rw [RealJacquet.determinant_realPairBlocks, Units.val_mul,
    Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hds.1, hes.1, ← hd, ← he]

/-- The functional equation reduces to the analytic restriction equation and
nonvanishing of the real standard compact-finite modules. -/
def RealPlaceAnalyticNonzeroReductionStatement : Prop :=
  RealJacquetRestrictionEquationStatement.{u} →
  RealStandardKFiniteNonzeroStatement →
  RealPlaceFunctionalEquationStatement.{u}

theorem realPlaceAnalyticNonzeroReduction : RealPlaceAnalyticNonzeroReductionStatement.{u} := by
  intro hJ hN
  exact realPlaceReflectionReduction hJ
    (realPairCentralCompatibility_of_standardNonzero hN)

end Langlands.Global.RankinSelbergGlobal
