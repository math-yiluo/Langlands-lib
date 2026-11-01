import Langlands.Geometry.Analytic.GeneralizedAffinoid.LaurentGaussField
import Langlands.Geometry.Analytic.GeneralizedAffinoid.Relations
import Langlands.Geometry.Analytic.GeneralizedTateAlgebra.Evaluation
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeSeriesMap
import Langlands.Geometry.Analytic.BoundedEquivalence.Definitions
import Mathlib.Algebra.MonoidAlgebra.Basic

/-! # An actual affinoid presentation of the completed Gauss Laurent ring -/

noncomputable section

universe u v

namespace Langlands.Analytic

namespace GaussLaurent

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {t : ℝ} [Fact (0 < t)]

instance : Algebra K (GaussLaurent K t) :=
  inferInstanceAs (Algebra K (AddMonoidAlgebra K ℤ))

instance : NormedAlgebra K (GaussLaurent K t) where
  norm_smul_le a p := by
    rw [Algebra.smul_def]
    change ‖C a * p‖ ≤ ‖a‖ * ‖p‖
    exact (norm_mul_le _ _).trans_eq (by rw [norm_C])

/-- The polynomial variable and its inverse monomial. -/
def variableUnit : (GaussLaurent K t)ˣ :=
  ⟨single 1 (1 : K), single (-1) (1 : K),
    by simp [single_mul_single, one_eq_single],
    by simp [single_mul_single, one_eq_single]⟩

omit [IsUltrametricDist K] [Fact (0 < t)] in
theorem variableUnit_zpow_val (n : ℤ) :
    (↑((variableUnit : (GaussLaurent K t)ˣ) ^ n) : GaussLaurent K t) =
      single n 1 := by
  cases n with
  | ofNat n =>
    change (AddMonoidAlgebra.single (1 : ℤ) (1 : K)) ^ n =
      AddMonoidAlgebra.single (n : ℤ) 1
    simp [AddMonoidAlgebra.single_pow]
  | negSucc n =>
    rw [zpow_negSucc, ← inv_pow, Units.val_pow_eq_pow_val]
    change (AddMonoidAlgebra.single (-1 : ℤ) (1 : K)) ^ (n + 1) =
      AddMonoidAlgebra.single (Int.negSucc n) 1
    simp [AddMonoidAlgebra.single_pow, Int.negSucc_eq]

variable (B : Type v) [NormedCommRing B] [NormedAlgebra K B]
  [IsUltrametricDist B]

/-- Evaluate an integer exponent at a unit, including negative exponents. -/
def unitPowers (b : Bˣ) : Multiplicative ℤ →* B where
  toFun n := ↑(b ^ n.toAdd)
  map_one' := by simp
  map_mul' m n := by
    change (↑(b ^ (m.toAdd + n.toAdd)) : B) = _
    rw [zpow_add, Units.val_mul]

/-- The finite Laurent polynomial evaluation map. -/
def evaluate (b : Bˣ) : GaussLaurent K t →ₐ[K] B :=
  AddMonoidAlgebra.lift K B ℤ (unitPowers B b)

omit [IsUltrametricDist K] [Fact (0 < t)] [IsUltrametricDist B] in
theorem evaluate_single (b : Bˣ) (n : ℤ) (a : K) :
    evaluate B b (single (t := t) n a) = a • (↑(b ^ n) : B) :=
  AddMonoidAlgebra.lift_single (unitPowers B b) n a

/-- A coefficientwise power bound makes finite Laurent evaluation contractive. -/
theorem norm_evaluate_le (b : Bˣ) (hb : ∀ n : ℤ, ‖(↑(b ^ n) : B)‖ ≤ t ^ n)
    (p : GaussLaurent K t) : ‖evaluate B b p‖ ≤ ‖p‖ := by
  change ‖(coeff p).sum (fun n a => algebraMap K B a * (↑(b ^ n) : B))‖ ≤ ‖p‖
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg p)
  intro n _
  dsimp only
  rw [← Algebra.smul_def]
  exact ((norm_smul_le _ _).trans
    (mul_le_mul_of_nonneg_left (hb n) (norm_nonneg _))).trans (norm_coeff_mul_le p n)

theorem continuous_evaluate (b : Bˣ)
    (hb : ∀ n : ℤ, ‖(↑(b ^ n) : B)‖ ≤ t ^ n) :
    Continuous (evaluate (K := K) (t := t) B b) :=
  AddMonoidHomClass.continuous_of_bound (evaluate (K := K) (t := t) B b) 1
    (fun p => by simpa using norm_evaluate_le (K := K) (t := t) B b hb p)

end GaussLaurent

namespace CompletedGaussLaurent

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {t : ℝ} [Fact (0 < t)]

instance : NormedAlgebra K (CompletedGaussLaurent K t) := inferInstance

/-- The Laurent variable is a unit before any independence hypothesis. -/
def variableUnit : (CompletedGaussLaurent K t)ˣ :=
  Units.map (UniformSpace.Completion.coeRingHom : GaussLaurent K t →+* _).toMonoidHom
    (GaussLaurent.variableUnit : (GaussLaurent K t)ˣ)

theorem variableUnit_val : (↑(variableUnit : (CompletedGaussLaurent K t)ˣ) :
    CompletedGaussLaurent K t) = X := rfl

theorem variableUnit_inv_val :
    ((variableUnit⁻¹ : (CompletedGaussLaurent K t)ˣ) : CompletedGaussLaurent K t) =
      ((GaussLaurent.single (-1) 1 : GaussLaurent K t) : CompletedGaussLaurent K t) := rfl

theorem norm_variableUnit_inv :
    ‖((variableUnit⁻¹ : (CompletedGaussLaurent K t)ˣ) : CompletedGaussLaurent K t)‖ = t⁻¹ := by
  rw [variableUnit_inv_val, UniformSpace.Completion.norm_coe, GaussLaurent.norm_single]
  simp

/-- The dense Laurent polynomial inclusion preserves the coefficient algebra. -/
def polynomialMap : GaussLaurent K t →ₐ[K] CompletedGaussLaurent K t where
  __ := UniformSpace.Completion.coeRingHom
  commutes' _ := rfl

theorem variableUnit_zpow_val (n : ℤ) :
    (↑((variableUnit : (CompletedGaussLaurent K t)ˣ) ^ n) :
      CompletedGaussLaurent K t) =
        ((GaussLaurent.single n 1 : GaussLaurent K t) : CompletedGaussLaurent K t) := by
  rw [variableUnit, ← map_zpow, Units.coe_map, GaussLaurent.variableUnit_zpow_val]
  rfl

variable (B : Type v) [NormedCommRing B] [NormedAlgebra K B]
  [IsUltrametricDist B] [CompleteSpace B]

omit [IsUltrametricDist B] [CompleteSpace B] in
/-- A bounded map out of the Laurent completion is determined by the variable. -/
theorem hom_ext (φ ψ : BoundedAlgHom K (CompletedGaussLaurent K t) B)
    (h : φ X = ψ X) : φ = ψ := by
  have hu : Units.map φ.toAlgHom.toRingHom.toMonoidHom
      (variableUnit : (CompletedGaussLaurent K t)ˣ) =
      Units.map ψ.toAlgHom.toRingHom.toMonoidHom variableUnit := by
    apply Units.ext
    exact h
  have hm (n : ℤ) :
      φ ((GaussLaurent.single n 1 : GaussLaurent K t) : CompletedGaussLaurent K t) =
      ψ ((GaussLaurent.single n 1 : GaussLaurent K t) : CompletedGaussLaurent K t) := by
    have hn := congrArg (fun b : Bˣ => (↑(b ^ n) : B)) hu
    simp only [← map_zpow, Units.coe_map, variableUnit_zpow_val] at hn
    exact hn
  have hp : φ.toAlgHom.comp polynomialMap = ψ.toAlgHom.comp polynomialMap := by
    apply (AddMonoidAlgebra.lift K B ℤ).symm.injective
    apply MonoidHom.ext
    intro n
    exact hm n.toAdd
  apply BoundedAlgHom.ext
  intro x
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq φ.continuous ψ.continuous) ?_
  intro p
  exact DFunLike.congr_fun hp p

/-- Continuous extension of contractive finite Laurent evaluation. -/
def lift (b : Bˣ) (hb : ∀ n : ℤ, ‖(↑(b ^ n) : B)‖ ≤ t ^ n) :
    BoundedAlgHom K (CompletedGaussLaurent K t) B where
  toAlgHom :=
    { UniformSpace.Completion.extensionHom (GaussLaurent.evaluate B b).toRingHom
        (GaussLaurent.continuous_evaluate (K := K) (t := t) B b hb) with
      commutes' a := by
        change UniformSpace.Completion.extensionHom _ _
          ((GaussLaurent.C a : GaussLaurent K t) : CompletedGaussLaurent K t) =
          algebraMap K B a
        rw [UniformSpace.Completion.extensionHom_coe]
        exact (GaussLaurent.evaluate B b).commutes a }
  bounded := by
    refine ⟨1, zero_lt_one, fun x => ?_⟩
    have hcont : Continuous (UniformSpace.Completion.extensionHom
        (GaussLaurent.evaluate B b).toRingHom
        (GaussLaurent.continuous_evaluate (K := K) (t := t) B b hb)) :=
      UniformSpace.Completion.continuous_extension
    refine UniformSpace.Completion.induction_on x ?_ ?_
    · exact isClosed_le (continuous_norm.comp hcont) (continuous_const.mul continuous_norm)
    · intro p
      rw [UniformSpace.Completion.extensionHom_coe, UniformSpace.Completion.norm_coe, one_mul]
      exact GaussLaurent.norm_evaluate_le B b hb p

@[simp] theorem lift_coe (b : Bˣ)
    (hb : ∀ n : ℤ, ‖(↑(b ^ n) : B)‖ ≤ t ^ n) (p : GaussLaurent K t) :
    lift B b hb (p : CompletedGaussLaurent K t) = GaussLaurent.evaluate B b p :=
  UniformSpace.Completion.extensionHom_coe _ (GaussLaurent.continuous_evaluate B b hb) p

theorem norm_lift_le (b : Bˣ)
    (hb : ∀ n : ℤ, ‖(↑(b ^ n) : B)‖ ≤ t ^ n) (x : CompletedGaussLaurent K t) :
    ‖lift B b hb x‖ ≤ ‖x‖ := by
  refine UniformSpace.Completion.induction_on x ?_ ?_
  · exact isClosed_le (continuous_norm.comp (lift (K := K) B b hb).continuous)
      continuous_norm
  · intro p
    rw [lift_coe, UniformSpace.Completion.norm_coe]
    exact GaussLaurent.norm_evaluate_le B b hb p

theorem lift_X (b : Bˣ)
    (hb : ∀ n : ℤ, ‖(↑(b ^ n) : B)‖ ≤ t ^ n) :
    lift B b hb (X : CompletedGaussLaurent K t) = b := by
  rw [X, lift_coe, GaussLaurent.evaluate_single]
  simp

theorem lift_variableUnit_inv (b : Bˣ)
    (hb : ∀ n : ℤ, ‖(↑(b ^ n) : B)‖ ≤ t ^ n) :
    lift B b hb (↑(variableUnit⁻¹ : (CompletedGaussLaurent K t)ˣ) :
      CompletedGaussLaurent K t) = (b⁻¹ : Bˣ) := by
  rw [variableUnit_inv_val, lift_coe, GaussLaurent.evaluate_single]
  simp

end CompletedGaussLaurent

namespace LaurentAnnulus

open PresentedAffinoidAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (t : ℝ) [Fact (0 < t)]

/-- The variable and inverse-variable radii. -/
def radii : PositivePolyradius (Fin 2) where
  radius := ![t, t⁻¹]
  positive i := by
    have ht : 0 < t := Fact.out
    fin_cases i
    · exact ht
    · exact inv_pos.mpr ht

/-- The equation imposing the Laurent inverse. -/
def relation : GeneralizedTateAlgebra (radii t) K :=
  GeneralizedTateAlgebra.X (radii t) K 0 *
    GeneralizedTateAlgebra.X (radii t) K 1 - 1

/-- The actual closed weighted quotient with equation `XY = 1`. -/
abbrev presentation : PresentedAffinoidAlgebra K :=
  ofRelations K 2 (radii t) {relation K t}

theorem coordinate_mul :
    coordinate K (presentation K t) (0 : Fin 2) * coordinate K (presentation K t) (1 : Fin 2) = 1 := by
  have h := presentationMap_relation K 2 (radii t) {relation K t}
    (Set.mem_singleton (relation K t))
  change Ideal.Quotient.mk ((Ideal.span {relation K t}).closure) (relation K t) = 0 at h
  rw [relation, map_sub, map_mul, map_one, sub_eq_zero] at h
  exact h

/-- The two quotient coordinates define an actual unit. -/
def coordinateUnit : (presentation K t)ˣ :=
  ⟨coordinate K (presentation K t) (0 : Fin 2), coordinate K (presentation K t) (1 : Fin 2),
    coordinate_mul K t, by rw [mul_comm]; exact coordinate_mul K t⟩

private theorem norm_pow_le_of_bound {B : Type v} [NormedCommRing B]
    (h1 : ‖(1 : B)‖ ≤ 1) (a : B) (c : ℝ) (hc : 0 ≤ c) (ha : ‖a‖ ≤ c)
    (n : ℕ) : ‖a ^ n‖ ≤ c ^ n := by
  induction n with
  | zero => simpa only [pow_zero] using h1
  | succ n hn =>
    rw [pow_succ, pow_succ]
    exact (norm_mul_le _ _).trans (mul_le_mul hn ha (norm_nonneg _) (pow_nonneg hc n))

theorem norm_coordinateUnit_zpow_le (n : ℤ) :
    ‖(↑((coordinateUnit K t) ^ n) : presentation K t)‖ ≤ t ^ n := by
  have ht : 0 < t := Fact.out
  have hb : ‖(↑(coordinateUnit K t) : presentation K t)‖ ≤ t :=
    norm_coordinate_le K (presentation K t) (0 : Fin 2)
  have hbi : ‖(↑((coordinateUnit K t)⁻¹) : presentation K t)‖ ≤ t⁻¹ :=
    norm_coordinate_le K (presentation K t) (1 : Fin 2)
  cases n with
  | ofNat n =>
    change ‖(↑((coordinateUnit K t) ^ (n : ℤ)) : presentation K t)‖ ≤ t ^ (n : ℤ)
    rw [zpow_natCast, Units.val_pow_eq_pow_val, zpow_natCast]
    exact norm_pow_le_of_bound (norm_one_le K (presentation K t)) _ _ ht.le hb n
  | negSucc n =>
    rw [zpow_negSucc, ← inv_pow, Units.val_pow_eq_pow_val, zpow_negSucc, ← inv_pow]
    exact norm_pow_le_of_bound (norm_one_le K (presentation K t)) _ _
      (inv_pos.mpr ht).le hbi (n + 1)

/-- The variable and inverse variable in the Laurent completion. -/
def completionTuple : Fin 2 → CompletedGaussLaurent K t :=
  ![CompletedGaussLaurent.X,
    (↑(CompletedGaussLaurent.variableUnit⁻¹ : (CompletedGaussLaurent K t)ˣ) :
      CompletedGaussLaurent K t)]

theorem norm_completionTuple_le (i : Fin 2) :
    ‖completionTuple K t i‖ ≤ radii t i := by
  fin_cases i
  · exact CompletedGaussLaurent.norm_X.le
  · exact CompletedGaussLaurent.norm_variableUnit_inv.le

theorem completionTuple_monomial_bound (d : Fin 2 →₀ ℕ) :
    ‖StrictTateAlgebra.monomialValue _ (CompletedGaussLaurent K t)
      (completionTuple K t) d‖ ≤ (radii t).weight d :=
  GeneralizedTateAlgebra.monomialValue_norm_le_weight _ _
    CompletedGaussLaurent.norm_one'.le _ (norm_completionTuple_le K t) d

/-- Contractive evaluation of two-variable weighted series in the completion. -/
def completionEvaluation :
    BoundedAlgHom K (GeneralizedTateAlgebra (radii t) K) (CompletedGaussLaurent K t) :=
  GeneralizedTateAlgebra.evaluateHom (radii t) K (CompletedGaussLaurent K t)
    (completionTuple K t)
    ⟨1, zero_lt_one, fun d => by
      simpa only [one_mul] using completionTuple_monomial_bound K t d⟩

@[simp] theorem completionEvaluation_X (i : Fin 2) :
    completionEvaluation K t (GeneralizedTateAlgebra.X (radii t) K i) =
      completionTuple K t i :=
  GeneralizedTateAlgebra.evaluate_X _ _ _ _ _

theorem completionEvaluation_relation :
    completionEvaluation K t (relation K t) = 0 := by
  change (completionEvaluation K t).toAlgHom (_ * _ - 1) = 0
  rw [map_sub, map_mul, map_one, completionEvaluation_X, completionEvaluation_X]
  change CompletedGaussLaurent.X *
    (↑(CompletedGaussLaurent.variableUnit⁻¹ : (CompletedGaussLaurent K t)ˣ) :
      CompletedGaussLaurent K t) - 1 = 0
  rw [← CompletedGaussLaurent.variableUnit_val,
    (CompletedGaussLaurent.variableUnit : (CompletedGaussLaurent K t)ˣ).mul_inv, sub_self]

/-- The quotient-to-completion comparison. -/
def toCompletion :
    BoundedAlgHom K (presentation K t) (CompletedGaussLaurent K t) :=
  descendRelations K 2 (radii t) {relation K t} (CompletedGaussLaurent K t)
    (completionEvaluation K t) (fun f hf => by
      rcases Set.mem_singleton_iff.mp hf with rfl
      exact completionEvaluation_relation K t)

@[simp] theorem toCompletion_coordinate (i : Fin 2) :
    toCompletion K t (coordinate K (presentation K t) i) = completionTuple K t i :=
  completionEvaluation_X K t i

theorem norm_toCompletion_le (a : presentation K t) :
    ‖toCompletion K t a‖ ≤ ‖a‖ := by
  have h := norm_descendRelations_le K 2 (radii t) {relation K t}
    (CompletedGaussLaurent K t) (completionEvaluation K t)
    (fun f hf => by
      rcases Set.mem_singleton_iff.mp hf with rfl
      exact completionEvaluation_relation K t)
    1 zero_lt_one
    (fun f => GeneralizedTateAlgebra.evaluate_norm_le_bound (radii t) K
      (CompletedGaussLaurent K t) (completionTuple K t) 1 zero_lt_one
      (fun d => by simpa only [one_mul] using completionTuple_monomial_bound K t d) f) a
  simpa only [toCompletion, one_mul] using h

variable [CompleteSpace K]

/-- The completion-to-quotient comparison, extended from Laurent polynomials. -/
def fromCompletion :
    BoundedAlgHom K (CompletedGaussLaurent K t) (presentation K t) :=
  CompletedGaussLaurent.lift (presentation K t) (coordinateUnit K t)
    (norm_coordinateUnit_zpow_le K t)

@[simp] theorem fromCompletion_X :
    fromCompletion K t (CompletedGaussLaurent.X : CompletedGaussLaurent K t) =
      coordinate K (presentation K t) (0 : Fin 2) :=
  CompletedGaussLaurent.lift_X _ _ _

@[simp] theorem fromCompletion_variableUnit_inv :
    fromCompletion K t
      (↑(CompletedGaussLaurent.variableUnit⁻¹ : (CompletedGaussLaurent K t)ˣ) :
        CompletedGaussLaurent K t) = coordinate K (presentation K t) (1 : Fin 2) :=
  CompletedGaussLaurent.lift_variableUnit_inv _ _ _

theorem norm_fromCompletion_le (x : CompletedGaussLaurent K t) :
    ‖fromCompletion K t x‖ ≤ ‖x‖ :=
  CompletedGaussLaurent.norm_lift_le _ _ _ x

@[simp] theorem toCompletion_fromCompletion (x : CompletedGaussLaurent K t) :
    toCompletion K t (fromCompletion K t x) = x := by
  have h : (toCompletion K t).comp (fromCompletion K t) =
      BoundedAlgHom.id K (CompletedGaussLaurent K t) := by
    apply CompletedGaussLaurent.hom_ext
    change toCompletion K t (fromCompletion K t CompletedGaussLaurent.X) =
      CompletedGaussLaurent.X
    rw [fromCompletion_X, toCompletion_coordinate]
    rfl
  exact congrArg (fun f : BoundedAlgHom K (CompletedGaussLaurent K t)
    (CompletedGaussLaurent K t) => f x) h

@[simp] theorem fromCompletion_toCompletion (a : presentation K t) :
    fromCompletion K t (toCompletion K t a) = a := by
  have h : ((fromCompletion K t).comp (toCompletion K t)).comp
        (presentationMap K (presentation K t)) =
      presentationMap K (presentation K t) := by
    apply GeneralizedTateAlgebra.hom_ext (radii t) K (presentation K t)
    intro i
    change fromCompletion K t (toCompletion K t (coordinate K (presentation K t) i)) =
      coordinate K (presentation K t) i
    rw [toCompletion_coordinate]
    fin_cases i
    · exact fromCompletion_X K t
    · exact fromCompletion_variableUnit_inv K t
  obtain ⟨f, rfl⟩ := presentationMap_surjective K (presentation K t) a
  exact congrArg (fun φ : BoundedAlgHom K
    (GeneralizedTateAlgebra (presentation K t).polyradius K) (presentation K t) => φ f) h

/-- The actual weighted closed quotient is the completed Gauss Laurent algebra. -/
def equivalence :
    BoundedAlgEquiv K (presentation K t) (CompletedGaussLaurent K t) :=
  BoundedAlgEquiv.ofHomInv (toCompletion K t) (fromCompletion K t)
    (fromCompletion_toCompletion K t) (toCompletion_fromCompletion K t)

theorem norm_equivalence (a : presentation K t) :
    ‖equivalence K t a‖ = ‖a‖ := by
  apply le_antisymm (norm_toCompletion_le K t a)
  calc
    ‖a‖ = ‖fromCompletion K t (toCompletion K t a)‖ := by
      rw [fromCompletion_toCompletion]
    _ ≤ ‖toCompletion K t a‖ := norm_fromCompletion_le K t _

theorem isometry_equivalence : Isometry (equivalence K t) :=
  AddMonoidHomClass.isometry_of_norm (equivalence K t).toAlgEquiv
    (norm_equivalence K t)

end LaurentAnnulus

end Langlands.Analytic
