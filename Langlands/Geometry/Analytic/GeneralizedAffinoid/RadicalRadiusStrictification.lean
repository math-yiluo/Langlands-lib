import Langlands.Geometry.Analytic.GeneralizedAffinoid.PureLaurentRadiusExtension
import Langlands.Geometry.Analytic.GeneralizedAffinoid.Banach
import Langlands.Geometry.Analytic.GeneralizedTateAlgebra.Evaluation
import Langlands.Geometry.Analytic.TateUniversal
import Langlands.Geometry.Analytic.WeightedPowerBounds
import Langlands.Geometry.Analytic.BoundedQuotient
import Langlands.Geometry.Analytic.BoundedEquivalence.Definitions

/-! # Strict presentations for radical-value-group radii -/

noncomputable section

universe u v

namespace Langlands.Analytic

/-- A positive-power weighted bound gives the original weighted power bound:
only finitely many residual powers are needed. -/
theorem HasRadiusBoundedPowers.of_pow {B : Type v} [NormedRing B]
    {x : B} {r : ℝ} (hr : 0 < r) {n : ℕ} (hn : 0 < n)
    (h : HasRadiusBoundedPowers (r ^ n) (x ^ n)) :
    HasRadiusBoundedPowers r x := by
  classical
  obtain ⟨C, hC, hc⟩ := h
  let D : ℝ := 1 + ∑ j ∈ Finset.range n, ‖x ^ j‖ / r ^ j
  have hD : 0 < D := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg fun j _ => div_nonneg (norm_nonneg _) (pow_pos hr j).le)
  refine ⟨C * D, mul_pos hC hD, fun m => ?_⟩
  have hrem : ‖x ^ (m % n)‖ ≤ D * r ^ (m % n) := by
    apply (div_le_iff₀ (pow_pos hr _)).mp
    exact (Finset.single_le_sum
      (fun j _ => div_nonneg (norm_nonneg _) (pow_pos hr j).le)
      (Finset.mem_range.mpr (Nat.mod_lt m hn))).trans
        (le_add_of_nonneg_left zero_le_one)
  calc
    ‖x ^ m‖ = ‖(x ^ n) ^ (m / n) * x ^ (m % n)‖ := by
      rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    _ ≤ ‖(x ^ n) ^ (m / n)‖ * ‖x ^ (m % n)‖ := norm_mul_le _ _
    _ ≤ (C * (r ^ n) ^ (m / n)) * (D * r ^ (m % n)) :=
      mul_le_mul (hc _) hrem (norm_nonneg _) (mul_nonneg hC.le (pow_pos (pow_pos hr _) _).le)
    _ = C * D * r ^ m := by
      rw [← pow_mul]
      calc
        _ = C * D * (r ^ (n * (m / n)) * r ^ (m % n)) := by ring
        _ = _ := by rw [← pow_add, Nat.div_add_mod]

namespace PresentedAffinoidAlgebra.RadicalStrictification

variable (K : Type u) [NormedField K]

/-- Actual positive-power scalar witnesses for every presentation radius. -/
structure RadiusData {N : ℕ} (r : PositivePolyradius (Fin N)) where
  scalar : Fin N → K
  exponent : Fin N → ℕ
  exponent_pos : ∀ i, 0 < exponent i
  norm_scalar : ∀ i, ‖scalar i‖ = r i ^ exponent i

namespace RadiusData

variable {K} {N : ℕ} {r : PositivePolyradius (Fin N)} (D : RadiusData K r)

theorem scalar_ne_zero (i : Fin N) : D.scalar i ≠ 0 :=
  norm_pos_iff.mp ((D.norm_scalar i).symm ▸ pow_pos (r.positive i) _)

/-- A scalar large enough to normalize the original coordinate. -/
def scale (i : Fin N) : K := if r i ≤ 1 then 1 else D.scalar i

theorem radius_le_norm_scale (i : Fin N) : r i ≤ ‖D.scale i‖ := by
  unfold scale
  split_ifs with h
  · simpa using h
  · rw [D.norm_scalar]
    exact le_self_pow₀ (le_of_lt (lt_of_not_ge h)) (D.exponent_pos i).ne'

theorem scale_ne_zero (i : Fin N) : D.scale i ≠ 0 :=
  norm_pos_iff.mp ((r.positive i).trans_le (D.radius_le_norm_scale i))

end RadiusData

variable [IsUltrametricDist K] [CompleteSpace K] (A : PresentedAffinoidAlgebra K)
  (D : RadiusData K A.polyradius)

omit [CompleteSpace K] in
theorem norm_coordinate_pow_le (i : Fin A.arity) (n : ℕ) :
    ‖coordinate K A i ^ n‖ ≤ A.polyradius i ^ n := by
  change ‖(presentationMap K A (GeneralizedTateAlgebra.X A.polyradius K i)) ^ n‖ ≤ _
  rw [← map_pow (presentationMap K A).toAlgHom]
  exact (norm_presentationMap_le K A _).trans
    ((norm_pow_le _ n).trans_eq (by rw [GeneralizedTateAlgebra.norm_X_of_normOne]))

/-- Normalize the old coordinates, and add their normalized witness powers. -/
def strictTuple : Fin (A.arity + A.arity) → A :=
  Fin.addCases
    (fun i => algebraMap K A (D.scale i)⁻¹ * coordinate K A i)
    (fun i => algebraMap K A (D.scalar i)⁻¹ * coordinate K A i ^ D.exponent i)

omit [CompleteSpace K] in
theorem strictTuple_norm_le (i : Fin (A.arity + A.arity)) :
    ‖strictTuple K A D i‖ ≤ 1 := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [strictTuple, Fin.addCases_left]
    rw [← Algebra.smul_def]
    calc
      _ ≤ ‖(D.scale j)⁻¹‖ * ‖coordinate K A j‖ := norm_smul_le _ _
      _ ≤ ‖D.scale j‖⁻¹ * A.polyradius j := by
        rw [norm_inv]
        exact mul_le_mul_of_nonneg_left (norm_coordinate_le K A j) (inv_nonneg.mpr (norm_nonneg _))
      _ ≤ 1 := (inv_mul_le_one₀ (norm_pos_iff.mpr (D.scale_ne_zero j))).mpr
        (D.radius_le_norm_scale j)
  · simp only [strictTuple, Fin.addCases_right]
    rw [← Algebra.smul_def]
    calc
      _ ≤ ‖(D.scalar j)⁻¹‖ * ‖coordinate K A j ^ D.exponent j‖ := norm_smul_le _ _
      _ ≤ ‖D.scalar j‖⁻¹ * A.polyradius j ^ D.exponent j := by
        rw [norm_inv]
        exact mul_le_mul_of_nonneg_left (norm_coordinate_pow_le K A j _) (inv_nonneg.mpr (norm_nonneg _))
      _ = 1 := by rw [D.norm_scalar, inv_mul_cancel₀ (pow_pos (A.polyradius.positive j) _).ne']

omit [CompleteSpace K] in
theorem strictTuple_hasBoundedMonomials :
    StrictTateAlgebra.HasBoundedMonomials (Fin (A.arity + A.arity)) A
      (strictTuple K A D) := by
  apply (StrictTateAlgebra.hasBoundedMonomials_iff_pow_bound _ _ _).mpr
  intro i
  refine ⟨1, zero_lt_one, fun n => ?_⟩
  cases n with
  | zero =>
    simp only [pow_zero]
    change ‖(1 : A)‖ ≤ 1
    exact (norm_presentationMap_le K A 1).trans_eq norm_one
  | succ n =>
    exact (norm_pow_le' _ (Nat.succ_pos n)).trans
      (pow_le_one₀ (norm_nonneg _) (strictTuple_norm_le K A D i))

/-- The actual bounded evaluation from the strict Tate algebra. -/
def evaluation :
    BoundedAlgHom K (StrictTateAlgebra (Fin (A.arity + A.arity)) K) A :=
  StrictTateAlgebra.evaluateHom _ K A (strictTuple K A D)
    (strictTuple_hasBoundedMonomials K A D)

/-- The strict presentation is the quotient by the whole closed kernel. -/
def presentation : PresentedStrictAffinoidAlgebra K where
  arity := A.arity + A.arity
  ideal := RingHom.ker (evaluation K A D).toAlgHom.toRingHom
  ideal_closed := isClosed_eq (evaluation K A D).continuous continuous_const

/-- Kernel descent gives an injective bounded map into the original algebra. -/
def fromPresentation : BoundedAlgHom K (presentation K A D) A := by
  letI := (presentation K A D).ideal_closed
  exact BoundedAlgHom.liftQuotient K (presentation K A D).ideal (evaluation K A D)
    (fun _ h => h)

theorem fromPresentation_injective : Function.Injective (fromPresentation K A D) := by
  intro x y h
  obtain ⟨f, rfl⟩ := PresentedStrictAffinoidAlgebra.presentationMap_surjective K (presentation K A D) x
  obtain ⟨g, rfl⟩ := PresentedStrictAffinoidAlgebra.presentationMap_surjective K (presentation K A D) y
  change StrictTateAlgebra (Fin (A.arity + A.arity)) K at f g
  apply Ideal.Quotient.eq.mpr
  change (evaluation K A D).toAlgHom (f - g) = 0
  change evaluation K A D f = evaluation K A D g at h
  rw [map_sub, sub_eq_zero]
  exact h

/-- The actual coordinate classes of the strict kernel quotient. -/
def strictCoordinate (i : Fin (A.arity + A.arity)) : presentation K A D :=
  PresentedStrictAffinoidAlgebra.presentationMap K (presentation K A D)
    (StrictTateAlgebra.X _ K i)

theorem fromPresentation_strictCoordinate (i : Fin (A.arity + A.arity)) :
    fromPresentation K A D (strictCoordinate K A D i) = strictTuple K A D i := by
  change StrictTateAlgebra.evaluate _ K A (strictTuple K A D)
    (StrictTateAlgebra.X _ K i) = _
  exact StrictTateAlgebra.evaluate_X _ K A (strictTuple K A D) i

theorem strictCoordinate_pow_norm_le (i : Fin (A.arity + A.arity)) (m : ℕ) :
    ‖strictCoordinate K A D i ^ m‖ ≤ 1 := by
  change ‖(PresentedStrictAffinoidAlgebra.presentationMap K (presentation K A D)).toAlgHom
    (StrictTateAlgebra.X _ K i) ^ m‖ ≤ 1
  rw [← map_pow]
  exact (Ideal.Quotient.norm_mk_le (presentation K A D).ideal _).trans
    ((norm_pow_le (StrictTateAlgebra.X (Fin (A.arity + A.arity)) K i) m).trans_eq
      (by rw [StrictTateAlgebra.norm_X, one_pow]))

/-- Recover an original coordinate inside the strict quotient. -/
def weightedTuple (i : Fin A.arity) : presentation K A D :=
  algebraMap K (presentation K A D) (D.scale i) *
    strictCoordinate K A D (Fin.castAdd A.arity i)

theorem fromPresentation_weightedTuple (i : Fin A.arity) :
    fromPresentation K A D (weightedTuple K A D i) = coordinate K A i := by
  change (fromPresentation K A D).toAlgHom
    (algebraMap K (presentation K A D) (D.scale i) *
      strictCoordinate K A D (Fin.castAdd A.arity i)) = _
  rw [map_mul, AlgHom.commutes, fromPresentation_strictCoordinate]
  simp only [strictTuple, Fin.addCases_left]
  rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ (D.scale_ne_zero i), map_one, one_mul]

theorem weightedTuple_pow (i : Fin A.arity) :
    weightedTuple K A D i ^ D.exponent i =
      algebraMap K (presentation K A D) (D.scalar i) *
        strictCoordinate K A D (Fin.natAdd A.arity i) := by
  apply fromPresentation_injective K A D
  rw [map_pow, fromPresentation_weightedTuple, map_mul, AlgHom.commutes,
    fromPresentation_strictCoordinate]
  simp only [strictTuple, Fin.addCases_right]
  rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ (D.scalar_ne_zero i), map_one, one_mul]

theorem weightedTuple_hasRadiusBoundedPowers (i : Fin A.arity) :
    HasRadiusBoundedPowers (A.polyradius i) (weightedTuple K A D i) := by
  apply HasRadiusBoundedPowers.of_pow (A.polyradius.positive i) (D.exponent_pos i)
  refine ⟨1, zero_lt_one, fun m => ?_⟩
  rw [one_mul, weightedTuple_pow, mul_pow, ← map_pow, ← Algebra.smul_def]
  calc
    _ ≤ ‖D.scalar i ^ m‖ *
        ‖strictCoordinate K A D (Fin.natAdd A.arity i) ^ m‖ := norm_smul_le _ _
    _ ≤ ‖D.scalar i ^ m‖ * 1 :=
      mul_le_mul_of_nonneg_left (strictCoordinate_pow_norm_le K A D _ m) (norm_nonneg _)
    _ = _ := by rw [mul_one, norm_pow, D.norm_scalar]

/-- Actual weighted evaluation into the strict quotient. -/
def weightedEvaluation :
    BoundedAlgHom K (GeneralizedTateAlgebra A.polyradius K) (presentation K A D) :=
  GeneralizedTateAlgebra.evaluateHom A.polyradius K (presentation K A D)
    (weightedTuple K A D)
    ((GeneralizedTateAlgebra.hasBoundedMonomials_iff_radiusBoundedPowers
      A.polyradius (presentation K A D) _).mpr
        (weightedTuple_hasRadiusBoundedPowers K A D))

theorem fromPresentation_comp_weightedEvaluation :
    (fromPresentation K A D).comp (weightedEvaluation K A D) =
      presentationMap K A := by
  apply GeneralizedTateAlgebra.hom_ext
  intro i
  change fromPresentation K A D
    (GeneralizedTateAlgebra.evaluate A.polyradius K (presentation K A D)
      (weightedTuple K A D) (GeneralizedTateAlgebra.X A.polyradius K i)) =
      coordinate K A i
  rw [GeneralizedTateAlgebra.evaluate_X, fromPresentation_weightedTuple]

theorem weightedEvaluation_annihilates (f : GeneralizedTateAlgebra A.polyradius K)
    (hf : f ∈ A.ideal) : weightedEvaluation K A D f = 0 := by
  apply fromPresentation_injective K A D
  have h := congrArg (fun φ : BoundedAlgHom K (GeneralizedTateAlgebra A.polyradius K) A =>
    φ f) (fromPresentation_comp_weightedEvaluation K A D)
  exact h.trans (((presentationMap_eq_zero_iff K A f).mpr hf).trans
    (map_zero (fromPresentation K A D).toAlgHom).symm)

/-- Descend the actual weighted evaluation through the original closed ideal. -/
def toPresentation : BoundedAlgHom K A (presentation K A D) := by
  letI := A.ideal_closed
  exact BoundedAlgHom.liftQuotient K A.ideal (weightedEvaluation K A D)
    (weightedEvaluation_annihilates K A D)

theorem fromPresentation_toPresentation (a : A) :
    fromPresentation K A D (toPresentation K A D a) = a := by
  obtain ⟨f, rfl⟩ := presentationMap_surjective K A a
  exact congrArg
    (fun φ : BoundedAlgHom K (GeneralizedTateAlgebra A.polyradius K) A => φ f)
    (fromPresentation_comp_weightedEvaluation K A D)

theorem toPresentation_fromPresentation (q : presentation K A D) :
    toPresentation K A D (fromPresentation K A D q) = q := by
  apply fromPresentation_injective K A D
  exact fromPresentation_toPresentation K A D (fromPresentation K A D q)

/-- An actual strict presentation boundedly equivalent over the same field. -/
def boundedEquiv : BoundedAlgEquiv K A (presentation K A D) :=
  BoundedAlgEquiv.ofHomInv (toPresentation K A D) (fromPresentation K A D)
    (fromPresentation_toPresentation K A D) (toPresentation_fromPresentation K A D)

/-- Choose concrete scalar witnesses from the radical-value-group condition. -/
def radiusDataOfRadical (h : ∀ i, RadiusInRadicalValueGroup K (A.polyradius i)) :
    RadiusData K A.polyradius where
  scalar i := (h i).choose
  exponent i := (h i).choose_spec.choose
  exponent_pos i := (h i).choose_spec.choose_spec.1
  norm_scalar i := (h i).choose_spec.choose_spec.2

/-- Radical-value-group radii suffice for a strict presentation over the
original complete coefficient field, in its full universe. -/
theorem exists_strictPresentation
    (h : ∀ i, RadiusInRadicalValueGroup K (A.polyradius i)) :
    ∃ Q : PresentedStrictAffinoidAlgebra K, Nonempty (BoundedAlgEquiv K A Q) :=
  ⟨presentation K A (radiusDataOfRadical K A h),
    ⟨boundedEquiv K A (radiusDataOfRadical K A h)⟩⟩

end PresentedAffinoidAlgebra.RadicalStrictification

end Langlands.Analytic
