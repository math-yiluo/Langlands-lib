import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeLaurentBaseChange
import Langlands.Geometry.Analytic.GeneralizedTateAlgebra.CoefficientMap
import Langlands.Geometry.Analytic.GeneralizedTateAlgebra.RelativeEvaluation

/-! # The actual relative Laurent annulus over the completed Laurent field -/

noncomputable section

universe u

namespace Langlands.Analytic.RelativeLaurentAnnulus

open PresentedAffinoidAlgebra GeneralizedTateAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (A : PresentedAffinoidAlgebra K) (t : ℝ) [Fact (0 < t)]

/-- Integer powers of the actual Laurent coordinate have their prescribed bounds. -/
theorem norm_coordinateUnit_zpow_le (n : ℤ) :
    ‖(↑((coordinateUnit K A t) ^ n) : algebra K A t)‖ ≤ t ^ n := by
  have ht : 0 < t := Fact.out
  have hp (b : algebra K A t) (s : ℝ) (hs : 0 ≤ s) (hb : ‖b‖ ≤ s) (m : ℕ) :
      ‖b ^ m‖ ≤ s ^ m := by
    induction m with
    | zero => simpa only [pow_zero] using norm_one_le K (algebra K A t)
    | succ m hm =>
      rw [pow_succ, pow_succ]
      exact (norm_mul_le _ _).trans
        (mul_le_mul hm hb (norm_nonneg _) (pow_nonneg hs m))
  cases n with
  | ofNat n =>
    change ‖(↑((coordinateUnit K A t) ^ (n : ℤ)) : algebra K A t)‖ ≤ t ^ (n : ℤ)
    rw [zpow_natCast, Units.val_pow_eq_pow_val, zpow_natCast]
    exact hp _ _ ht.le
      (Adjoin.norm_newCoordinate_le K A (LaurentAnnulus.radii t) {relation K A t} 0) n
  | negSucc n =>
    rw [zpow_negSucc, ← inv_pow, Units.val_pow_eq_pow_val, zpow_negSucc, ← inv_pow]
    exact hp _ _ (inv_pos.mpr ht).le
      (Adjoin.norm_newCoordinate_le K A (LaurentAnnulus.radii t) {relation K A t} 1) (n + 1)

variable [CompleteSpace K]

/-- The completed Laurent constants in the actual relative Laurent annulus. -/
def completedScalarMap :
    BoundedAlgHom K (CompletedGaussLaurent K t) (algebra K A t) :=
  CompletedGaussLaurent.lift (algebra K A t) (coordinateUnit K A t)
    (norm_coordinateUnit_zpow_le K A t)

theorem norm_completedScalarMap_le (z : CompletedGaussLaurent K t) :
    ‖completedScalarMap K A t z‖ ≤ ‖z‖ :=
  CompletedGaussLaurent.norm_lift_le _ _ _ z

@[simp] theorem completedScalarMap_X :
    completedScalarMap K A t (CompletedGaussLaurent.X : CompletedGaussLaurent K t) =
      Adjoin.newCoordinate K A (LaurentAnnulus.radii t) {relation K A t} 0 :=
  CompletedGaussLaurent.lift_X _ _ _

@[simp] theorem completedScalarMap_invVariable :
    completedScalarMap K A t
      (↑(CompletedGaussLaurent.variableUnit⁻¹ : (CompletedGaussLaurent K t)ˣ) :
        CompletedGaussLaurent K t) =
      Adjoin.newCoordinate K A (LaurentAnnulus.radii t) {relation K A t} 1 :=
  CompletedGaussLaurent.lift_variableUnit_inv _ _ _

theorem transport_completedScalarMap {B : PresentedAffinoidAlgebra K}
    (φ : BoundedAlgHom K A B) :
    (transport K t φ).comp (completedScalarMap K A t) = completedScalarMap K B t := by
  apply CompletedGaussLaurent.hom_ext
  change transport K t φ
    (completedScalarMap K A t CompletedGaussLaurent.X) =
      completedScalarMap K B t CompletedGaussLaurent.X
  rw [completedScalarMap_X, transport_newCoordinate, completedScalarMap_X]

namespace ScalarExtension

variable [H : Fact (∀ (a : K) (n : ℤ), n ≠ 0 → ‖a‖ ≠ t ^ n)]

instance independentNormedField : NormedField (CompletedGaussLaurent K t) :=
  CompletedGaussLaurent.normedField H.out

/-- The actual scalar action furnished by the completed Laurent constants. -/
instance annulusNormedAlgebra : NormedAlgebra (CompletedGaussLaurent K t) (algebra K A t) where
  toAlgebra := (completedScalarMap K A t).toAlgHom.toRingHom.toAlgebra
  norm_smul_le z a :=
    (norm_mul_le (completedScalarMap K A t z) a).trans
      (mul_le_mul_of_nonneg_right (norm_completedScalarMap_le K A t z) (norm_nonneg a))

instance annulusScalarTower :
    IsScalarTower K (CompletedGaussLaurent K t) (algebra K A t) :=
  IsScalarTower.of_algebraMap_eq fun c => ((completedScalarMap K A t).toAlgHom.commutes c).symm

/-- Coefficient extension without rescaling the original positive radii. -/
def coefficientMap : BoundedAlgHom K K (CompletedGaussLaurent K t) where
  toAlgHom := Algebra.ofId K (CompletedGaussLaurent K t)
  bounded := ⟨1, zero_lt_one, fun a => by
    change ‖CompletedGaussLaurent.ι a‖ ≤ 1 * ‖a‖
    rw [CompletedGaussLaurent.norm_ι, one_mul]⟩

/-- The original weighted presentation after extension of its coefficient field. -/
def presentation : PresentedAffinoidAlgebra (CompletedGaussLaurent K t) :=
  ofRelations (CompletedGaussLaurent K t) A.arity A.polyradius
    (mapCoefficientsAlgHom A.polyradius (coefficientMap K t) '' A.ideal)

instance presentationNormedAlgebra :
    NormedAlgebra K (presentation K A t) :=
  NormedAlgebra.restrictScalars K (CompletedGaussLaurent K t) (presentation K A t)

instance presentationScalarTower :
    IsScalarTower K (CompletedGaussLaurent K t) (presentation K A t) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The quotient presentation map, with its original scalar compatibility retained. -/
def presentationMapOverBase :
    BoundedAlgHom K (GeneralizedTateAlgebra A.polyradius (CompletedGaussLaurent K t))
      (presentation K A t) where
  toAlgHom := (presentationMap (CompletedGaussLaurent K t)
    (presentation K A t)).toAlgHom.restrictScalars K
  bounded := (presentationMap (CompletedGaussLaurent K t)
    (presentation K A t)).bounded

/-- The original coefficient series map followed by the actual extended quotient. -/
def seriesBaseMap :
    BoundedAlgHom K (GeneralizedTateAlgebra A.polyradius K) (presentation K A t) :=
  (presentationMapOverBase K A t).comp
    (mapCoefficientsAlgHom A.polyradius (coefficientMap K t))

omit [CompleteSpace K] in
theorem seriesBaseMap_ideal (f : GeneralizedTateAlgebra A.polyradius K) (hf : f ∈ A.ideal) :
    seriesBaseMap K A t f = 0 :=
  presentationMap_relation (CompletedGaussLaurent K t) _ _ _
    (Set.mem_image_of_mem _ hf)

/-- The actual original algebra map into the extended weighted quotient. -/
def base : BoundedAlgHom K A (presentation K A t) := by
  letI := A.ideal_closed
  exact BoundedAlgHom.liftQuotient K A.ideal (seriesBaseMap K A t)
    (seriesBaseMap_ideal K A t)

omit [CompleteSpace K] in
@[simp] theorem base_presentationMap (f : GeneralizedTateAlgebra A.polyradius K) :
    base K A t (presentationMap K A f) =
      presentationMap (CompletedGaussLaurent K t) (presentation K A t)
        (mapCoefficientsAlgHom A.polyradius (coefficientMap K t) f) := rfl

/-- The scalar inclusion into the actual extended quotient, also over `K`. -/
def scalarInclusion : BoundedAlgHom K (CompletedGaussLaurent K t) (presentation K A t) :=
  (presentationMapOverBase K A t).comp
    (constantAlgHom A.polyradius K (CompletedGaussLaurent K t))

omit [CompleteSpace K] in
theorem norm_scalarInclusion_le (z : CompletedGaussLaurent K t) :
    ‖scalarInclusion K A t z‖ ≤ ‖z‖ := by
  exact (norm_presentationMap_le (CompletedGaussLaurent K t) (presentation K A t) _).trans_eq
    (norm_constantAlgHom A.polyradius K (CompletedGaussLaurent K t) z)

/-- The Laurent variable and its inverse viewed as extended scalars. -/
def scalarTuple : Fin 2 → presentation K A t :=
  fun j => scalarInclusion K A t (LaurentAnnulus.completionTuple K t j)

omit [CompleteSpace K] in
theorem scalarTuple_bounded :
    HasBoundedMonomials (LaurentAnnulus.radii t) (presentation K A t) (scalarTuple K A t) := by
  refine ⟨1, zero_lt_one, fun d => ?_⟩
  rw [one_mul]
  apply monomialValue_norm_le_weight _ _
    (norm_one_le (CompletedGaussLaurent K t) (presentation K A t))
  intro j
  exact (norm_scalarInclusion_le K A t _).trans (LaurentAnnulus.norm_completionTuple_le K t j)

omit [CompleteSpace K] in
theorem scalarTuple_mul : scalarTuple K A t 0 * scalarTuple K A t 1 = 1 := by
  change scalarInclusion K A t CompletedGaussLaurent.X *
    scalarInclusion K A t (↑(CompletedGaussLaurent.variableUnit⁻¹ :
      (CompletedGaussLaurent K t)ˣ) : CompletedGaussLaurent K t) = 1
  rw [← map_mul, ← CompletedGaussLaurent.variableUnit_val,
    (CompletedGaussLaurent.variableUnit : (CompletedGaussLaurent K t)ˣ).mul_inv, map_one]

/-- The actual annulus map to its coefficient-extended weighted presentation. -/
def toPresentation : BoundedAlgHom K (algebra K A t) (presentation K A t) :=
  liftFromBase K t (presentation K A t) (base K A t) (scalarTuple K A t)
    (scalarTuple_bounded K A t) (scalarTuple_mul K A t)

@[simp] theorem toPresentation_baseMap (a : A) :
    toPresentation K A t (baseMap K A t a) = base K A t a :=
  liftFromBase_baseMap K t _ _ _ _ _ a

@[simp] theorem toPresentation_newCoordinate (j : Fin 2) :
    toPresentation K A t
      (Adjoin.newCoordinate K A (LaurentAnnulus.radii t) {relation K A t} j) =
        scalarTuple K A t j :=
  liftFromBase_newCoordinate K t _ _ _ _ _ j

/-- Evaluate extended-coefficient series at the original coordinates in the annulus. -/
def annulusEvaluation : BoundedAlgHom (CompletedGaussLaurent K t)
    (GeneralizedTateAlgebra A.polyradius (CompletedGaussLaurent K t)) (algebra K A t) :=
  evaluateHom A.polyradius (CompletedGaussLaurent K t) (algebra K A t)
    (fun i => baseMap K A t (coordinate K A i))
    (hasBoundedMonomials_coordinate K (algebra K A t) A (baseMap K A t))

/-- The same evaluation retaining the original scalar field. -/
def annulusEvaluationOverBase : BoundedAlgHom K
    (GeneralizedTateAlgebra A.polyradius (CompletedGaussLaurent K t)) (algebra K A t) where
  toAlgHom := (annulusEvaluation K A t).toAlgHom.restrictScalars K
  bounded := (annulusEvaluation K A t).bounded

theorem annulusEvaluation_comp_coefficients :
    (annulusEvaluationOverBase K A t).comp
      (mapCoefficientsAlgHom A.polyradius (coefficientMap K t)) =
        (baseMap K A t).comp (presentationMap K A) := by
  apply GeneralizedTateAlgebra.hom_ext
  intro i
  change annulusEvaluation K A t
    (mapCoefficients A.polyradius (coefficientMap K t).toBoundedRingHom
      (X A.polyradius K i)) = _
  rw [mapCoefficients_X]
  exact evaluate_X _ _ _ _ i

theorem annulusEvaluation_relations :
    ∀ f ∈ mapCoefficientsAlgHom A.polyradius (coefficientMap K t) '' A.ideal,
      annulusEvaluation K A t f = 0 := by
  rintro f ⟨g, hg, rfl⟩
  have h := congrArg (fun φ : BoundedAlgHom K (GeneralizedTateAlgebra A.polyradius K)
    (algebra K A t) => φ g) (annulusEvaluation_comp_coefficients K A t)
  change annulusEvaluation K A t _ = _ at h
  exact h.trans (by
    change baseMap K A t (presentationMap K A g) = 0
    rw [(presentationMap_eq_zero_iff K A g).mpr hg, map_zero])

/-- Evaluation descends through the closed extended relation ideal. -/
def fromPresentationOverExtension : BoundedAlgHom (CompletedGaussLaurent K t)
    (presentation K A t) (algebra K A t) :=
  descendRelations (CompletedGaussLaurent K t) A.arity A.polyradius
    (mapCoefficientsAlgHom A.polyradius (coefficientMap K t) '' A.ideal)
    (algebra K A t) (annulusEvaluation K A t) (annulusEvaluation_relations K A t)

/-- The inverse comparison also as an actual bounded `K`-algebra map. -/
def fromPresentation : BoundedAlgHom K (presentation K A t) (algebra K A t) where
  toAlgHom := (fromPresentationOverExtension K A t).toAlgHom.restrictScalars K
  bounded := (fromPresentationOverExtension K A t).bounded

@[simp] theorem fromPresentation_presentationMap
    (f : GeneralizedTateAlgebra A.polyradius (CompletedGaussLaurent K t)) :
    fromPresentation K A t
      (presentationMap (CompletedGaussLaurent K t) (presentation K A t) f) =
        annulusEvaluation K A t f := rfl

@[simp] theorem fromPresentation_base (a : A) :
    fromPresentation K A t (base K A t a) = baseMap K A t a := by
  obtain ⟨f, rfl⟩ := presentationMap_surjective K A a
  rw [base_presentationMap, fromPresentation_presentationMap]
  exact congrArg (fun φ : BoundedAlgHom K (GeneralizedTateAlgebra A.polyradius K)
    (algebra K A t) => φ f) (annulusEvaluation_comp_coefficients K A t)

@[simp] theorem fromPresentation_scalarInclusion (z : CompletedGaussLaurent K t) :
    fromPresentation K A t (scalarInclusion K A t z) = completedScalarMap K A t z :=
  (fromPresentationOverExtension K A t).toAlgHom.commutes z

omit [CompleteSpace K] in
@[simp] theorem base_coordinate (i : Fin A.arity) :
    base K A t (coordinate K A i) =
      coordinate (CompletedGaussLaurent K t) (presentation K A t) i := by
  change base K A t (presentationMap K A (X A.polyradius K i)) = _
  rw [base_presentationMap]
  exact congrArg (presentationMap (CompletedGaussLaurent K t) (presentation K A t))
    (mapCoefficients_X A.polyradius (coefficientMap K t).toBoundedRingHom i)

@[simp] theorem fromPresentation_coordinate (i : Fin A.arity) :
    fromPresentation K A t (coordinate (CompletedGaussLaurent K t) (presentation K A t) i) =
      baseMap K A t (coordinate K A i) :=
  evaluate_X _ _ _ _ i

theorem toPresentation_comp_completedScalarMap :
    (toPresentation K A t).comp (completedScalarMap K A t) = scalarInclusion K A t := by
  apply CompletedGaussLaurent.hom_ext
  change toPresentation K A t (completedScalarMap K A t CompletedGaussLaurent.X) = _
  rw [completedScalarMap_X, toPresentation_newCoordinate]
  rfl

@[simp] theorem toPresentation_completedScalarMap (z : CompletedGaussLaurent K t) :
    toPresentation K A t (completedScalarMap K A t z) = scalarInclusion K A t z :=
  congrArg (fun φ : BoundedAlgHom K (CompletedGaussLaurent K t) (presentation K A t) => φ z)
    (toPresentation_comp_completedScalarMap K A t)

/-- The forward comparison preserves the completed Laurent scalar field. -/
def toPresentationOverExtension : BoundedAlgHom (CompletedGaussLaurent K t)
    (algebra K A t) (presentation K A t) where
  toAlgHom :=
    { toRingHom := (toPresentation K A t).toAlgHom.toRingHom
      commutes' := toPresentation_completedScalarMap K A t }
  bounded := (toPresentation K A t).bounded

theorem fromPresentation_toPresentation (a : algebra K A t) :
    fromPresentation K A t (toPresentation K A t a) = a := by
  have h : (fromPresentation K A t).comp (toPresentation K A t) =
      BoundedAlgHom.id K (algebra K A t) := by
    apply hom_ext K t
    · intro a
      simp only [BoundedAlgHom.comp_apply, toPresentation_baseMap,
        fromPresentation_base, BoundedAlgHom.id_apply]
    · intro j
      simp only [BoundedAlgHom.comp_apply, toPresentation_newCoordinate,
        BoundedAlgHom.id_apply, scalarTuple, fromPresentation_scalarInclusion]
      fin_cases j
      · exact completedScalarMap_X K A t
      · exact completedScalarMap_invVariable K A t
  exact congrArg (fun φ : BoundedAlgHom K (algebra K A t) (algebra K A t) => φ a) h

theorem toPresentation_fromPresentation (a : presentation K A t) :
    toPresentation K A t (fromPresentation K A t a) = a := by
  have h : ((toPresentation K A t).comp (fromPresentation K A t)).comp
      (presentationMapOverBase K A t) = presentationMapOverBase K A t := by
    apply relative_hom_ext A.polyradius
    · intro z
      change toPresentation K A t (fromPresentation K A t (scalarInclusion K A t z)) =
        scalarInclusion K A t z
      rw [fromPresentation_scalarInclusion, toPresentation_completedScalarMap]
    · intro i
      change toPresentation K A t (fromPresentation K A t
        (coordinate (CompletedGaussLaurent K t) (presentation K A t) i)) = _
      rw [fromPresentation_coordinate, toPresentation_baseMap, base_coordinate]
      rfl
  obtain ⟨f, rfl⟩ := presentationMap_surjective (CompletedGaussLaurent K t) (presentation K A t) a
  exact congrArg (fun φ : BoundedAlgHom K
    (GeneralizedTateAlgebra A.polyradius (CompletedGaussLaurent K t))
      (presentation K A t) => φ f) h

/-- The actual annulus and coefficient-extended presentation are boundedly equivalent over `K`. -/
def boundedEquivOverBase : BoundedAlgEquiv K (algebra K A t) (presentation K A t) :=
  BoundedAlgEquiv.ofHomInv (toPresentation K A t) (fromPresentation K A t)
    (fromPresentation_toPresentation K A t) (toPresentation_fromPresentation K A t)

/-- The same actual equivalence over the independent completed Laurent field. -/
def boundedEquiv : BoundedAlgEquiv (CompletedGaussLaurent K t)
    (algebra K A t) (presentation K A t) :=
  BoundedAlgEquiv.ofHomInv (toPresentationOverExtension K A t)
    (fromPresentationOverExtension K A t)
    (fromPresentation_toPresentation K A t) (toPresentation_fromPresentation K A t)

end ScalarExtension
end Langlands.Analytic.RelativeLaurentAnnulus
