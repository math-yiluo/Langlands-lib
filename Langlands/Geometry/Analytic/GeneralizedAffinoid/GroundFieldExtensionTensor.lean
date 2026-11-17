import Langlands.Geometry.Analytic.GeneralizedAffinoid.GroundFieldExtension
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeSeriesMap
import Langlands.Geometry.Analytic.GeneralizedTateAlgebra.RelativeEvaluation
import Langlands.Geometry.Analytic.CompletedTensorUniversal

/-! # The ground field extension is the completed tensor product -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.GroundFieldExtension

open GeneralizedTateAlgebra CompletedTensorAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (L : Type v) [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L]
  (A : PresentedAffinoidAlgebra K)

/-- The comparison map from the completed tensor product `A ⊗̂_K L` to `A_L`,
induced by `ι : A → A_L` and the scalar inclusion `L → A_L`. -/
def fromTensor : BoundedAlgHom K (CompletedTensorAlgebra.Algebra K A L) (algebra K L A) :=
  CompletedTensorAlgebra.lift (iota K L A) (scalarMap K L A)

@[simp] theorem fromTensor_leftMap (a : A) :
    fromTensor K L A (leftMap K A L a) = iota K L A a :=
  congrArg (fun φ : BoundedAlgHom K A (algebra K L A) => φ a)
    (lift_comp_leftMap (iota K L A) (scalarMap K L A))

@[simp] theorem fromTensor_rightMap (c : L) :
    fromTensor K L A (rightMap K A L c) = scalarMap K L A c :=
  congrArg (fun φ : BoundedAlgHom K L (algebra K L A) => φ c)
    (lift_comp_rightMap (iota K L A) (scalarMap K L A))

omit [IsUltrametricDist L] [CompleteSpace L] in
/-- The second leg of the completed tensor product is contractive. -/
theorem norm_rightMap_le_self (c : L) : ‖rightMap K A L c‖ ≤ ‖c‖ :=
  (norm_rightMap_le K A L c).trans
    (mul_le_of_le_one_left (norm_nonneg c) (norm_one_le K A))

omit [IsUltrametricDist L] [CompleteSpace L] in
/-- The first leg of the completed tensor product is contractive. -/
theorem norm_leftMap_le_self (a : A) : ‖leftMap K A L a‖ ≤ ‖a‖ :=
  (norm_leftMap_le K A L a).trans_eq (by rw [norm_one, mul_one])

omit [IsUltrametricDist L] [CompleteSpace L] in
theorem norm_one_tensor_le : ‖(1 : CompletedTensorAlgebra.Algebra K A L)‖ ≤ 1 := by
  have h := norm_leftMap_le_self K L A 1
  rw [map_one (leftMap K A L).toAlgHom] at h
  exact h.trans (norm_one_le K A)

/-- The images in `A ⊗̂_K L` of the presentation coordinates of `A`. -/
def tensorTuple : Fin A.arity → CompletedTensorAlgebra.Algebra K A L :=
  fun i => leftMap K A L (coordinate K A i)

omit [IsUltrametricDist L] [CompleteSpace L] in
theorem tensorTuple_monomial_le (d : Fin A.arity →₀ ℕ) :
    ‖StrictTateAlgebra.monomialValue (Fin A.arity) (CompletedTensorAlgebra.Algebra K A L)
      (tensorTuple K L A) d‖ ≤ A.polyradius.weight d :=
  monomialValue_norm_le_weight A.polyradius _ (norm_one_tensor_le K L A) _
    (fun i => (norm_leftMap_le_self K L A _).trans (norm_coordinate_le K A i)) d

/-- Evaluation of weighted series over `L` in `A ⊗̂_K L`: coefficients go
through the second leg and variables to the first-leg images of the
coordinates of `A`. -/
def tensorEvaluation :
    BoundedAlgHom K (GeneralizedTateAlgebra A.polyradius L)
      (CompletedTensorAlgebra.Algebra K A L) :=
  evaluateCoefficientsHom A.polyradius (rightMap K A L) (tensorTuple K L A)
    (norm_rightMap_le_self K L A) (tensorTuple_monomial_le K L A)

omit [CompleteSpace L] in
@[simp] theorem tensorEvaluation_constant (c : L) :
    tensorEvaluation K L A (constantAlgHom A.polyradius K L c) = rightMap K A L c :=
  evaluateCoefficients_constant A.polyradius (rightMap K A L) (tensorTuple K L A) c

omit [CompleteSpace L] in
@[simp] theorem tensorEvaluation_X (i : Fin A.arity) :
    tensorEvaluation K L A (X A.polyradius L i) = leftMap K A L (coordinate K A i) :=
  evaluateCoefficients_X A.polyradius (rightMap K A L) (tensorTuple K L A) i

omit [CompleteSpace L] in
theorem tensorEvaluation_comp_coefficients :
    (tensorEvaluation K L A).comp (mapCoefficientsAlgHom A.polyradius (coefficientMap K L)) =
      (leftMap K A L).comp (presentationMap K A) := by
  apply GeneralizedTateAlgebra.hom_ext A.polyradius K
  intro i
  change tensorEvaluation K L A
    (mapCoefficients A.polyradius (coefficientMap K L).toBoundedRingHom
      (X A.polyradius K i)) = leftMap K A L (coordinate K A i)
  rw [mapCoefficients_X]
  exact tensorEvaluation_X K L A i

omit [CompleteSpace L] in
theorem tensorEvaluation_relations :
    ∀ f ∈ relations K L A, tensorEvaluation K L A f = 0 := by
  rintro f ⟨g, hg, rfl⟩
  have h := congrArg (fun φ : BoundedAlgHom K (GeneralizedTateAlgebra A.polyradius K)
    (CompletedTensorAlgebra.Algebra K A L) => φ g) (tensorEvaluation_comp_coefficients K L A)
  change tensorEvaluation K L A _ = leftMap K A L (presentationMap K A g) at h
  refine h.trans ?_
  rw [(presentationMap_eq_zero_iff K A g).mpr hg]
  exact map_zero (leftMap K A L).toAlgHom

omit [CompleteSpace L] in
theorem tensorEvaluation_ideal :
    ∀ f ∈ (algebra K L A).ideal, tensorEvaluation K L A f = 0 := by
  have hspan : ∀ f ∈ Ideal.span (relations K L A), tensorEvaluation K L A f = 0 :=
    (Ideal.span_le.mpr (tensorEvaluation_relations K L A) :
      Ideal.span (relations K L A) ≤ RingHom.ker (tensorEvaluation K L A).toAlgHom.toRingHom)
  exact (tensorEvaluation K L A).annihilates_closure _ hspan

/-- The underlying ring map `A_L → A ⊗̂_K L`, descended from `tensorEvaluation`. -/
def toTensorRingHom : algebra K L A →+* CompletedTensorAlgebra.Algebra K A L := by
  let _ := (algebra K L A).ideal_closed
  exact Ideal.Quotient.lift (algebra K L A).ideal
    (tensorEvaluation K L A).toAlgHom.toRingHom (tensorEvaluation_ideal K L A)

omit [CompleteSpace L] in
@[simp] theorem toTensorRingHom_presentationMap (f : GeneralizedTateAlgebra A.polyradius L) :
    toTensorRingHom K L A (presentationMap L (algebra K L A) f) = tensorEvaluation K L A f :=
  rfl

/-- The inverse comparison map `A_L → A ⊗̂_K L`, a bounded `K`-algebra map. -/
def toTensor : BoundedAlgHom K (algebra K L A) (CompletedTensorAlgebra.Algebra K A L) where
  toAlgHom :=
    { toRingHom := toTensorRingHom K L A
      commutes' := fun c => by
        change tensorEvaluation K L A
          (constantAlgHom A.polyradius K L (algebraMap K L c)) = _
        rw [tensorEvaluation_constant]
        exact (rightMap K A L).toAlgHom.commutes c }
  bounded := ⟨1, zero_lt_one, by
    let _ := (algebra K L A).ideal_closed
    exact BoundedAlgHom.quotient_norm_bound (algebra K L A).ideal (toTensorRingHom K L A) 1
      zero_lt_one (fun f => by
        change ‖tensorEvaluation K L A f‖ ≤ 1 * ‖f‖
        rw [one_mul]
        exact norm_evaluateCoefficients_le A.polyradius (rightMap K A L) (tensorTuple K L A)
          (norm_rightMap_le_self K L A) (tensorTuple_monomial_le K L A) f)⟩

omit [CompleteSpace L] in
@[simp] theorem toTensor_presentationMap (f : GeneralizedTateAlgebra A.polyradius L) :
    toTensor K L A (presentationMap L (algebra K L A) f) = tensorEvaluation K L A f :=
  rfl

omit [CompleteSpace L] in
@[simp] theorem toTensor_iota (a : A) : toTensor K L A (iota K L A a) = leftMap K A L a := by
  obtain ⟨f, rfl⟩ := presentationMap_surjective K A a
  rw [iota_presentationMap, toTensor_presentationMap]
  exact congrArg (fun φ : BoundedAlgHom K (GeneralizedTateAlgebra A.polyradius K)
    (CompletedTensorAlgebra.Algebra K A L) => φ f) (tensorEvaluation_comp_coefficients K L A)

omit [CompleteSpace L] in
@[simp] theorem toTensor_scalarMap (c : L) :
    toTensor K L A (scalarMap K L A c) = rightMap K A L c :=
  tensorEvaluation_constant K L A c

theorem toTensor_fromTensor (t : CompletedTensorAlgebra.Algebra K A L) :
    toTensor K L A (fromTensor K L A t) = t := by
  have h : (toTensor K L A).comp (fromTensor K L A) =
      BoundedAlgHom.id K (CompletedTensorAlgebra.Algebra K A L) := by
    apply CompletedTensorAlgebra.hom_ext
    · apply BoundedAlgHom.ext
      intro a
      simp only [BoundedAlgHom.comp_apply, fromTensor_leftMap, toTensor_iota,
        BoundedAlgHom.id_apply]
    · apply BoundedAlgHom.ext
      intro c
      simp only [BoundedAlgHom.comp_apply, fromTensor_rightMap, toTensor_scalarMap,
        BoundedAlgHom.id_apply]
  exact congrArg (fun φ : BoundedAlgHom K (CompletedTensorAlgebra.Algebra K A L)
    (CompletedTensorAlgebra.Algebra K A L) => φ t) h

theorem fromTensor_toTensor (x : algebra K L A) :
    fromTensor K L A (toTensor K L A x) = x := by
  have h : ((fromTensor K L A).comp (toTensor K L A)).comp (presentationMapOverBase K L A) =
      presentationMapOverBase K L A := by
    apply relative_hom_ext A.polyradius
    · intro c
      change fromTensor K L A (toTensor K L A (scalarMap K L A c)) = scalarMap K L A c
      rw [toTensor_scalarMap, fromTensor_rightMap]
    · intro (i : Fin A.arity)
      change fromTensor K L A (toTensor K L A (coordinate L (algebra K L A) i)) =
        coordinate L (algebra K L A) i
      rw [← iota_coordinate, toTensor_iota, fromTensor_leftMap]
  obtain ⟨f, rfl⟩ := presentationMap_surjective L (algebra K L A) x
  exact congrArg (fun φ : BoundedAlgHom K (GeneralizedTateAlgebra A.polyradius L)
    (algebra K L A) => φ f) h

/-- The ground field extension `A_L` is boundedly `K`-isomorphic to the actual
projective completed tensor product `A ⊗̂_K L`. -/
def tensorEquiv :
    BoundedAlgEquiv K (CompletedTensorAlgebra.Algebra K A L) (algebra K L A) :=
  BoundedAlgEquiv.ofHomInv (fromTensor K L A) (toTensor K L A)
    (toTensor_fromTensor K L A) (fromTensor_toTensor K L A)

@[simp] theorem tensorEquiv_apply (t : CompletedTensorAlgebra.Algebra K A L) :
    tensorEquiv K L A t = fromTensor K L A t := rfl

@[simp] theorem tensorEquiv_symm_apply (x : algebra K L A) :
    (tensorEquiv K L A).toAlgEquiv.symm x = toTensor K L A x := rfl

/-- The comparison is compatible with the first legs: `a ⊗ 1 ↦ ι a`. -/
theorem tensorEquiv_leftMap (a : A) :
    tensorEquiv K L A (leftMap K A L a) = iota K L A a :=
  fromTensor_leftMap K L A a

/-- The comparison is compatible with the second legs: `1 ⊗ c ↦ c · 1`. -/
theorem tensorEquiv_rightMap (c : L) :
    tensorEquiv K L A (rightMap K A L c) = algebraMap L (algebra K L A) c :=
  fromTensor_rightMap K L A c

end Langlands.Analytic.PresentedAffinoidAlgebra.GroundFieldExtension
