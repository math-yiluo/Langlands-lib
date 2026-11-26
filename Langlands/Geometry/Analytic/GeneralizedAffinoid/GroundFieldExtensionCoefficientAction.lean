import Langlands.Geometry.Analytic.GeneralizedAffinoid.GroundFieldExtensionTensor

/-! # Isometric coefficient automorphisms of scalar-extended affinoid algebras -/

noncomputable section

universe u v z

namespace Langlands.Analytic.PresentedAffinoidAlgebra.GroundFieldExtension

open CompletedTensorAlgebra
open scoped TensorProduct

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (L : Type v) [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L]

/-- The isometric field automorphisms of `L` fixing `K`. -/
def isometricAutomorphisms : Subgroup (L ≃ₐ[K] L) where
  carrier := {σ | ∀ c : L, ‖σ c‖ = ‖c‖}
  one_mem' _ := rfl
  mul_mem' {σ τ} hσ hτ c := (hσ (τ c)).trans (hτ c)
  inv_mem' {σ} hσ c := by
    change ‖σ.symm c‖ = ‖c‖
    simpa only [AlgEquiv.apply_symm_apply] using (hσ (σ.symm c)).symm

variable (A : PresentedAffinoidAlgebra K)

local notation "T" => CompletedTensorAlgebra.Algebra K A L
local notation "AL" => algebra K L A

private def fieldHom (σ : isometricAutomorphisms K L) : BoundedAlgHom K L L :=
  ⟨σ.val.toAlgHom, ⟨1, zero_lt_one, fun c => (σ.property c).le.trans_eq (one_mul _).symm⟩⟩

private def tensorOperator (σ : isometricAutomorphisms K L) : BoundedAlgHom K T T :=
  CompletedTensorAlgebra.lift (leftMap K A L) ((rightMap K A L).comp (fieldHom K L σ))

omit [IsUltrametricDist L] [CompleteSpace L] in
private theorem tensorOperator_left (σ : isometricAutomorphisms K L) (a : A) :
    tensorOperator K L A σ (leftMap K A L a) = leftMap K A L a := by
  exact congrArg (fun f : BoundedAlgHom K A T => f a)
    (lift_comp_leftMap (leftMap K A L) ((rightMap K A L).comp (fieldHom K L σ)))

omit [IsUltrametricDist L] [CompleteSpace L] in
private theorem tensorOperator_right (σ : isometricAutomorphisms K L) (c : L) :
    tensorOperator K L A σ (rightMap K A L c) = rightMap K A L (σ.val c) := by
  exact congrArg (fun f : BoundedAlgHom K L T => f c)
    (lift_comp_rightMap (leftMap K A L) ((rightMap K A L).comp (fieldHom K L σ)))

omit [IsUltrametricDist L] [CompleteSpace L] in
private theorem norm_tensorOperator_le (σ : isometricAutomorphisms K L) (t : T) :
    ‖tensorOperator K L A σ t‖ ≤ ‖t‖ := by
  change ‖CompletedTensorAlgebra.extensionRingHom (leftMap K A L)
    ((rightMap K A L).comp (fieldHom K L σ)) t‖ ≤ ‖t‖
  simpa only [one_mul] using
    CompletedTensorAlgebra.norm_extensionRingHom_le (leftMap K A L)
      ((rightMap K A L).comp (fieldHom K L σ)) 1 1 zero_lt_one zero_lt_one
      (fun a => (norm_leftMap_le_self K L A a).trans_eq (one_mul _).symm)
      (fun c => (norm_rightMap_le_self K L A (σ.val c)).trans_eq
        ((σ.property c).trans (one_mul _).symm)) t

/-- The bounded `K`-algebra map of `A_L` that fixes `A` and acts as `σ` on `L`. -/
def coefficientHom (σ : isometricAutomorphisms K L) : BoundedAlgHom K AL AL :=
  (fromTensor K L A).comp ((tensorOperator K L A σ).comp (toTensor K L A))

@[simp] theorem coefficientHom_iota (σ : isometricAutomorphisms K L) (a : A) :
    coefficientHom K L A σ (iota K L A a) = iota K L A a := by
  simp only [coefficientHom, BoundedAlgHom.comp_apply, toTensor_iota, tensorOperator_left,
    fromTensor_leftMap]

@[simp] theorem coefficientHom_scalar (σ : isometricAutomorphisms K L) (c : L) :
    coefficientHom K L A σ (scalarMap K L A c) = scalarMap K L A (σ.val c) := by
  simp only [coefficientHom, BoundedAlgHom.comp_apply, toTensor_scalarMap, tensorOperator_right,
    fromTensor_rightMap]

/-- The coefficient automorphism is semilinear for the action of `L` on `A_L`. -/
theorem coefficientHom_smul (σ : isometricAutomorphisms K L) (c : L) (a : AL) :
    coefficientHom K L A σ (c • a) = σ.val c • coefficientHom K L A σ a := by
  simp only [Algebra.smul_def]
  change coefficientHom K L A σ (scalarMap K L A c * a) =
    scalarMap K L A (σ.val c) * coefficientHom K L A σ a
  exact ((coefficientHom K L A σ).toAlgHom.map_mul _ _).trans
    (congrArg (· * coefficientHom K L A σ a) (coefficientHom_scalar K L A σ c))

/-- Bounded `K`-algebra maps out of `A_L` are determined by the two original tensor legs. -/
theorem hom_ext_over_base {E : Type*} [NormedCommRing E] [NormedAlgebra K E]
    {f g : BoundedAlgHom K AL E} (hi : ∀ a : A, f (iota K L A a) = g (iota K L A a))
    (hs : ∀ c : L, f (scalarMap K L A c) = g (scalarMap K L A c)) : f = g := by
  have h : f.comp (fromTensor K L A) = g.comp (fromTensor K L A) := by
    apply CompletedTensorAlgebra.hom_ext
    · ext a
      simpa only [BoundedAlgHom.comp_apply, fromTensor_leftMap] using hi a
    · ext c
      simpa only [BoundedAlgHom.comp_apply, fromTensor_rightMap] using hs c
  ext x
  have hx := congrArg (fun f : BoundedAlgHom K T E => f (toTensor K L A x)) h
  simpa only [BoundedAlgHom.comp_apply, fromTensor_toTensor] using hx

@[simp] theorem coefficientHom_one :
    coefficientHom K L A 1 = BoundedAlgHom.id K AL := by
  apply hom_ext_over_base
  · simp
  · intro c
    exact coefficientHom_scalar K L A 1 c

theorem coefficientHom_mul (σ τ : isometricAutomorphisms K L) :
    coefficientHom K L A (σ * τ) =
      (coefficientHom K L A σ).comp (coefficientHom K L A τ) := by
  apply hom_ext_over_base
  · simp
  · intro c
    simp only [coefficientHom_scalar, BoundedAlgHom.comp_apply]
    rfl

/-- The bounded automorphism of the actual affinoid algebra after scalar extension. -/
def coefficientAutomorphism (σ : isometricAutomorphisms K L) : BoundedAlgEquiv K AL AL :=
  BoundedAlgEquiv.ofHomInv (coefficientHom K L A σ) (coefficientHom K L A σ⁻¹)
    (fun x => by rw [← BoundedAlgHom.comp_apply, ← coefficientHom_mul, inv_mul_cancel,
      coefficientHom_one, BoundedAlgHom.id_apply])
    (fun x => by rw [← BoundedAlgHom.comp_apply, ← coefficientHom_mul, mul_inv_cancel,
      coefficientHom_one, BoundedAlgHom.id_apply])

/-- The coefficient action on `A_L`, with semilinearity over `L` given by its formula
on the scalar leg. -/
def coefficientAction :
    isometricAutomorphisms K L →* (AL ≃ₐ[K] AL) where
  toFun σ := (coefficientAutomorphism K L A σ).toAlgEquiv
  map_one' := by
    ext x
    exact congrArg (fun f : BoundedAlgHom K AL AL => f x) (coefficientHom_one K L A)
  map_mul' σ τ := by
    ext x
    exact congrArg (fun f : BoundedAlgHom K AL AL => f x) (coefficientHom_mul K L A σ τ)

/-- Coefficient actions commute with every scalar-extended bounded chart map. -/
theorem coefficientHom_natural {A B : PresentedAffinoidAlgebra K}
    (σ : isometricAutomorphisms K L) (f : BoundedAlgHom K A B) :
    (overBase K L (map K L f)).comp (coefficientHom K L A σ) =
      (coefficientHom K L B σ).comp (overBase K L (map K L f)) := by
  have hscalar (c : L) : map K L f (scalarMap K L A c) = scalarMap K L B c :=
    (map K L f).toAlgHom.commutes c
  apply hom_ext_over_base
  · intro a
    simp only [BoundedAlgHom.comp_apply, coefficientHom_iota, overBase_apply, map_iota]
  · intro c
    simp only [BoundedAlgHom.comp_apply, coefficientHom_scalar, overBase_apply, hscalar]

variable {G : Type z} [Group G] [TopologicalSpace G]

omit [IsUltrametricDist L] [CompleteSpace L] in
private theorem continuous_tensorOrbit (σ : G →* isometricAutomorphisms K L)
    (hσ : ∀ c : L, Continuous (fun g : G => (σ g).val c)) (t : T) :
    Continuous (fun g : G => tensorOperator K L A (σ g) t) := by
  have halg (r : Algebraic K A L) :
      Continuous (fun g : G => tensorOperator K L A (σ g) (toCompletion K A L r)) := by
    induction r using TensorProduct.inductionOn with
    | tmul a c =>
      rw [show (a ⊗ₜ[K] c : A ⊗[K] L) = (a ⊗ₜ[K] c : Algebraic K A L) from rfl,
        toCompletion_tmul]
      simp only [map_mul, tensorOperator_left, tensorOperator_right]
      exact continuous_const.mul ((rightMap K A L).continuous.comp (hσ c))
    | add r s hr hs =>
      have he : (fun g : G => tensorOperator K L A (σ g) (toCompletion K A L (r + s))) =
          (fun g : G => tensorOperator K L A (σ g) (toCompletion K A L r) +
            tensorOperator K L A (σ g) (toCompletion K A L s)) := by
        funext g
        exact ((tensorOperator K L A (σ g)).toAlgHom.comp (toCompletion K A L)).map_add r s
      exact he.symm ▸ hr.add hs
  have hdist (g : G) (a b : T) :
      dist (tensorOperator K L A (σ g) a) (tensorOperator K L A (σ g) b) ≤ dist a b := by
    rw [dist_eq_norm, ← map_sub, dist_eq_norm]
    exact norm_tensorOperator_le K L A (σ g) (a - b)
  apply continuous_iff_continuousAt.mpr
  intro g
  apply Metric.continuousAt_iff'.mpr
  intro ε hε
  have hthird : 0 < ε / 3 := by positivity
  obtain ⟨r, hr⟩ := (denseRange_toCompletion K A L).exists_dist_lt t hthird
  let s := toCompletion K A L r
  filter_upwards [Metric.continuousAt_iff'.mp (halg r).continuousAt (ε / 3) hthird] with a ha
  exact (dist_triangle4 _ (tensorOperator K L A (σ a) s)
    (tensorOperator K L A (σ g) s) _).trans_lt (by
      have h₁ := (hdist a t s).trans_lt hr
      have h₂ := (hdist g s t).trans_lt ((dist_comm s t).trans_lt hr)
      linarith)

/-- Pointwise norm-continuity of field automorphisms gives norm-continuity
on the scalar-extended affinoid algebra. -/
theorem continuous_coefficientOrbit (σ : G →* isometricAutomorphisms K L)
    (hσ : ∀ c : L, Continuous (fun g : G => (σ g).val c)) (x : AL) :
    Continuous (fun g : G => coefficientAction K L A (σ g) x) :=
  (fromTensor K L A).continuous.comp (continuous_tensorOrbit K L A σ hσ (toTensor K L A x))

end Langlands.Analytic.PresentedAffinoidAlgebra.GroundFieldExtension
