import Langlands.Global.ArchimedeanAdjoint
import Langlands.Global.ArchimedeanSplitCenter
import Langlands.Global.ArchimedeanCompact

/-! # Adjoint automorphisms of the actual reduced and compact Lie algebras -/

noncomputable section

universe u

open scoped TensorProduct Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] (n : ℕ)

@[simp]
theorem realTrace_realLieConjugation (g : InfiniteAdelicGL K n)
    (X : RealLieAlgebra K n) :
    realTrace K n (realLieConjugation K n g X) = realTrace K n X := by
  simp only [realTrace_apply, realLieAlgebraToMatrix_realLieConjugation,
    map_inv, Matrix.trace_units_conj]

/-- Restrict actual conjugation to the real split-center complement. -/
def reducedRealLieConjugation (g : InfiniteAdelicGL K n) :
    reducedLieSubalgebra K n ≃ₗ⁅ℝ⁆ reducedLieSubalgebra K n where
  toFun X := ⟨realLieConjugation K n g X, by
    simpa only [mem_reducedLieSubalgebra, realTrace_realLieConjugation] using X.property⟩
  invFun X := ⟨realLieConjugation K n g⁻¹ X, by
    simpa only [mem_reducedLieSubalgebra, realTrace_realLieConjugation] using X.property⟩
  left_inv X := Subtype.ext (by simp)
  right_inv X := Subtype.ext (by simp)
  map_add' X Y := Subtype.ext (map_add (realLieConjugation K n g) X.val Y.val)
  map_smul' r X := Subtype.ext (map_smul (realLieConjugation K n g) r X.val)
  map_lie' := by
    intro X Y
    apply Subtype.ext
    exact (realLieConjugation K n g).map_lie X.val Y.val

@[simp]
theorem reducedRealLieConjugation_coe (g : InfiniteAdelicGL K n)
    (X : reducedLieSubalgebra K n) :
    (reducedRealLieConjugation K n g X : RealLieAlgebra K n) =
      realLieConjugation K n g X := rfl

@[simp]
theorem reducedRealLieConjugation_one :
    reducedRealLieConjugation K n 1 = LieEquiv.refl := by
  ext X
  simp

theorem reducedRealLieConjugation_mul (g h : InfiniteAdelicGL K n) :
    reducedRealLieConjugation K n (g * h) =
      (reducedRealLieConjugation K n h).trans (reducedRealLieConjugation K n g) := by
  apply LieEquiv.ext
  intro X
  apply Subtype.ext
  exact congrArg (fun e => e (X : RealLieAlgebra K n)) (realLieConjugation_mul K n g h)

@[simp]
theorem reducedRealLieConjugation_inv (g : InfiniteAdelicGL K n) :
    reducedRealLieConjugation K n g⁻¹ = (reducedRealLieConjugation K n g).symm := by
  apply LieEquiv.ext
  intro X
  rfl

/-- Complexification of the actual reduced conjugation. -/
def reducedComplexLieConjugation (g : InfiniteAdelicGL K n) :
    ReducedComplexLieAlgebra K n ≃ₗ⁅ℂ⁆ ReducedComplexLieAlgebra K n :=
  { (reducedRealLieConjugation K n g).toLinearEquiv.baseChange ℝ ℂ _ _ with
    map_lie' := by
      intro X Y
      exact (LieAlgebra.ExtendScalars.map (AlgHom.id ℝ ℂ)
        (reducedRealLieConjugation K n g).toLieHom).map_lie X Y }

@[simp]
theorem reducedComplexLieConjugation_tmul (g : InfiniteAdelicGL K n)
    (z : ℂ) (X : reducedLieSubalgebra K n) :
    reducedComplexLieConjugation K n g (z ⊗ₜ[ℝ] X) =
      z ⊗ₜ[ℝ] reducedRealLieConjugation K n g X := rfl

theorem reducedComplexInclusion_conjugation (g : InfiniteAdelicGL K n)
    (X : ReducedComplexLieAlgebra K n) :
    reducedComplexInclusion K n (reducedComplexLieConjugation K n g X) =
      complexLieConjugation K n g (reducedComplexInclusion K n X) := by
  induction X using TensorProduct.inductionOn with
  | tmul z X => rfl
  | add X Y hX hY => simp only [map_add, hX, hY]

@[simp]
theorem reducedComplexLieConjugation_one :
    reducedComplexLieConjugation K n 1 = LieEquiv.refl := by
  apply LieEquiv.ext
  intro X
  apply reducedComplexInclusion_injective K n
  simp [reducedComplexInclusion_conjugation]

theorem reducedComplexLieConjugation_mul (g h : InfiniteAdelicGL K n) :
    reducedComplexLieConjugation K n (g * h) =
      (reducedComplexLieConjugation K n h).trans
        (reducedComplexLieConjugation K n g) := by
  apply LieEquiv.ext
  intro X
  apply reducedComplexInclusion_injective K n
  simp only [reducedComplexInclusion_conjugation, LieEquiv.trans_apply,
    complexLieConjugation_mul]

@[simp]
theorem reducedComplexLieConjugation_inv (g : InfiniteAdelicGL K n) :
    reducedComplexLieConjugation K n g⁻¹ =
      (reducedComplexLieConjugation K n g).symm := by
  apply LieEquiv.ext
  intro X
  apply (reducedComplexLieConjugation K n g).injective
  have h := congrArg (fun e : ReducedComplexLieAlgebra K n ≃ₗ⁅ℂ⁆
    ReducedComplexLieAlgebra K n => e X) (reducedComplexLieConjugation_mul K n g g⁻¹)
  simpa using h.symm

/-- In mixed coordinates the inverse of a standard compact matrix is its star. -/
theorem standardCompact_coordinates_star (k : standardInfiniteCompact K n) :
    star (archimedeanGLCoordinates K n k.val).val =
      (archimedeanGLCoordinates K n k.val)⁻¹.val := by
  obtain ⟨p, hp⟩ := k.property
  have he : archimedeanGLCoordinates K n k.val =
      ArchimedeanCompactFactors.toArchimedeanGL K n p := by
    rw [← hp]
    exact ArchimedeanCompactFactors.coordinates_toInfiniteAdelicGL K n p
  rw [he]
  apply Matrix.ext
  intro i j
  apply Prod.ext
  · funext v
    rfl
  · funext v
    rfl

/-- Compact conjugation commutes with the actual matrix star. -/
theorem realLieConjugation_star (k : standardInfiniteCompact K n)
    (X : RealLieAlgebra K n) :
    realLieConjugation K n k.val (star X) =
      star (realLieConjugation K n k.val X) := by
  apply (realLieAlgebraToMatrix K n).injective
  change realLieAlgebraToMatrix K n (realLieConjugation K n k.val (star X)) =
    star (realLieAlgebraToMatrix K n (realLieConjugation K n k.val X))
  rw [realLieAlgebraToMatrix_realLieConjugation,
    realLieAlgebraToMatrix_realLieConjugation]
  have hk := standardCompact_coordinates_star K n k
  have hki := standardCompact_coordinates_star K n k⁻¹
  simp only [Subgroup.coe_inv, map_inv, inv_inv] at hki
  change (archimedeanGLCoordinates K n k.val).val *
    star (realLieAlgebraToMatrix K n X) * (archimedeanGLCoordinates K n k.val)⁻¹.val =
      star ((archimedeanGLCoordinates K n k.val).val *
        realLieAlgebraToMatrix K n X * (archimedeanGLCoordinates K n k.val)⁻¹.val)
  simp only [star_mul, hk, hki, mul_assoc]

theorem realLieConjugation_mem_compact (k : standardInfiniteCompact K n)
    (X : compactLieSubalgebra K n) :
    realLieConjugation K n k.val X ∈ compactLieSubalgebra K n := by
  rw [mem_compactLieSubalgebra, ← realLieConjugation_star]
  rw [(mem_compactLieSubalgebra K n X).mp X.property, map_neg]

/-- The full standard compact group acts by real Lie automorphisms of its algebra. -/
def compactRealLieConjugation (k : standardInfiniteCompact K n) :
    compactLieSubalgebra K n ≃ₗ⁅ℝ⁆ compactLieSubalgebra K n where
  toFun X := ⟨realLieConjugation K n k.val X, realLieConjugation_mem_compact K n k X⟩
  invFun X := ⟨realLieConjugation K n k⁻¹.val X, realLieConjugation_mem_compact K n k⁻¹ X⟩
  left_inv X := Subtype.ext (by simp)
  right_inv X := Subtype.ext (by simp)
  map_add' X Y := Subtype.ext (map_add (realLieConjugation K n k.val) X.val Y.val)
  map_smul' r X := Subtype.ext (map_smul (realLieConjugation K n k.val) r X.val)
  map_lie' := by
    intro X Y
    apply Subtype.ext
    exact (realLieConjugation K n k.val).map_lie X.val Y.val

@[simp]
theorem compactRealLieConjugation_coe (k : standardInfiniteCompact K n)
    (X : compactLieSubalgebra K n) :
    (compactRealLieConjugation K n k X : RealLieAlgebra K n) =
      realLieConjugation K n k.val X := rfl

@[simp]
theorem compactRealLieConjugation_one :
    compactRealLieConjugation K n 1 = LieEquiv.refl := by
  ext X
  simp

theorem compactRealLieConjugation_mul (k l : standardInfiniteCompact K n) :
    compactRealLieConjugation K n (k * l) =
      (compactRealLieConjugation K n l).trans (compactRealLieConjugation K n k) := by
  apply LieEquiv.ext
  intro X
  apply Subtype.ext
  exact congrArg (fun e => e (X : RealLieAlgebra K n))
    (realLieConjugation_mul K n k.val l.val)

@[simp]
theorem compactRealLieConjugation_inv (k : standardInfiniteCompact K n) :
    compactRealLieConjugation K n k⁻¹ = (compactRealLieConjugation K n k).symm := by
  apply LieEquiv.ext
  intro X
  rfl

/-- Complexify the actual compact adjoint action. -/
def compactComplexLieConjugation (k : standardInfiniteCompact K n) :
    CompactComplexLieAlgebra K n ≃ₗ⁅ℂ⁆ CompactComplexLieAlgebra K n :=
  { (compactRealLieConjugation K n k).toLinearEquiv.baseChange ℝ ℂ _ _ with
    map_lie' := by
      intro X Y
      exact (LieAlgebra.ExtendScalars.map (AlgHom.id ℝ ℂ)
        (compactRealLieConjugation K n k).toLieHom).map_lie X Y }

@[simp]
theorem compactComplexLieConjugation_tmul (k : standardInfiniteCompact K n)
    (z : ℂ) (X : compactLieSubalgebra K n) :
    compactComplexLieConjugation K n k (z ⊗ₜ[ℝ] X) =
      z ⊗ₜ[ℝ] compactRealLieConjugation K n k X := rfl

theorem compactComplexInclusion_conjugation (k : standardInfiniteCompact K n)
    (X : CompactComplexLieAlgebra K n) :
    compactComplexInclusion K n (compactComplexLieConjugation K n k X) =
      complexLieConjugation K n k.val (compactComplexInclusion K n X) := by
  induction X using TensorProduct.inductionOn with
  | tmul z X => rfl
  | add X Y hX hY => simp only [map_add, hX, hY]

@[simp]
theorem compactComplexLieConjugation_one :
    compactComplexLieConjugation K n 1 = LieEquiv.refl := by
  apply LieEquiv.ext
  intro X
  apply compactComplexInclusion_injective K n
  simp [compactComplexInclusion_conjugation]

theorem compactComplexLieConjugation_mul (k l : standardInfiniteCompact K n) :
    compactComplexLieConjugation K n (k * l) =
      (compactComplexLieConjugation K n l).trans
        (compactComplexLieConjugation K n k) := by
  apply LieEquiv.ext
  intro X
  apply compactComplexInclusion_injective K n
  simp only [compactComplexInclusion_conjugation, LieEquiv.trans_apply,
    Subgroup.coe_mul, complexLieConjugation_mul]

@[simp]
theorem compactComplexLieConjugation_inv (k : standardInfiniteCompact K n) :
    compactComplexLieConjugation K n k⁻¹ =
      (compactComplexLieConjugation K n k).symm := by
  apply LieEquiv.ext
  intro X
  apply (compactComplexLieConjugation K n k).injective
  have h := congrArg (fun e : CompactComplexLieAlgebra K n ≃ₗ⁅ℂ⁆
    CompactComplexLieAlgebra K n => e X) (compactComplexLieConjugation_mul K n k k⁻¹)
  simpa using h.symm

theorem compactToReducedComplex_conjugation (k : standardInfiniteCompact K n)
    (X : CompactComplexLieAlgebra K n) :
    compactToReducedComplex K n (compactComplexLieConjugation K n k X) =
      reducedComplexLieConjugation K n k.val (compactToReducedComplex K n X) := by
  apply reducedComplexInclusion_injective K n
  rw [reducedComplexInclusion_compact, compactComplexInclusion_conjugation,
    reducedComplexInclusion_conjugation, reducedComplexInclusion_compact]

end Langlands.Global.ArchimedeanGL
