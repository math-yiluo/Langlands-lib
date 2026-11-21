import Langlands.Global.RankinSelberg.InfiniteWhittakerSliceProduct
import Langlands.Global.ArchimedeanCompactComponentCoverageProof
import Langlands.Global.ArchimedeanAnalyticJetProof

/-! # Matrix coordinates for a single varying infinite place -/

noncomputable section
open NumberField
open scoped Classical TensorProduct Matrix.Norms.Operator ContDiff Manifold Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

universe u

namespace Langlands.Global.RankinSelbergGlobal.InfiniteWhittakerSlice

open ArchimedeanGL Langlands.Automorphic.InfinitePlaceFamily

attribute [local instance 100] LieRing.ofAssociativeRing

variable {F : Type u} [Field F] [NumberField F] (n : ℕ)

local notation "M" => ArchimedeanMatrix F n
local notation "G" => ArchimedeanGL F n
local notation "L" => RealLieAlgebra F n

private abbrev PlaceMatrix (n : ℕ) : Index F → Type
  | .inl _ => Matrix (Fin n) (Fin n) ℝ
  | .inr _ => Matrix (Fin n) (Fin n) ℂ

private instance (i : Index F) : Ring (PlaceMatrix n i) := by
  cases i <;> infer_instance

private instance (i : Index F) : Algebra ℝ (PlaceMatrix n i) := by
  cases i <;> infer_instance

private def matrixCoordinate : (i : Index F) → M →ₐ[ℝ] PlaceMatrix n i
  | .inl v => (realPlaceScalarProjection F v).mapMatrix
  | .inr w => (complexPlaceScalarProjection F w).mapMatrix

private def lieInclude : (i : Index F) → PlaceMatrix n i →ₗ[ℝ] L
  | .inl v => (realPlaceLieInclusion F n v).toLinearMap
  | .inr w => (complexPlaceLieInclusion F n w).toLinearMap

private theorem matrix_ext {a b : M}
    (h : ∀ i, matrixCoordinate n i a = matrixCoordinate n i b) : a = b := by
  apply Matrix.ext
  intro k l
  exact Prod.ext (funext fun v => congrFun (congrFun (h (.inl v)) k) l)
    (funext fun w => congrFun (congrFun (h (.inr w)) k) l)

private def matrixMask (i : Index F) : M →ₗ[ℝ] M :=
  (realLieAlgebraToMatrix F n).toLinearMap.comp
    ((lieInclude n i).comp (matrixCoordinate n i).toLinearMap)

private theorem matrixMask_same (i : Index F) (a : M) :
    matrixCoordinate n i (matrixMask n i a) = matrixCoordinate n i a := by
  cases i with
  | inl v =>
    change realPlaceLieProjection F n v
      (realPlaceLieInclusion F n v (matrixCoordinate n (.inl v) a)) = _
    rw [realProjection_realInclusion, Pi.single_eq_same]
  | inr w =>
    change complexPlaceLieProjection F n w
      (complexPlaceLieInclusion F n w (matrixCoordinate n (.inr w) a)) = _
    rw [complexProjection_complexInclusion, Pi.single_eq_same]

private theorem matrixMask_other {i j : Index F} (h : j ≠ i) (a : M) :
    matrixCoordinate n j (matrixMask n i a) = 0 := by
  cases i with
  | inl v =>
    cases j with
    | inl w =>
      change realPlaceLieProjection F n w
        (realPlaceLieInclusion F n v (matrixCoordinate n (.inl v) a)) = 0
      rw [realProjection_realInclusion, Pi.single_eq_of_ne (fun he => h (congrArg Sum.inl he))]
    | inr w => exact complexProjection_realInclusion F n w v (matrixCoordinate n (.inl v) a)
  | inr v =>
    cases j with
    | inl w => exact realProjection_complexInclusion F n w v (matrixCoordinate n (.inr v) a)
    | inr w =>
      change complexPlaceLieProjection F n w
        (complexPlaceLieInclusion F n v (matrixCoordinate n (.inr v) a)) = 0
      rw [complexProjection_complexInclusion, Pi.single_eq_of_ne (fun he => h (congrArg Sum.inr he))]

private def realComplexify : (i : Index F) → PlaceMatrix n i → Lie n i
  | .inl _ => fun X => (1 : ℂ) ⊗ₜ[ℝ] X
  | .inr _ => fun X => (1 : ℂ) ⊗ₜ[ℝ] X

/-- The actual local complexified generator coming from a real mixed-matrix direction. -/
def placeGenerator (i : Index F) (X : L) : Lie n i :=
  realComplexify n i (matrixCoordinate n i (realLieAlgebraToMatrix F n X))

/-- Keep the real Lie direction at the selected place. -/
def supportedDirection (i : Index F) (X : L) : L :=
  lieInclude n i (matrixCoordinate n i (realLieAlgebraToMatrix F n X))

theorem lieInclusion_placeGenerator (i : Index F) (X : L) :
    lieInclusion n i (placeGenerator n i X) = complexify F n (supportedDirection n i X) := by
  cases i <;>
    simp only [lieInclusion, placeGenerator, supportedDirection, realComplexify, lieInclude,
      realPlaceComplexLieInclusion_tmul, complexPlaceComplexLieInclusion_tmul, complexify_apply,
      LieHom.coe_toLinearMap]

/-- Collect the individual infinite group coordinates of a mixed-coordinate unit. -/
def tupleCoordinates (g : G) : PlaceTuple (F := F) n
  | .inl v => (places F n g).1 v
  | .inr w => (places F n g).2 w

/-- Assemble the tuple of local groups into mixed coordinates. -/
def tupleGL (g : PlaceTuple (F := F) n) : G :=
  placeGL F n (fun v => g (.inl v), fun w => g (.inr w))

private def placeVal : (i : Index F) → PlaceGroup n i → PlaceMatrix n i
  | .inl _ => Units.val
  | .inr _ => Units.val

private theorem placeVal_injective (i : Index F) : Function.Injective (placeVal n i) := by
  cases i <;> exact fun _ _ h => Units.ext h

private theorem matrixCoordinate_tupleGL (g : PlaceTuple (F := F) n) (i : Index F) :
    matrixCoordinate n i (tupleGL n g).val = placeVal n i (g i) := by
  cases i <;> rfl

private theorem placeVal_tupleCoordinates (g : G) (i : Index F) :
    placeVal n i (tupleCoordinates n g i) = matrixCoordinate n i g.val := by
  cases i <;> rfl

theorem tupleCoordinates_tupleGL (g : PlaceTuple (F := F) n) : tupleCoordinates n (tupleGL n g) = g := by
  funext i
  apply placeVal_injective n i
  rw [placeVal_tupleCoordinates, matrixCoordinate_tupleGL]

private theorem tupleCoordinates_one : tupleCoordinates n (1 : G) = 1 := by
  have h : tupleGL n (1 : PlaceTuple (F := F) n) = 1 := map_one (placeGL F n)
  exact h ▸ tupleCoordinates_tupleGL n 1

/-- Keep the coordinate of the argument at the selected place and fix the others to `g`. -/
def freezeGL (i : Index F) (g : PlaceTuple (F := F) n) (a : G) : G :=
  tupleGL n (Function.update g i (tupleCoordinates n a i))

theorem freezeGL_tupleGL (i : Index F) (g y : PlaceTuple (F := F) n) :
    freezeGL n i g (tupleGL n y) = tupleGL n (Function.update g i (y i)) := by
  rw [freezeGL, tupleCoordinates_tupleGL]

theorem freezeGL_one (i : Index F) (g : PlaceTuple (F := F) n) :
    freezeGL n i g (1 : G) = tupleGL n (Function.update g i 1) := by
  rw [freezeGL, tupleCoordinates_one]
  rfl

private def matrixMaskCLM (i : Index F) : M →L[ℝ] M :=
  (matrixMask n i).toContinuousLinearMap

private def freezeMatrix (i : Index F) (g : PlaceTuple (F := F) n) (a : M) : M :=
  matrixMaskCLM n i a + (1 - matrixMaskCLM n i 1) * (tupleGL n g).val

private theorem freezeMatrix_unit (i : Index F) (g : PlaceTuple (F := F) n) (a : G) :
    freezeMatrix n i g a.val = (freezeGL n i g a).val := by
  change matrixMask n i a.val + (1 - matrixMask n i 1) * (tupleGL n g).val =
    (freezeGL n i g a).val
  apply matrix_ext n
  intro j
  by_cases h : j = i
  · subst j
    simp only [map_add, map_mul, map_sub, map_one, matrixMask_same, sub_self, zero_mul, add_zero,
      freezeGL, matrixCoordinate_tupleGL, Function.update_self, placeVal_tupleCoordinates]
  · simp only [map_add, map_mul, map_sub, map_one, matrixMask_other n h, sub_zero, one_mul,
      zero_add, freezeGL, matrixCoordinate_tupleGL, Function.update_of_ne h]

private theorem matrixMask_mul_direction (i : Index F) (g : PlaceTuple (F := F) n) (a : G)
    (X : L) : matrixMaskCLM n i (a.val * realLieAlgebraToMatrix F n X) =
      (freezeGL n i g a).val * realLieAlgebraToMatrix F n (supportedDirection n i X) := by
  change matrixMask n i (a.val * realLieAlgebraToMatrix F n X) =
    (freezeGL n i g a).val * matrixMask n i (realLieAlgebraToMatrix F n X)
  apply matrix_ext n
  intro j
  by_cases h : j = i
  · subst j
    simp only [matrixMask_same, map_mul, freezeGL, matrixCoordinate_tupleGL, Function.update_self,
      placeVal_tupleCoordinates]
  · rw [matrixMask_other n h, map_mul, matrixMask_other n h, mul_zero]

private def compactCoordinate (p : ArchimedeanCompactFactors F n) :
    (i : Index F) → Compact n i
  | .inl v => p.1 v
  | .inr w => p.2 w

private theorem compactCoordinate_same (p : ArchimedeanCompactFactors F n) (i : Index F) :
    matrixCoordinate n i (ArchimedeanCompactFactors.toArchimedeanGL F n p).val =
      matrixCoordinate n i
        (ArchimedeanCompactFactors.toArchimedeanGL F n (compactFactor n i (compactCoordinate n p i))).val := by
  cases i with
  | inl v =>
    change (p.1 v).val = ((ArchimedeanCompactFactors.realPlaceFactor F n v (p.1 v)).1 v).val
    rw [ArchimedeanCompactFactors.realPlaceFactor_fst, Pi.mulSingle_eq_same]
  | inr w =>
    change (p.2 w).val = ((ArchimedeanCompactFactors.complexPlaceFactor F n w (p.2 w)).2 w).val
    rw [ArchimedeanCompactFactors.complexPlaceFactor_snd, Pi.mulSingle_eq_same]

private theorem compactCoordinate_other (p : ArchimedeanCompactFactors F n)
    {i j : Index F} (h : j ≠ i) :
    matrixCoordinate n j
      (ArchimedeanCompactFactors.toArchimedeanGL F n (compactFactor n i (compactCoordinate n p i))).val = 1 := by
  cases i with
  | inl v =>
    cases j with
    | inl w =>
      change ((ArchimedeanCompactFactors.realPlaceFactor F n v (p.1 v)).1 w).val = 1
      rw [ArchimedeanCompactFactors.realPlaceFactor_fst, Pi.mulSingle_eq_of_ne
        (fun he => h (congrArg Sum.inl he))]
      rfl
    | inr w => rfl
  | inr v =>
    cases j with
    | inl w => rfl
    | inr w =>
      change ((ArchimedeanCompactFactors.complexPlaceFactor F n v (p.2 v)).2 w).val = 1
      rw [ArchimedeanCompactFactors.complexPlaceFactor_snd, Pi.mulSingle_eq_of_ne
        (fun he => h (congrArg Sum.inr he))]
      rfl

/-- At any compact point the varying coordinate is a single-place compact translate
of the slice's identity point. It is the same local translate for every frozen tuple. -/
theorem exists_freezeGL_compact (i : Index F) (k : standardInfiniteCompact F n) :
    ∃ l : Compact n i, ∀ g : PlaceTuple (F := F) n,
      freezeGL n i g (archimedeanGLCoordinates F n k.val) =
        freezeGL n i g 1 * archimedeanGLCoordinates F n (compactInclusion n i l).val := by
  obtain ⟨p, rfl⟩ := ArchimedeanCompactFactors.toStandardCompact_surjective F n k
  refine ⟨compactCoordinate n p i, fun g => Units.ext ?_⟩
  rw [Units.val_mul, ArchimedeanCompactFactors.toStandardCompact_val,
    ArchimedeanCompactFactors.coordinates_toInfiniteAdelicGL]
  have hcompact : archimedeanGLCoordinates F n (compactInclusion n i (compactCoordinate n p i)).val =
      ArchimedeanCompactFactors.toArchimedeanGL F n (compactFactor n i (compactCoordinate n p i)) :=
    ArchimedeanCompactFactors.coordinates_toInfiniteAdelicGL F n _
  rw [hcompact]
  apply matrix_ext n
  intro j
  by_cases h : j = i
  · subst j
    simp only [freezeGL, map_mul, matrixCoordinate_tupleGL, Function.update_self,
      placeVal_tupleCoordinates, Units.val_one, map_one, one_mul]
    exact compactCoordinate_same n p i
  · simp only [freezeGL, map_mul, matrixCoordinate_tupleGL, Function.update_of_ne h,
      compactCoordinate_other n p h, mul_one]

private theorem freezeExtension_unit (i : Index F) (g : PlaceTuple (F := F) n)
    (f : SmoothFunctions F n) (a : G) :
    coordinateExtension F n f (freezeMatrix n i g a.val) =
      f.val ((archimedeanGLCoordinates F n).symm (freezeGL n i g a)) := by
  rw [freezeMatrix_unit, coordinateExtension_apply]

private theorem freezeMatrix_contDiffAt (i : Index F) (g : PlaceTuple (F := F) n) (a : M) :
    ContDiffAt ℝ ∞ (freezeMatrix n i g) a :=
  (matrixMaskCLM n i).contDiff.contDiffAt.add contDiffAt_const

/-- View a one-place restriction as a smooth function on the whole infinite group,
constant in the other coordinates. -/
def freezeSmooth (i : Index F) (g : PlaceTuple (F := F) n) :
    SmoothFunctions F n →ₗ[ℂ] SmoothFunctions F n where
  toFun f := ⟨fun a => f.val ((archimedeanGLCoordinates F n).symm
    (freezeGL n i g (archimedeanGLCoordinates F n a))), by
      change ContMDiff 𝓘(ℝ, M) 𝓘(ℝ, ℂ) ∞ (fun a : G =>
        f.val ((archimedeanGLCoordinates F n).symm
          (freezeGL n i g (archimedeanGLCoordinates F n ((archimedeanGLCoordinates F n).symm a)))))
      simp only [ContinuousMulEquiv.apply_symm_apply]
      have hs : ContDiffOn ℝ ∞ (coordinateExtension F n f ∘ freezeMatrix n i g)
          (Set.range (Units.val : G → M)) := by
        rintro _ ⟨a, rfl⟩
        have hf : ContDiffAt ℝ ∞ (coordinateExtension F n f) (freezeMatrix n i g a.val) := by
          rw [freezeMatrix_unit]
          exact coordinateExtension_contDiffAt F n f _
        exact (hf.comp a.val (freezeMatrix_contDiffAt n i g a.val)).contDiffWithinAt
      have hv : ContMDiff 𝓘(ℝ, M) 𝓘(ℝ, M) ∞ (Units.val : G → M) :=
        Units.contMDiff_val
      exact ((contMDiffOn_iff_contDiffOn.mpr hs).comp_contMDiff hv (fun a => ⟨a, rfl⟩)).congr
        (fun a => (freezeExtension_unit n i g f a).symm)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem freezeSmooth_apply (i : Index F) (g : PlaceTuple (F := F) n)
    (f : SmoothFunctions F n) (a : InfiniteAdelicGL F n) :
    (freezeSmooth n i g f).val a =
      f.val ((archimedeanGLCoordinates F n).symm (freezeGL n i g (archimedeanGLCoordinates F n a))) :=
  rfl

theorem freezeSmooth_analytic (i : Index F) (g : PlaceTuple (F := F) n)
    (f : SmoothFunctions F n)
    (hf : ∀ a : G, AnalyticAt ℝ (coordinateExtension F n f) a.val) (a : G) :
    AnalyticAt ℝ (coordinateExtension F n (freezeSmooth n i g f)) a.val := by
  have ha : AnalyticAt ℝ (freezeMatrix n i g) a.val :=
    ((matrixMaskCLM n i).analyticAt a.val).add analyticAt_const
  refine ((hf (freezeGL n i g a)).comp_of_eq ha (freezeMatrix_unit n i g a)).congr ?_
  filter_upwards [Units.isOpenEmbedding_val.isOpen_range.mem_nhds
    (show a.val ∈ Set.range (Units.val : G → M) from ⟨a, rfl⟩)] with _ h
  obtain ⟨b, rfl⟩ := h
  rw [coordinateExtension_apply, freezeSmooth_apply, ContinuousMulEquiv.apply_symm_apply]
  exact freezeExtension_unit n i g f b

theorem smoothDifferential_freezeSmooth (i : Index F) (g : PlaceTuple (F := F) n)
    (f : SmoothFunctions F n) (X : L) :
    smoothDifferential F n X (freezeSmooth n i g f) =
      freezeSmooth n i g (smoothDifferential F n (supportedDirection n i X) f) := by
  apply Subtype.ext
  funext a
  let A := archimedeanGLCoordinates F n a
  let B := freezeGL n i g A
  have hderiv : HasFDerivAt (freezeMatrix n i g) (matrixMaskCLM n i) A.val :=
    (matrixMaskCLM n i).hasFDerivAt.add_const _
  have hf : HasFDerivAt (coordinateExtension F n f)
      (fderiv ℝ (coordinateExtension F n f) B.val) (freezeMatrix n i g A.val) := by
    rw [freezeMatrix_unit]
    exact ((coordinateExtension_contDiffAt F n f B).differentiableAt (by simp)).hasFDerivAt
  have hcomp := (hf.comp A.val hderiv).fderiv
  rw [smoothDifferential_eq_of_extension F n X _ (coordinateExtension F n f ∘ freezeMatrix n i g)
    (fun b => by
      rw [freezeSmooth_apply, ContinuousMulEquiv.apply_symm_apply]
      exact freezeExtension_unit n i g f b) a, freezeSmooth_apply, smoothDifferential_apply,
    ContinuousMulEquiv.apply_symm_apply]
  change fderiv ℝ (coordinateExtension F n f ∘ freezeMatrix n i g) A.val
    (A.val * realLieAlgebraToMatrix F n X) =
    fderiv ℝ (coordinateExtension F n f) B.val
      (B.val * realLieAlgebraToMatrix F n (supportedDirection n i X))
  rw [hcomp, ContinuousLinearMap.comp_apply, matrixMask_mul_direction]

end Langlands.Global.RankinSelbergGlobal.InfiniteWhittakerSlice
