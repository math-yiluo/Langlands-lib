import Langlands.Global.Factors.CuspidalBlockArchimedeanEvaluation
import Langlands.Global.AdelicBlockParabolicPlaceCurves

/-! # Lie derivatives of local evaluation in the actual cuspidal coefficients -/

noncomputable section

open scoped Classical ContDiff Manifold Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 230000
set_option Elab.async false

universe u

namespace Langlands.Global.CuspidalBlockInduction

open Automorphic _root_.Langlands.Archimedean LocalFactor.Archimedean
open NumberField ArchimedeanCompactBlocks ArchimedeanGL AdelicBlockParabolic InfinitePlaceFamily

attribute [local instance 100] LieRing.ofAssociativeRing

private theorem congr_blockOperators {I : Type*} [Fintype I] [DecidableEq I]
    {V W : I → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (e : ∀ i, V i ≃ₗ[ℂ] W i) (A : ∀ i, Module.End ℂ (V i)) (D : ∀ i, Module.End ℂ (W i))
    (h : ∀ i x, e i (A i x) = D i (e i x)) (x : ⨂[ℂ] i, V i) :
    PiTensorProduct.congr e ((∑ i, PiTensorProduct.map (fun j => if j = i then A j else LinearMap.id)) x) =
      (∑ i, PiTensorProduct.map (fun j => if j = i then D j else LinearMap.id)) (PiTensorProduct.congr e x) := by
  simp only [LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  let L (j : I) := (e j).toLinearMap
  change ((PiTensorProduct.map L).comp (PiTensorProduct.map (fun j => if j = i then A j else LinearMap.id))) x =
    ((PiTensorProduct.map (fun j => if j = i then D j else LinearMap.id)).comp (PiTensorProduct.map L)) x
  rw [← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp]
  apply congrArg (fun g : ∀ j, V j →ₗ[ℂ] W j => PiTensorProduct.map g x)
  funext j
  by_cases hj : j = i
  · subst j
    simp only [ite_true]
    exact LinearMap.ext (h i)
  · simp only [ite_eq_right hj, LinearMap.comp_id, LinearMap.id_comp]

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
variable {r k : ℕ} {m : Fin k → ℕ} (hm : ∑ i, (m i + 1) = r + 1)
variable (T : ∀ i, CuspidalOperatorRealization F (m i))

local notation "B" => GeneralLinear.BlockShape.mk k (fun i => m i + 1) (fun i => Nat.succ_pos (m i)) hm
local notation "flat" => (fun d => List.flatten (List.ofFn d))
local notation "C" => (fun (p : Index F) (i : Fin k) => OperatorRealization.PlaceDensityModels.subspace
  (CuspidalOperatorRealization.placeDensityModels (T i)) p)

private local instance (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
private local instance {n : ℕ} (A : OperatorRealization F n) : AddCommGroup A.Space := Submodule.addCommGroup _
private local instance (p : Index F) (i : Fin k) : AddCommGroup (C p i) := Submodule.addCommGroup _

/-- Sum of the actual local Lie operators in the block slots of one place's coefficient tensor. -/
def placeCoefficientLieSum (v : Index F) (Y : ∀ i, Lie (m i + 1) v) :
    Module.End ℂ (⨂[ℂ] i, C v i) :=
  ∑ i, PiTensorProduct.map (fun j => if j = i then (T j).placeDensityModels.sourceLie v (Y j) else LinearMap.id)

section Real

variable (v : {v : InfinitePlace F // v.IsReal}) (ds : Fin k → List RealBlock)
variable (hp : ∀ i, (T i).realization.HasRealPlaceParameter v (ds i))

omit [CompactSpace (AdeleQuotient F)] in
private theorem realStandardEvaluation_lie_upper
    (D : StandardBlockEvaluation ℝ B (realStandardKFinite (r + 1) (flat ds))
      (fun i => realStandardKFinite (m i + 1) (ds i)))
    (X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) (hX : X.IsUpperTriangular)
    (f : realStandardKFinite (r + 1) (flat ds)) :
    D.evaluation 1 (realStandardLie (r + 1) (flat ds) (1 ⊗ₜ[ℝ] X) f) =
      archimedeanHalfDerivative F B (realPlaceLieInclusion F (r + 1) v X) • D.evaluation 1 f +
      blockTensorDifferential (fun i => realStandardLie (m i + 1) (ds i)
        (1 ⊗ₜ[ℝ] localDiagonalBlock ℝ B i X)) (D.evaluation 1 f) := by
  let p := parabolicLine ℝ B X hX
  let Z := realPlaceLieInclusion F (r + 1) v X
  let a := archimedeanHalfDerivative F B Z
  let q (t : ℝ) := realInfiniteParabolicInclusion F B v (p t)
  have hp₀ : p 0 = 1 := parabolicLine_zero ℝ B X hX
  have hpX : HasDerivAt (fun t => (p t).val.val) X 0 := parabolicLine_hasDerivAt ℝ B X hX
  have hq₀ : q 0 = 1 := by change realInfiniteParabolicInclusion F B v (p 0) = 1; rw [hp₀, map_one]
  have hqZ := realInfiniteParabolicInclusion_hasDerivAt F B v p X hpX
  have ha : HasDerivAt (fun t => localLeviHalf ℝ B ((B).leviProjection ℝ (p t))) a 0 :=
    (archimedeanHalfExtension_hasDerivAt F B q hq₀ Z hqZ).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => (archimedeanHalfExtension_realInfiniteParabolicInclusion F B v (p t)).symm)
  let df := realStandardLie (r + 1) (flat ds) (1 ⊗ₜ[ℝ] X) f
  let Y (i : Fin k) := localDiagonalBlock ℝ B i X
  let L (i : Fin k) := realStandardLie (m i + 1) (ds i) (1 ⊗ₜ[ℝ] Y i)
  exact D.evaluation_differential_parabolic
    (fun g => contMDiff_of_mem_realStandardModule g.2.1)
    (fun _ g => contMDiff_of_mem_realStandardModule g.2.1)
    f df X (realStandardLie_one_tmul_apply_coe _ _ X f) p hp₀ hpX Y
    (leviProjection_hasDerivAt ℝ B p X hpX) L
    (fun i => realStandardLie_one_tmul_apply_coe _ _ (Y i)) a ha

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
/-- At real compact identity, evaluation of the upper triangular Lie derivative
splits into the half-character derivative and actual block Lie operators. -/
theorem realPlaceEvaluation_lie_upper (X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ)
    (hX : X.IsUpperTriangular) (f : realStandardKFinite (r + 1) (flat ds)) :
    realPlaceEvaluation hm T v ds hp 1 (realStandardLie (r + 1) (flat ds) (1 ⊗ₜ[ℝ] X) f) =
      archimedeanHalfDerivative F B (realPlaceLieInclusion F (r + 1) v X) •
        realPlaceEvaluation hm T v ds hp 1 f +
      placeCoefficientLieSum T (.inl v) (fun i => 1 ⊗ₜ[ℝ] localDiagonalBlock ℝ B i X)
        (realPlaceEvaluation hm T v ds hp 1 f) := by
  let a := archimedeanHalfDerivative F B (realPlaceLieInclusion F (r + 1) v X)
  let Y (i : Fin k) := localDiagonalBlock ℝ B i X
  let L (i : Fin k) := realStandardLie (m i + 1) (ds i) (1 ⊗ₜ[ℝ] Y i)
  let D := realStandardBlockEvaluationOfShape B ds (fun i => (hp i).1)
  have hd := realStandardEvaluation_lie_upper hm v ds D X hX f
  let e (i : Fin k) := (realStandardCoefficientEquiv (T i) v (hp i)).toLinearEquiv
  let L' (i : Fin k) := (T i).placeDensityModels.sourceLie (.inl v) (1 ⊗ₜ[ℝ] Y i)
  have hL (i : Fin k) (x : realStandardKFinite (m i + 1) (ds i)) : e i (L i x) = L' i (e i x) :=
    Representation.IntertwiningMap.isIntertwining _ _
      (realStandardCoefficientEquiv (T i) v (hp i)).toIntertwiningMap
      (FreeMonoid.of (.inr (1 ⊗ₜ[ℝ] Y i))) x
  have hsum := @congr_blockOperators (Fin k) (Fin.fintype k) (inferInstance : DecidableEq (Fin k))
    (fun i => realStandardKFinite (m i + 1) (ds i)) (fun i => ↥(C (.inl v) i))
    (fun _ => Submodule.addCommGroup _) (fun _ => Submodule.module _)
    (fun _ => Submodule.addCommGroup _) (fun _ => Submodule.module _)
    e L L' hL (D.evaluation 1 f)
  let E := realCoefficientTensorEquiv T v ds hp
  change E (blockTensorDifferential L (D.evaluation 1 f)) =
    placeCoefficientLieSum T (.inl v) (fun i => 1 ⊗ₜ[ℝ] Y i) (E (D.evaluation 1 f)) at hsum
  have h := congrArg E hd
  simp only [map_add, map_smul] at h
  have hfinal := h.trans (congrArg (Add.add (a • E (D.evaluation 1 f))) hsum)
  simpa only [realPlaceEvaluation, LinearMap.comp_apply, LinearEquiv.coe_coe, E, D, a, Y] using! hfinal

end Real

section Complex

variable (v : {v : InfinitePlace F // v.IsComplex}) (ds : Fin k → List ComplexCharacterData)
variable (hp : ∀ i, (T i).realization.HasComplexPlaceParameter v (ds i))

omit [CompactSpace (AdeleQuotient F)] in
private theorem complexStandardEvaluation_lie_upper
    (D : StandardBlockEvaluation ℂ B (complexStandardKFinite (r + 1) (flat ds))
      (fun i => complexStandardKFinite (m i + 1) (ds i)))
    (X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (hX : X.IsUpperTriangular)
    (f : complexStandardKFinite (r + 1) (flat ds)) :
    D.evaluation 1 (complexStandardLie (r + 1) (flat ds) (1 ⊗ₜ[ℝ] X) f) =
      archimedeanHalfDerivative F B (complexPlaceLieInclusion F (r + 1) v X) • D.evaluation 1 f +
      blockTensorDifferential (fun i => complexStandardLie (m i + 1) (ds i)
        (1 ⊗ₜ[ℝ] localDiagonalBlock ℂ B i X)) (D.evaluation 1 f) := by
  let p := parabolicLine ℂ B X hX
  let Z := complexPlaceLieInclusion F (r + 1) v X
  let a := archimedeanHalfDerivative F B Z
  let q (t : ℝ) := complexInfiniteParabolicInclusion F B v (p t)
  have hp₀ : p 0 = 1 := parabolicLine_zero ℂ B X hX
  have hpX : HasDerivAt (fun t => (p t).val.val) X 0 := parabolicLine_hasDerivAt ℂ B X hX
  have hq₀ : q 0 = 1 := by change complexInfiniteParabolicInclusion F B v (p 0) = 1; rw [hp₀, map_one]
  have hqZ := complexInfiniteParabolicInclusion_hasDerivAt F B v p X hpX
  have ha : HasDerivAt (fun t => localLeviHalf ℂ B ((B).leviProjection ℂ (p t))) a 0 :=
    (archimedeanHalfExtension_hasDerivAt F B q hq₀ Z hqZ).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => (archimedeanHalfExtension_complexInfiniteParabolicInclusion F B v (p t)).symm)
  let df := complexStandardLie (r + 1) (flat ds) (1 ⊗ₜ[ℝ] X) f
  let Y (i : Fin k) := localDiagonalBlock ℂ B i X
  let L (i : Fin k) := complexStandardLie (m i + 1) (ds i) (1 ⊗ₜ[ℝ] Y i)
  exact D.evaluation_differential_parabolic (fun g => g.2.1.1) (fun _ g => g.2.1.1)
    f df X (principalSeriesLie_one_tmul_apply_coe ℂ _ _ X f) p hp₀ hpX Y
    (leviProjection_hasDerivAt ℂ B p X hpX) L
    (fun i => principalSeriesLie_one_tmul_apply_coe ℂ _ _ (Y i)) a ha

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
/-- At complex compact identity, evaluation of the upper triangular Lie derivative
splits into the half-character derivative and actual block Lie operators. -/
theorem complexPlaceEvaluation_lie_upper (X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hX : X.IsUpperTriangular) (f : complexStandardKFinite (r + 1) (flat ds)) :
    complexPlaceEvaluation hm T v ds hp 1 (complexStandardLie (r + 1) (flat ds) (1 ⊗ₜ[ℝ] X) f) =
      archimedeanHalfDerivative F B (complexPlaceLieInclusion F (r + 1) v X) •
        complexPlaceEvaluation hm T v ds hp 1 f +
      placeCoefficientLieSum T (.inr v) (fun i => 1 ⊗ₜ[ℝ] localDiagonalBlock ℂ B i X)
        (complexPlaceEvaluation hm T v ds hp 1 f) := by
  let a := archimedeanHalfDerivative F B (complexPlaceLieInclusion F (r + 1) v X)
  let Y (i : Fin k) := localDiagonalBlock ℂ B i X
  let L (i : Fin k) := complexStandardLie (m i + 1) (ds i) (1 ⊗ₜ[ℝ] Y i)
  let D := complexStandardBlockEvaluationOfShape B ds (fun i => (hp i).1)
  have hd := complexStandardEvaluation_lie_upper hm v ds D X hX f
  let e (i : Fin k) := (complexStandardCoefficientEquiv (T i) v (hp i)).toLinearEquiv
  let L' (i : Fin k) := (T i).placeDensityModels.sourceLie (.inr v) (1 ⊗ₜ[ℝ] Y i)
  have hL (i : Fin k) (x : complexStandardKFinite (m i + 1) (ds i)) : e i (L i x) = L' i (e i x) :=
    Representation.IntertwiningMap.isIntertwining _ _
      (complexStandardCoefficientEquiv (T i) v (hp i)).toIntertwiningMap
      (FreeMonoid.of (.inr (1 ⊗ₜ[ℝ] Y i))) x
  have hsum := @congr_blockOperators (Fin k) (Fin.fintype k) (inferInstance : DecidableEq (Fin k))
    (fun i => complexStandardKFinite (m i + 1) (ds i)) (fun i => ↥(C (.inr v) i))
    (fun _ => Submodule.addCommGroup _) (fun _ => Submodule.module _)
    (fun _ => Submodule.addCommGroup _) (fun _ => Submodule.module _)
    e L L' hL (D.evaluation 1 f)
  let E := complexCoefficientTensorEquiv T v ds hp
  change E (blockTensorDifferential L (D.evaluation 1 f)) =
    placeCoefficientLieSum T (.inr v) (fun i => 1 ⊗ₜ[ℝ] Y i) (E (D.evaluation 1 f)) at hsum
  have h := congrArg E hd
  simp only [map_add, map_smul] at h
  have hfinal := h.trans (congrArg (Add.add (a • E (D.evaluation 1 f))) hsum)
  simpa only [complexPlaceEvaluation, LinearMap.comp_apply, LinearEquiv.coe_coe, E, D, a, Y] using! hfinal

end Complex

end Langlands.Global.CuspidalBlockInduction
