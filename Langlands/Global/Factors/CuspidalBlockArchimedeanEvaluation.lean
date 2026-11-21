import Langlands.Global.ArchimedeanBlockEvaluationActions
import Langlands.Global.Factors.CuspidalBlockStandardCoefficients

/-! # Evaluation of standard vectors into actual cuspidal block coefficients -/

noncomputable section

open scoped BigOperators TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 160000

universe u

namespace Langlands.Global.CuspidalBlockInduction

open Automorphic _root_.Langlands.Archimedean LocalFactor.Archimedean
open ArchimedeanCompactBlocks
open NumberField

private theorem tensor_congr_map
    {I : Type*} {V W : I → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (e : ∀ i, V i ≃ₗ[ℂ] W i) (a : ∀ i, Module.End ℂ (V i)) (b : ∀ i, Module.End ℂ (W i))
    (h : ∀ i z, e i (a i z) = b i (e i z)) (x : ⨂[ℂ] i, V i) :
    PiTensorProduct.congr e (PiTensorProduct.map a x) =
      PiTensorProduct.map b (PiTensorProduct.congr e x) := by
  let L := (PiTensorProduct.congr e).toLinearMap.comp (PiTensorProduct.map a)
  let R := (PiTensorProduct.map b).comp (PiTensorProduct.congr e).toLinearMap
  have he : L = R := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro s
    change PiTensorProduct.congr e (PiTensorProduct.map a (PiTensorProduct.tprod ℂ s)) =
      PiTensorProduct.map b (PiTensorProduct.congr e (PiTensorProduct.tprod ℂ s))
    simp only [PiTensorProduct.map_tprod, PiTensorProduct.congr_tprod, h]
  exact LinearMap.congr_fun he x

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
variable {r k : ℕ} {m : Fin k → ℕ} (hm : ∑ i, (m i + 1) = r + 1)
variable (T : ∀ i, CuspidalOperatorRealization F (m i))

local notation "B" =>
  GeneralLinear.BlockShape.mk k (fun i => m i + 1) (fun i => Nat.succ_pos (m i)) hm
local notation "flat" => (fun d => List.flatten (List.ofFn d))

private local instance (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
private local instance {n : ℕ} (A : OperatorRealization F n) : AddCommGroup A.Space := Submodule.addCommGroup _
private local instance (i : Fin k) (p : InfinitePlaceFamily.Index F) :
    AddCommGroup ((T i).placeDensityModels.subspace p) := Submodule.addCommGroup _

section Real

variable (v : {v : InfinitePlace F // v.IsReal}) (ds : Fin k → List RealBlock)
variable (hp : ∀ i, (T i).realization.HasRealPlaceParameter v (ds i))

local notation "C" => (⨂[ℂ] i, OperatorRealization.PlaceDensityModels.subspace
  (CuspidalOperatorRealization.placeDensityModels (T i)) (Sum.inl v))
local notation "D" => realStandardBlockEvaluationOfShape B ds (fun i => And.left (hp i))

/-- Identify the real standard block tensor with the actual real cuspidal coefficients. -/
def realCoefficientTensorEquiv :
    (⨂[ℂ] i, realStandardKFinite (m i + 1) (ds i)) ≃ₗ[ℂ] C :=
  PiTensorProduct.congr fun i => (realStandardCoefficientEquiv (T i) v (hp i)).toLinearEquiv

/-- Evaluate an original-order real standard vector in the actual coefficient tensor. -/
def realPlaceEvaluation (q : unitaryCompact ℝ (r + 1)) :
    realStandardKFinite (r + 1) (flat ds) →ₗ[ℂ] C :=
  (realCoefficientTensorEquiv T v ds hp).toLinearMap.comp ((D).evaluation q)

theorem realPlaceEvaluation_right (q d : unitaryCompact ℝ (r + 1))
    (f : realStandardKFinite (r + 1) (flat ds)) :
    realPlaceEvaluation hm T v ds hp q (realCompactAction (r + 1) (flat ds) d f) =
      realPlaceEvaluation hm T v ds hp (q * d) f :=
  congrArg (realCoefficientTensorEquiv T v ds hp)
    ((D).evaluation_right (realCompactAction (r + 1) (flat ds))
      (realCompactAction_apply _ _) q d f)

theorem realPlaceEvaluation_left
    (d : ∀ i, unitaryCompact ℝ (m i + 1)) (q : unitaryCompact ℝ (r + 1))
    (f : realStandardKFinite (r + 1) (flat ds)) :
    realPlaceEvaluation hm T v ds hp (compactLeviEmbedding ℝ B d * q) f =
      PiTensorProduct.map (fun i => (T i).placeDensityModels.sourceCompact (.inl v)
        ⟨(d i).val.val, (d i).property⟩) (realPlaceEvaluation hm T v ds hp q f) := by
  let e (i : Fin k) := (realStandardCoefficientEquiv (T i) v (hp i)).toLinearEquiv
  let a (i : Fin k) := realCompactAction (m i + 1) (ds i) (d i)
  let b (i : Fin k) := (T i).placeDensityModels.sourceCompact (.inl v)
    ⟨(d i).val.val, (d i).property⟩
  have h (i : Fin k) (z : realStandardKFinite (m i + 1) (ds i)) : e i (a i z) = b i (e i z) :=
    Representation.IntertwiningMap.isIntertwining _ _
      (realStandardCoefficientEquiv (T i) v (hp i)).toIntertwiningMap
      (FreeMonoid.of (.inl ⟨(d i).val.val, (d i).property⟩)) z
  exact (congrArg (realCoefficientTensorEquiv T v ds hp) ((D).evaluation_left
    (fun i => realCompactAction (m i + 1) (ds i)) (fun i => realCompactAction_apply _ _) d q f)).trans
      (tensor_congr_map e a b h ((D).evaluation q f))

theorem realPlaceEvaluation_injective :
    Function.Injective (fun (f : realStandardKFinite (r + 1) (flat ds)) =>
      fun q => realPlaceEvaluation hm T v ds hp q f) := by
  intro f g h
  apply sub_eq_zero.mp
  refine (D).evaluation_separates ((inf_le_left : realStandardKFinite (r + 1) (flat ds) ≤ _).trans
    (realStandardModule_le_principalSeries (r + 1) (flat ds))) (f - g) ?_
  intro q
  have he : (D).evaluation q f = (D).evaluation q g :=
    (realCoefficientTensorEquiv T v ds hp).injective (congrFun h q)
  exact (map_sub ((D).evaluation q) f g).trans (sub_eq_zero.mpr he)

end Real

section Complex

variable (v : {v : InfinitePlace F // v.IsComplex}) (ds : Fin k → List ComplexCharacterData)
variable (hp : ∀ i, (T i).realization.HasComplexPlaceParameter v (ds i))

local notation "C" => (⨂[ℂ] i, OperatorRealization.PlaceDensityModels.subspace
  (CuspidalOperatorRealization.placeDensityModels (T i)) (Sum.inr v))
local notation "D" => complexStandardBlockEvaluationOfShape B ds (fun i => And.left (hp i))

/-- Identify the complex standard block tensor with the actual complex cuspidal coefficients. -/
def complexCoefficientTensorEquiv :
    (⨂[ℂ] i, complexStandardKFinite (m i + 1) (ds i)) ≃ₗ[ℂ] C :=
  PiTensorProduct.congr fun i => (complexStandardCoefficientEquiv (T i) v (hp i)).toLinearEquiv

/-- Evaluate an original-order complex standard vector in the actual coefficient tensor. -/
def complexPlaceEvaluation (q : unitaryCompact ℂ (r + 1)) :
    complexStandardKFinite (r + 1) (flat ds) →ₗ[ℂ] C :=
  (complexCoefficientTensorEquiv T v ds hp).toLinearMap.comp ((D).evaluation q)

theorem complexPlaceEvaluation_right (q d : unitaryCompact ℂ (r + 1))
    (f : complexStandardKFinite (r + 1) (flat ds)) :
    complexPlaceEvaluation hm T v ds hp q (complexCompactAction (r + 1) (flat ds) d f) =
      complexPlaceEvaluation hm T v ds hp (q * d) f :=
  congrArg (complexCoefficientTensorEquiv T v ds hp)
    ((D).evaluation_right (complexCompactAction (r + 1) (flat ds))
      (complexCompactAction_apply _ _) q d f)

theorem complexPlaceEvaluation_left
    (d : ∀ i, unitaryCompact ℂ (m i + 1)) (q : unitaryCompact ℂ (r + 1))
    (f : complexStandardKFinite (r + 1) (flat ds)) :
    complexPlaceEvaluation hm T v ds hp (compactLeviEmbedding ℂ B d * q) f =
      PiTensorProduct.map (fun i => (T i).placeDensityModels.sourceCompact (.inr v)
        ⟨(d i).val.val, (d i).property⟩) (complexPlaceEvaluation hm T v ds hp q f) := by
  let e (i : Fin k) := (complexStandardCoefficientEquiv (T i) v (hp i)).toLinearEquiv
  let a (i : Fin k) := complexCompactAction (m i + 1) (ds i) (d i)
  let b (i : Fin k) := (T i).placeDensityModels.sourceCompact (.inr v)
    ⟨(d i).val.val, (d i).property⟩
  have h (i : Fin k) (z : complexStandardKFinite (m i + 1) (ds i)) : e i (a i z) = b i (e i z) :=
    Representation.IntertwiningMap.isIntertwining _ _
      (complexStandardCoefficientEquiv (T i) v (hp i)).toIntertwiningMap
      (FreeMonoid.of (.inl ⟨(d i).val.val, (d i).property⟩)) z
  exact (congrArg (complexCoefficientTensorEquiv T v ds hp) ((D).evaluation_left
    (fun i => complexCompactAction (m i + 1) (ds i)) (fun i => complexCompactAction_apply _ _) d q f)).trans
      (tensor_congr_map e a b h ((D).evaluation q f))

theorem complexPlaceEvaluation_injective :
    Function.Injective (fun (f : complexStandardKFinite (r + 1) (flat ds)) =>
      fun q => complexPlaceEvaluation hm T v ds hp q f) := by
  intro f g h
  apply sub_eq_zero.mp
  refine (D).evaluation_separates inf_le_left (f - g) ?_
  intro q
  have he : (D).evaluation q f = (D).evaluation q g :=
    (complexCoefficientTensorEquiv T v ds hp).injective (congrFun h q)
  exact (map_sub ((D).evaluation q) f g).trans (sub_eq_zero.mpr he)

end Complex

end Langlands.Global.CuspidalBlockInduction
