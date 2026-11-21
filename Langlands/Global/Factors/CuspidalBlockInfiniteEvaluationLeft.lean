import Langlands.Global.Factors.CuspidalBlockInfiniteCompactCoordinates

/-! # Left compact covariance of the infinite block evaluations -/

noncomputable section

open scoped TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 115000

universe u

namespace Langlands.Global.CuspidalBlockInduction

open Automorphic _root_.Langlands.Archimedean NumberField LocalFactor.Archimedean
open InfinitePlaceFamily ArchimedeanCompactBlocks AdelicBlockParabolic

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
variable {k : ℕ} {m : Fin k → ℕ}
variable (T : ∀ i, CuspidalOperatorRealization F (m i))

private local instance (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
private local instance {n : ℕ} (R : OperatorRealization F n) : AddCommGroup R.Space := Submodule.addCommGroup _
private local instance (i : Fin k) (p : Index F) : AddCommGroup ((T i).placeDensityModels.subspace p) :=
  Submodule.addCommGroup _

local notation "C" => (fun p : Index F => ⨂[ℂ] i, OperatorRealization.PlaceDensityModels.subspace
  (CuspidalOperatorRealization.placeDensityModels (T i)) p)

/-- The genuine block compact actions on the infinite coefficients, grouped
first by place and then by the ordered blocks. -/
def infiniteCoefficientCompactMap (d : ∀ i : Fin k, standardInfiniteCompact F (m i + 1)) :
    Module.End ℂ (⨂[ℂ] v, C v) :=
  PiTensorProduct.map fun v => PiTensorProduct.map fun i =>
    (T i).placeDensityModels.sourceCompact v (infiniteCompactCoordinates F _ (d i) v)

variable {r : ℕ} (hm : ∑ i, (m i + 1) = r + 1)
variable (real : {v : InfinitePlace F // v.IsReal} → Fin k → List RealBlock)
variable (complex : {v : InfinitePlace F // v.IsComplex} → Fin k → List ComplexCharacterData)
variable (hr : ∀ v i, (T i).realization.HasRealPlaceParameter v (real v i))
variable (hc : ∀ v i, (T i).realization.HasComplexPlaceParameter v (complex v i))

local notation "B" =>
  GeneralLinear.BlockShape.mk k (fun i => m i + 1) (fun i => Nat.succ_pos (m i)) hm
local notation "K" => standardInfiniteCompact F (r + 1)
local notation "A" => infiniteStandardSpace r real complex
local notation "coords" => infiniteCompactCoordinates F (r + 1)
local notation "ev" => infiniteLocalEvaluation real complex hm T hr hc

private theorem infiniteLocalEvaluation_left (p : infiniteCompactIntersection F B)
    (q : K) (v : Index F) (a : A v) :
    ev v (coords (⟨p.val.val, p.property⟩ * q) v) a =
      PiTensorProduct.map (fun i => (T i).placeDensityModels.sourceCompact v
        (infiniteCompactCoordinates F _ (infiniteLeviCompact B p i) v)) (ev v (coords q v) a) := by
  let pK : K := ⟨p.val.val, p.property⟩
  have hmul := congrFun ((coords).map_mul pK q) v
  cases v with
  | inl v =>
    let j := matrixUnitaryToCompact ℝ (r + 1)
    let d (i : Fin k) := matrixUnitaryToCompact ℝ (m i + 1)
      (infiniteCompactCoordinates F (m i + 1) (infiniteLeviCompact B p i) (.inl v))
    let h := j (coords q (.inl v))
    have hl := infiniteCompactCoordinates_levi_real B p v
    have he : j (coords (pK * q) (.inl v)) = compactLeviEmbedding ℝ B d * h :=
      (congrArg j hmul).trans ((j.map_mul _ _).trans (congrArg (fun x => x * h) hl))
    exact (congrArg (fun x => realPlaceEvaluation hm T v (real v) (hr v) x a) he).trans
      (realPlaceEvaluation_left hm T v (real v) (hr v) d h a)
  | inr v =>
    let j := matrixUnitaryToCompact ℂ (r + 1)
    let d (i : Fin k) := matrixUnitaryToCompact ℂ (m i + 1)
      (infiniteCompactCoordinates F (m i + 1) (infiniteLeviCompact B p i) (.inr v))
    let h := j (coords q (.inr v))
    have hl := infiniteCompactCoordinates_levi_complex B p v
    have he : j (coords (pK * q) (.inr v)) = compactLeviEmbedding ℂ B d * h :=
      (congrArg j hmul).trans ((j.map_mul _ _).trans (congrArg (fun x => x * h) hl))
    exact (congrArg (fun x => complexPlaceEvaluation hm T v (complex v) (hc v) x a) he).trans
      (complexPlaceEvaluation_left hm T v (complex v) (hc v) d h a)

/-- Multiplication by an element of the genuine infinite compact parabolic
intersection gives the actual left compact Levi action on the evaluations. -/
theorem infiniteEvaluation_left (p : infiniteCompactIntersection F B) (q : K)
    (a : ⨂[ℂ] v, A v) :
    infiniteEvaluation real complex hm T hr hc (⟨p.val.val, p.property⟩ * q) a =
      infiniteCoefficientCompactMap T (infiniteLeviCompact B p)
        (infiniteEvaluation real complex hm T hr hc q a) := by
  let L (q : K) (v : Index F) : A v →ₗ[ℂ] C v := ev v (coords q v)
  let pK : K := ⟨p.val.val, p.property⟩
  let U (v : Index F) : Module.End ℂ (C v) := PiTensorProduct.map fun i =>
    (T i).placeDensityModels.sourceCompact v
      (infiniteCompactCoordinates F _ (infiniteLeviCompact B p i) v)
  have h (v : Index F) : L (pK * q) v = (U v).comp (L q v) :=
    LinearMap.ext fun f => infiniteLocalEvaluation_left T hm real complex hr hc p q v f
  change PiTensorProduct.map (L (pK * q)) a = PiTensorProduct.map U (PiTensorProduct.map (L q) a)
  exact congrArg (fun f => f a) ((congrArg (fun l => PiTensorProduct.map l) (funext h)).trans
    (PiTensorProduct.map_comp U (L q)))

end Langlands.Global.CuspidalBlockInduction
