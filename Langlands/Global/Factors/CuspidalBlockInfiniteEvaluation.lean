import Langlands.Global.Factors.CuspidalBlockArchimedeanEvaluation
import Langlands.Representation.Archimedean.UnitaryCompactAdmissibility
import Langlands.Representation.Tensor.Finite

/-! # The product of the actual archimedean evaluations -/

noncomputable section

open scoped TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 140000

universe u

namespace Langlands.Global.CuspidalBlockInduction

open Automorphic _root_.Langlands.Archimedean LocalFactor.Archimedean
open InfinitePlaceFamily ArchimedeanCompactBlocks NumberField

variable {F : Type u} [Field F] [NumberField F]

local notation "RP" => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "CP" => {v : InfinitePlace F // InfinitePlace.IsComplex v}
local notation "flat" => (fun d => List.flatten (List.ofFn d))

section Coordinates

variable (F) (n : ℕ)

private def compactFactorsPi :
    ArchimedeanCompactFactors F n ≃* (∀ v : Index F, Compact n v) where
  toFun p v := match v with
    | .inl v => p.1 v
    | .inr v => p.2 v
  invFun p := (fun v => p (.inl v), fun v => p (.inr v))
  left_inv _ := rfl
  right_inv p := funext fun v => by cases v <;> rfl
  map_mul' _ _ := funext fun v => by cases v <;> rfl

/-- The genuine standard infinite compact expressed in the individual unitary
matrix groups. -/
def infiniteCompactCoordinates :
    standardInfiniteCompact F n ≃* (∀ v : Index F, Compact n v) :=
  (MulEquiv.ofBijective (ArchimedeanCompactFactors.toStandardCompact F n).toMonoidHom
    ⟨ArchimedeanCompactFactors.toStandardCompact_injective F n,
      ArchimedeanCompactFactors.toStandardCompact_surjective F n⟩).symm.trans (compactFactorsPi F n)

theorem infiniteCompactCoordinates_apply_real (q : standardInfiniteCompact F n) (v : RP) :
    (infiniteCompactCoordinates F n q (.inl v)).val =
      ArchimedeanGL.realMatrix F n (archimedeanGLCoordinates F n q.val) v := by
  obtain ⟨p, rfl⟩ := ArchimedeanCompactFactors.toStandardCompact_surjective F n q
  have h : infiniteCompactCoordinates F n (ArchimedeanCompactFactors.toStandardCompact F n p) =
      compactFactorsPi F n p :=
    congrArg (compactFactorsPi F n) ((MulEquiv.ofBijective
      (ArchimedeanCompactFactors.toStandardCompact F n).toMonoidHom
        ⟨ArchimedeanCompactFactors.toStandardCompact_injective F n,
          ArchimedeanCompactFactors.toStandardCompact_surjective F n⟩).symm_apply_apply p)
  rw [h, ArchimedeanCompactFactors.toStandardCompact_val,
    ArchimedeanCompactFactors.coordinates_toInfiniteAdelicGL]
  rfl

theorem infiniteCompactCoordinates_apply_complex (q : standardInfiniteCompact F n) (v : CP) :
    (infiniteCompactCoordinates F n q (.inr v)).val =
      ArchimedeanGL.complexMatrix F n (archimedeanGLCoordinates F n q.val) v := by
  obtain ⟨p, rfl⟩ := ArchimedeanCompactFactors.toStandardCompact_surjective F n q
  have h : infiniteCompactCoordinates F n (ArchimedeanCompactFactors.toStandardCompact F n p) =
      compactFactorsPi F n p :=
    congrArg (compactFactorsPi F n) ((MulEquiv.ofBijective
      (ArchimedeanCompactFactors.toStandardCompact F n).toMonoidHom
        ⟨ArchimedeanCompactFactors.toStandardCompact_injective F n,
          ArchimedeanCompactFactors.toStandardCompact_surjective F n⟩).symm_apply_apply p)
  rw [h, ArchimedeanCompactFactors.toStandardCompact_val,
    ArchimedeanCompactFactors.coordinates_toInfiniteAdelicGL]
  rfl

end Coordinates

variable {k : ℕ}
variable (r : ℕ)
variable (real : {v : InfinitePlace F // v.IsReal} → Fin k → List RealBlock)
variable (complex : {v : InfinitePlace F // v.IsComplex} → Fin k → List ComplexCharacterData)

/-- The original-order standard module at each infinite place. -/
abbrev infiniteStandardSpace : Index F → Type
  | .inl v => realStandardKFinite (r + 1) (flat (real v))
  | .inr v => complexStandardKFinite (r + 1) (flat (complex v))

instance infiniteStandardSpace_group (v : Index F) : AddCommGroup (infiniteStandardSpace r real complex v) := by
  cases v <;> exact Submodule.addCommGroup _

instance infiniteStandardSpace_module (v : Index F) : Module ℂ (infiniteStandardSpace r real complex v) := by
  cases v <;> exact Submodule.module _

/-- The usual matrix-unitary right actions on the original-order standard modules. -/
def infiniteStandardLocalAction (v : Index F) :
    Representation ℂ (Compact (r + 1) v) (infiniteStandardSpace r real complex v) := by
  cases v with
  | inl v => exact realStandardRep (r + 1) (flat (real v))
  | inr v => exact complexStandardRep (r + 1) (flat (complex v))

/-- The tensor of the original-order standard modules with its actual full
infinite compact action. -/
def infiniteStandardAction :
    Representation ℂ (standardInfiniteCompact F (r + 1)) (⨂[ℂ] v, infiniteStandardSpace r real complex v) :=
  (FiniteTensor.external (infiniteStandardLocalAction r real complex)).comp
    (infiniteCompactCoordinates F (r + 1)).toMonoidHom

variable {r} [CompactSpace (AdeleQuotient F)] {m : Fin k → ℕ}
variable (hm : ∑ i, (m i + 1) = r + 1)
variable (T : ∀ i, CuspidalOperatorRealization F (m i))
variable (hr : ∀ v i, (T i).realization.HasRealPlaceParameter v (real v i))
variable (hc : ∀ v i, (T i).realization.HasComplexPlaceParameter v (complex v i))

private local instance (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
private local instance (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
private local instance {n : ℕ} (A : OperatorRealization F n) : AddCommGroup A.Space := Submodule.addCommGroup _
private local instance (i : Fin k) (p : Index F) : AddCommGroup ((T i).placeDensityModels.subspace p) :=
  Submodule.addCommGroup _

local notation "C" => (fun p : Index F => ⨂[ℂ] i, OperatorRealization.PlaceDensityModels.subspace
  (CuspidalOperatorRealization.placeDensityModels (T i)) p)
local notation "A" => infiniteStandardSpace r real complex

/-- The genuine single-place evaluation into the ordered tensor of local
cuspidal coefficients. -/
def infiniteLocalEvaluation (v : Index F) (q : Compact (r + 1) v) : A v →ₗ[ℂ] C v := by
  cases v with
  | inl v =>
    exact realPlaceEvaluation hm T v (real v) (hr v)
      (matrixUnitaryToCompact ℝ (r + 1) q)
  | inr v =>
    exact complexPlaceEvaluation hm T v (complex v) (hc v)
      (matrixUnitaryToCompact ℂ (r + 1) q)

/-- The product of the single-place evaluations, at a genuine infinite compact point. -/
def infiniteEvaluation (q : standardInfiniteCompact F (r + 1)) :
    (⨂[ℂ] v, A v) →ₗ[ℂ] (⨂[ℂ] v, C v) :=
  PiTensorProduct.map fun v => infiniteLocalEvaluation real complex hm T hr hc v
    (infiniteCompactCoordinates F (r + 1) q v)

theorem infiniteLocalEvaluation_right (v : Index F) (q d : Compact (r + 1) v) (f : A v) :
    infiniteLocalEvaluation real complex hm T hr hc v q (infiniteStandardLocalAction r real complex v d f) =
      infiniteLocalEvaluation real complex hm T hr hc v (q * d) f := by
  cases v with
  | inl v =>
    have h := realPlaceEvaluation_right hm T v (real v) (hr v)
      (matrixUnitaryToCompact ℝ (r + 1) q) (matrixUnitaryToCompact ℝ (r + 1) d) f
    exact h.trans (congrArg (fun z => realPlaceEvaluation hm T v (real v) (hr v) z f)
      ((matrixUnitaryToCompact ℝ (r + 1)).map_mul q d).symm)
  | inr v =>
    have h := complexPlaceEvaluation_right hm T v (complex v) (hc v)
      (matrixUnitaryToCompact ℂ (r + 1) q) (matrixUnitaryToCompact ℂ (r + 1) d) f
    exact h.trans (congrArg (fun z => complexPlaceEvaluation hm T v (complex v) (hc v) z f)
      ((matrixUnitaryToCompact ℂ (r + 1)).map_mul q d).symm)

theorem infiniteEvaluation_right (q d : standardInfiniteCompact F (r + 1)) (f : ⨂[ℂ] v, A v) :
    infiniteEvaluation real complex hm T hr hc q (infiniteStandardAction r real complex d f) =
      infiniteEvaluation real complex hm T hr hc (q * d) f := by
  let L (g : standardInfiniteCompact F (r + 1)) (v : Index F) :=
    infiniteLocalEvaluation real complex hm T hr hc v (infiniteCompactCoordinates F (r + 1) g v)
  let P (v : Index F) := infiniteStandardLocalAction r real complex v (infiniteCompactCoordinates F (r + 1) d v)
  have h (v : Index F) : (L q v).comp (P v) = L (q * d) v := by
    apply LinearMap.ext
    intro f
    change L q v (P v f) = L (q * d) v f
    have h' := infiniteLocalEvaluation_right real complex hm T hr hc v
      (infiniteCompactCoordinates F (r + 1) q v) (infiniteCompactCoordinates F (r + 1) d v) f
    exact h'.trans (congrArg (fun z => infiniteLocalEvaluation real complex hm T hr hc v z f)
      (congrFun ((infiniteCompactCoordinates F (r + 1)).map_mul q d) v).symm)
  change PiTensorProduct.map (L q) (PiTensorProduct.map P f) = PiTensorProduct.map (L (q * d)) f
  exact congrArg (fun g => g f) ((PiTensorProduct.map_comp (L q) P).symm.trans
    (congrArg (fun R => PiTensorProduct.map R) (funext h)))

end Langlands.Global.CuspidalBlockInduction
