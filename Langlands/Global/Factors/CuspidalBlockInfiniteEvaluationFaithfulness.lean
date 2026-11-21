import Langlands.Global.Factors.CuspidalBlockInfiniteEvaluation

/-! # Separation by the full infinite compact family -/

noncomputable section

open scoped TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 130000

universe u v w x

namespace Langlands.Global.CuspidalBlockInduction

open AdelicBlockScalarSections (indexedEvaluation indexedEvaluation_tprod indexedEvaluation_injective)
open Automorphic InfinitePlaceFamily NumberField LocalFactor.Archimedean

section TensorMaps

variable {I : Type u} {A : I → Type v} {C : I → Type w} {K : I → Type x}
  [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)]
  [∀ i, AddCommGroup (C i)] [∀ i, Module ℂ (C i)]

private theorem tensorMap_family_injective_fin {k : ℕ}
    {A : Fin k → Type v} {C : Fin k → Type w} {K : Fin k → Type x}
    [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)]
    [∀ i, AddCommGroup (C i)] [∀ i, Module ℂ (C i)]
    (e : ∀ i, K i → A i →ₗ[ℂ] C i)
    (he : ∀ i, Function.Injective (fun a : A i => fun q => e i q a)) :
    Function.Injective (fun a : (⨂[ℂ] i, A i) => fun q : ∀ i, K i =>
      PiTensorProduct.map (fun i => e i (q i)) a) := by
  let L (i : Fin k) : A i →ₗ[ℂ] (K i × (C i →ₗ[ℂ] ℂ) → ℂ) :=
    LinearMap.pi fun q => q.2.comp (e i q.1)
  have hL (i : Fin k) : Function.Injective (L i) := by
    intro a b h
    apply he i
    funext q
    let basis := Module.Free.chooseBasis ℂ (C i)
    apply basis.repr.injective
    ext j
    exact congrFun h (q, basis.coord j)
  intro a b h
  apply indexedEvaluation_injective L hL
  funext q
  let s (i : Fin k) := e i (q i).1
  let φ := PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ (Fin k) ℂ).compLinearMap
    (fun i => (q i).2))
  have hcomp : (LinearMap.proj q).comp (indexedEvaluation L) = φ.comp (PiTensorProduct.map s) := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro y
    change indexedEvaluation L (PiTensorProduct.tprod ℂ y) q =
      φ (PiTensorProduct.map s (PiTensorProduct.tprod ℂ y))
    dsimp only [φ]
    rw [indexedEvaluation_tprod, PiTensorProduct.map_tprod, PiTensorProduct.lift.tprod]
    rfl
  exact (LinearMap.congr_fun hcomp a).trans
    ((congrArg φ (congrFun h (fun i => (q i).1))).trans (LinearMap.congr_fun hcomp b).symm)

/-- Tensor evaluations remain jointly injective when the evaluation arguments
vary independently in the finite collection of factors. -/
theorem tensorMap_family_injective [Finite I] (e : ∀ i, K i → A i →ₗ[ℂ] C i)
    (he : ∀ i, Function.Injective (fun a : A i => fun q => e i q a)) :
    Function.Injective (fun a : (⨂[ℂ] i, A i) => fun q : ∀ i, K i =>
      PiTensorProduct.map (fun i => e i (q i)) a) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let j := Fintype.equivFin I
  intro a b h
  apply (PiTensorProduct.reindex ℂ A j).injective
  apply tensorMap_family_injective_fin (fun i => e (j.symm i)) (fun i => he (j.symm i))
  funext q
  let q₀ := (Equiv.piCongrLeft' K j).symm q
  have hq (i : Fin (Fintype.card I)) : q₀ (j.symm i) = q i :=
    Equiv.piCongrLeft'_symm_apply_apply K j q i
  have h₁ := PiTensorProduct.map_reindex (fun i => e i (q₀ i)) j a
  have h₂ := PiTensorProduct.map_reindex (fun i => e i (q₀ i)) j b
  simp only [hq] at h₁ h₂
  exact h₁.trans ((congrArg (PiTensorProduct.reindex ℂ C j) (congrFun h q₀)).trans h₂.symm)

private theorem tensorMap_family_injective_of_surjective [Finite I] {P : Type*}
    (e : ∀ i, K i → A i →ₗ[ℂ] C i)
    (he : ∀ i, Function.Injective (fun a : A i => fun q => e i q a))
    (c : P → ∀ i, K i) (hc : Function.Surjective c) :
    Function.Injective (fun a : (⨂[ℂ] i, A i) => fun p : P =>
      PiTensorProduct.map (fun i => e i (c p i)) a) := by
  intro a b h
  apply tensorMap_family_injective e he
  funext q
  obtain ⟨p, rfl⟩ := hc q
  exact congrFun h p

end TensorMaps

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
variable {r k : ℕ} {m : Fin k → ℕ}
variable (real : {v : InfinitePlace F // v.IsReal} → Fin k → List RealBlock)
variable (complex : {v : InfinitePlace F // v.IsComplex} → Fin k → List ComplexCharacterData)
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

local notation "Coeff" => (fun p : Index F => ⨂[ℂ] i, OperatorRealization.PlaceDensityModels.subspace
  (CuspidalOperatorRealization.placeDensityModels (T i)) p)
local notation "Std" => infiniteStandardSpace r real complex
local notation "Comp" => Compact (r + 1) (F := F)

private theorem infiniteLocalEvaluation_injective (v : Index F) :
    Function.Injective (fun x : infiniteStandardSpace r real complex v => fun q =>
      infiniteLocalEvaluation real complex hm T hr hc v q x) := by
  intro a b h
  cases v with
  | inl v =>
    apply realPlaceEvaluation_injective hm T v (real v) (hr v)
    funext q
    let t : Compact (r + 1) (.inl v : Index F) := ⟨q.val.val, q.property⟩
    have ht : Archimedean.matrixUnitaryToCompact ℝ (r + 1) t = q := Subtype.ext (Units.ext rfl)
    have he := congrFun h t
    change realPlaceEvaluation hm T v (real v) (hr v) _ a =
      realPlaceEvaluation hm T v (real v) (hr v) _ b
    exact (congrArg (fun z => realPlaceEvaluation hm T v (real v) (hr v) z a) ht.symm).trans
      (he.trans (congrArg (fun z => realPlaceEvaluation hm T v (real v) (hr v) z b) ht))
  | inr v =>
    apply complexPlaceEvaluation_injective hm T v (complex v) (hc v)
    funext q
    let t : Compact (r + 1) (.inr v : Index F) := ⟨q.val.val, q.property⟩
    have ht : Archimedean.matrixUnitaryToCompact ℂ (r + 1) t = q := Subtype.ext (Units.ext rfl)
    have he := congrFun h t
    change complexPlaceEvaluation hm T v (complex v) (hc v) _ a =
      complexPlaceEvaluation hm T v (complex v) (hc v) _ b
    exact (congrArg (fun z => complexPlaceEvaluation hm T v (complex v) (hc v) z a) ht.symm).trans
      (he.trans (congrArg (fun z => complexPlaceEvaluation hm T v (complex v) (hc v) z b) ht))

/-- The simultaneous evaluation map on the actual infinite compact group. -/
def infiniteEvaluationFamily :
    (⨂[ℂ] v, Std v) →ₗ[ℂ]
      (standardInfiniteCompact F (r + 1) → (⨂[ℂ] v, Coeff v)) :=
  LinearMap.pi (infiniteEvaluation real complex hm T hr hc)

/-- Evaluation at all genuine infinite compact arguments detects every vector
of the original-order infinite standard tensor. -/
theorem infiniteEvaluation_injective :
    Function.Injective (infiniteEvaluationFamily real complex hm T hr hc) := by
  exact tensorMap_family_injective_of_surjective (I := Index F) (A := Std) (C := Coeff) (K := Comp)
    (infiniteLocalEvaluation real complex hm T hr hc)
    (infiniteLocalEvaluation_injective real complex hm T hr hc)
    (infiniteCompactCoordinates F (r + 1)) (infiniteCompactCoordinates F (r + 1)).surjective

end Langlands.Global.CuspidalBlockInduction
