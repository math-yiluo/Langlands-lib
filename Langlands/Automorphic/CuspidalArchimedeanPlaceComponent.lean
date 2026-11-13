import Langlands.Automorphic.PlaceCompactAction
import Langlands.Automorphic.PlaceLieAction
import Langlands.Automorphic.CuspidalOperatorRealization

/-! # Irreducible admissible components and Whittaker functionals at infinite places

At an infinite place `v`, an actual automorphic operator realization carries the compact
action of `K_v` (`O(n)` or `U(n)`) and the complexified Lie action of `𝔤𝔩_n(F_v)` of its
published place actions. For a subspace `W` of a carrier with such a pair of actions, this
module defines stability, irreducibility, admissibility, and Whittaker functionals for a
nondegenerate character of the strictly upper triangular Lie algebra. It states two
propositions about actual cuspidal realizations:

* `CuspidalArchimedeanIrreducibleAdmissibleComponentStatement`: at every infinite place,
  every actual cuspidal realization of `GL_{r+1}` has an irreducible admissible
  place-stable subspace;
* `CuspidalArchimedeanWhittakerFunctionalStatement`: every nonzero place-stable subspace of
  a cuspidal operator realization carries a Whittaker functional, nonzero on it, for some
  nondegenerate character.

Neither proposition is proved here.
-/

noncomputable section

universe u

open scoped TensorProduct Matrix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

attribute [local instance 100] LieRing.ofAssociativeRing

namespace PlaceComponent

section Abstract

variable {K : Type*} [Group K] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
  {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- `W` is stable under every compact operator `κ k` and every Lie operator `π X`. -/
def IsStable (κ : Representation ℂ K V) (π : 𝔤 →ₗ⁅ℂ⁆ Module.End ℂ V)
    (W : Submodule ℂ V) : Prop :=
  (∀ (k : K), ∀ x ∈ W, κ k x ∈ W) ∧ ∀ (X : 𝔤), ∀ x ∈ W, π X x ∈ W

/-- `W` is a nonzero stable subspace whose only stable subspaces are `⊥` and `W`. -/
def IsIrreducible (κ : Representation ℂ K V) (π : 𝔤 →ₗ⁅ℂ⁆ Module.End ℂ V)
    (W : Submodule ℂ V) : Prop :=
  W ≠ ⊥ ∧ IsStable κ π W ∧
    ∀ W' : Submodule ℂ V, W' ≤ W → IsStable κ π W' → W' = ⊥ ∨ W' = W

/-- The linear maps `T : ℂ^d → V` with values in `W` that intertwine the matrix
representation `τ` of `K` with `κ`: `T (τ k x) = κ k (T x)`. -/
def intertwiners (κ : Representation ℂ K V) (W : Submodule ℂ V) (d : ℕ)
    (τ : K →* Matrix (Fin d) (Fin d) ℂ) : Submodule ℂ ((Fin d → ℂ) →ₗ[ℂ] V) where
  carrier := {T | (∀ x, T x ∈ W) ∧ ∀ (k : K) (x : Fin d → ℂ), T (τ k *ᵥ x) = κ k (T x)}
  add_mem' := by
    rintro S T ⟨hS, hS'⟩ ⟨hT, hT'⟩
    refine ⟨fun x => W.add_mem (hS x) (hT x), fun k x => ?_⟩
    simp only [LinearMap.add_apply, map_add, hS', hT']
  zero_mem' := ⟨fun _ => W.zero_mem, fun k x => by simp⟩
  smul_mem' := by
    rintro c T ⟨hT, hT'⟩
    refine ⟨fun x => W.smul_mem c (hT x), fun k x => ?_⟩
    simp only [LinearMap.smul_apply, map_smul, hT']

theorem mem_intertwiners (κ : Representation ℂ K V) (W : Submodule ℂ V) (d : ℕ)
    (τ : K →* Matrix (Fin d) (Fin d) ℂ) (T : (Fin d → ℂ) →ₗ[ℂ] V) :
    T ∈ intertwiners κ W d τ ↔
      (∀ x, T x ∈ W) ∧ ∀ (k : K) (x : Fin d → ℂ), T (τ k *ᵥ x) = κ k (T x) :=
  Iff.rfl

/-- Admissibility of `W` for `K`: for every continuous finite-dimensional matrix
representation `τ` of `K`, the space of `K`-intertwiners from `τ` into `W` is
finite-dimensional. -/
def IsAdmissible [TopologicalSpace K] (κ : Representation ℂ K V) (W : Submodule ℂ V) :
    Prop :=
  ∀ (d : ℕ) (τ : K →* Matrix (Fin d) (Fin d) ℂ), Continuous τ →
    FiniteDimensional ℂ (intertwiners κ W d τ)

end Abstract

section Whittaker

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}

/-- `ℓ` is a Whittaker functional on `W` at a real place for the character with coefficients
`a`: for every strictly upper triangular real matrix `X` and every `x ∈ W`,
`ℓ (π (1 ⊗ X) x) = i · (∑ᵢ aᵢ X_{i,i+1}) · ℓ x`. -/
def IsRealWhittakerFunctional
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (W : Submodule ℂ V) (a : Fin n → ℝ) (ℓ : V →ₗ[ℂ] ℂ) : Prop :=
  ∀ X : Matrix (Fin n) (Fin n) ℝ, (∀ i j : Fin n, (j : ℕ) ≤ i → X i j = 0) →
    ∀ x ∈ W, ℓ (π (1 ⊗ₜ X) x) =
      (Complex.I * ((∑ i : Fin n, ∑ j : Fin n,
        if (j : ℕ) = i + 1 then a i * X i j else 0 : ℝ) : ℂ)) * ℓ x

/-- `ℓ` is a Whittaker functional on `W` at a complex place for the character with
coefficients `a`: for every strictly upper triangular complex matrix `X`, a real direction of
`𝔤𝔩_n(ℂ)`, and every `x ∈ W`, `ℓ (π (1 ⊗ X) x) = i · Re (∑ᵢ aᵢ X_{i,i+1}) · ℓ x`. -/
def IsComplexWhittakerFunctional
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (W : Submodule ℂ V) (a : Fin n → ℂ) (ℓ : V →ₗ[ℂ] ℂ) : Prop :=
  ∀ X : Matrix (Fin n) (Fin n) ℂ, (∀ i j : Fin n, (j : ℕ) ≤ i → X i j = 0) →
    ∀ x ∈ W, ℓ (π (1 ⊗ₜ X) x) =
      (Complex.I * (((∑ i : Fin n, ∑ j : Fin n,
        if (j : ℕ) = i + 1 then a i * X i j else 0 : ℂ).re : ℝ) : ℂ)) * ℓ x

/-- `W` carries a real-place Whittaker functional, nonzero on `W`, for some nondegenerate
character: all coefficients `aᵢ` with `i + 1 < n` are nonzero. -/
def IsRealGeneric
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (W : Submodule ℂ V) : Prop :=
  ∃ a : Fin n → ℝ, (∀ i : Fin n, (i : ℕ) + 1 < n → a i ≠ 0) ∧
    ∃ ℓ : V →ₗ[ℂ] ℂ, (∃ x ∈ W, ℓ x ≠ 0) ∧ IsRealWhittakerFunctional π W a ℓ

/-- `W` carries a complex-place Whittaker functional, nonzero on `W`, for some
nondegenerate character: all coefficients `aᵢ` with `i + 1 < n` are nonzero. -/
def IsComplexGeneric
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (W : Submodule ℂ V) : Prop :=
  ∃ a : Fin n → ℂ, (∀ i : Fin n, (i : ℕ) + 1 < n → a i ≠ 0) ∧
    ∃ ℓ : V →ₗ[ℂ] ℂ, (∃ x ∈ W, ℓ x ≠ 0) ∧ IsComplexWhittakerFunctional π W a ℓ

end Whittaker

end PlaceComponent

open Langlands.Global

local instance placeComponentRationalAddCommGroup {F : Type u} [Field F] [NumberField F]
    {n : ℕ} : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance placeComponentContinuousAddCommGroup {F : Type u} [Field F] [NumberField F]
    {n : ℕ} : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance placeComponentSmoothAddCommGroup {F : Type u} [Field F] [NumberField F]
    {n : ℕ} : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance placeComponentFormsAddCommGroup {F : Type u} [Field F] [NumberField F]
    {n : ℕ} : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance placeComponentStableAddCommGroup {F : Type u} [Field F] [NumberField F]
    {n : ℕ} : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance placeComponentSpaceAddCommGroup {F : Type u} [Field F] [NumberField F]
    {n : ℕ} (S : OperatorRealization F n) : AddCommGroup S.Space := Submodule.addCommGroup _

/-- **Irreducible admissible place components.** Let `F` be a number field whose adele
quotient is compact and let `T` be an actual cuspidal realization of `GL_{r+1}`. At every
real place `v` there is a subspace of `T` that is irreducible for the
`(𝔤𝔩_{r+1}(ℝ), O(r+1))` place actions at `v` and admissible for `O(r+1)`, and at every
complex place `v` there is one that is irreducible for the `(𝔤𝔩_{r+1}(ℂ), U(r+1))` place
actions at `v` and admissible for `U(r+1)`. -/
def CuspidalArchimedeanIrreducibleAdmissibleComponentStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (Global.AdeleQuotient F)] (r : ℕ)
    (T : CuspidalOperatorRealization F r),
    (∀ v : {v : NumberField.InfinitePlace F // v.IsReal},
      ∃ W : Submodule ℂ T.realization.Space,
        PlaceComponent.IsIrreducible (T.realization.realPlaceCompactRepresentation v)
            (T.realization.realPlaceLieAction v) W ∧
          PlaceComponent.IsAdmissible (T.realization.realPlaceCompactRepresentation v) W) ∧
    ∀ v : {v : NumberField.InfinitePlace F // v.IsComplex},
      ∃ W : Submodule ℂ T.realization.Space,
        PlaceComponent.IsIrreducible (T.realization.complexPlaceCompactRepresentation v)
            (T.realization.complexPlaceLieAction v) W ∧
          PlaceComponent.IsAdmissible (T.realization.complexPlaceCompactRepresentation v) W

/-- **Place Whittaker functionals.** Let `F` be a number field whose adele quotient is
compact and let `S` be a cuspidal actual operator realization of `GL_{r+1}`. Every nonzero
subspace of `S` stable under the compact and Lie place actions at an infinite place `v`
carries a linear functional on `S`, nonzero on the subspace, that is a Whittaker functional
on it for some nondegenerate character of the strictly upper triangular Lie algebra at
`v`. -/
def CuspidalArchimedeanWhittakerFunctionalStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (Global.AdeleQuotient F)] (r : ℕ)
    (S : OperatorRealization F (r + 1)), S.IsCuspidal →
    (∀ (v : {v : NumberField.InfinitePlace F // v.IsReal}) (W : Submodule ℂ S.Space),
      W ≠ ⊥ →
      PlaceComponent.IsStable (S.realPlaceCompactRepresentation v)
          (S.realPlaceLieAction v) W →
        PlaceComponent.IsRealGeneric (S.realPlaceLieAction v) W) ∧
    ∀ (v : {v : NumberField.InfinitePlace F // v.IsComplex}) (W : Submodule ℂ S.Space),
      W ≠ ⊥ →
      PlaceComponent.IsStable (S.complexPlaceCompactRepresentation v)
          (S.complexPlaceLieAction v) W →
        PlaceComponent.IsComplexGeneric (S.complexPlaceLieAction v) W

end Langlands.Automorphic
