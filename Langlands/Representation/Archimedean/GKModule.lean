import Mathlib.Algebra.Lie.BaseChange
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.RepresentationTheory.Basic
import Mathlib.Topology.Instances.Matrix
import Langlands.Representation.FiniteVectors
import Langlands.Representation.Archimedean.StandardModule

/-!
# Algebraic `(𝔤, K)`-modules of `GL_n(ℝ)` and `GL_n(ℂ)`

A `(𝔤, K)`-module of `GL_n(F)`, `F = ℝ` or `ℂ`, is a complex vector space `V` with a
representation `ρ` of the standard maximal compact subgroup `K = O(n)` or `U(n)` and a
complex Lie algebra action `π` of the complexified Lie algebra `ℂ ⊗_ℝ 𝔤𝔩_n(F)`, such that
every vector is `K`-finite, `K` acts continuously on finite-dimensional subspaces, the
derivative of `ρ` is `π` on the Lie algebra of `K`, and `ρ(k) π(X) ρ(k)⁻¹ = π(Ad(k) X)`
(Getz–Hahn 2024, Definition 4.4.6). This file states these conditions, irreducibility,
admissibility (Getz–Hahn, Definition 4.4.4 and p. 116) and genericity: a nonzero linear
functional on `V` on which the nilpotent radical `𝔫` of the upper triangular Borel subalgebra
acts by the differential of a nondegenerate character of `N(F)` (the infinitesimal,
`K`-finite form of Getz–Hahn, Definitions 11.2.1 and 11.3.2). No topology on `V` is used.
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

universe uK uL uV

section General

variable {K : Type uK} [Group K] {L : Type uL} [LieRing L] [LieAlgebra ℂ L]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Irreducibility of a `(𝔤, K)`-module (Getz–Hahn, p. 116): `V` is nonzero and has no
subspace other than `0` and `V` stable under both `ρ` and `π`. -/
def IsIrreducibleGKModule (ρ : Representation ℂ K V) (π : L →ₗ⁅ℂ⁆ Module.End ℂ V) : Prop :=
  Nontrivial V ∧ ∀ W : Submodule ℂ V, (∀ (k : K), ∀ w ∈ W, ρ k w ∈ W) →
    (∀ (X : L), ∀ w ∈ W, π X w ∈ W) → W = ⊥ ∨ W = ⊤

/-- The `K`-intertwiners from the matrix representation `τ` of `K` to `ρ`. -/
def gkIntertwiners (ρ : Representation ℂ K V) (d : ℕ) (τ : K →* Matrix (Fin d) (Fin d) ℂ) :
    Submodule ℂ ((Fin d → ℂ) →ₗ[ℂ] V) where
  carrier := {T | ∀ (k : K) (x : Fin d → ℂ), T (τ k *ᵥ x) = ρ k (T x)}
  zero_mem' := by
    intro k x
    simp
  add_mem' {S T} hS hT := by
    intro k x
    simp [hS k x, hT k x]
  smul_mem' c T hT := by
    intro k x
    simp [hT k x]

/-- Admissibility (Getz–Hahn, Definition 4.4.4 and p. 116): every continuous
finite-dimensional representation of `K` has a finite-dimensional space of `K`-intertwiners
into `ρ`. For a `K`-finite `V` with continuous finite-dimensional subrepresentations this says
that every isotypic component `V(σ)` is finite-dimensional. -/
def IsAdmissibleGKModule [TopologicalSpace K] (ρ : Representation ℂ K V) : Prop :=
  ∀ (d : ℕ) (τ : K →* Matrix (Fin d) (Fin d) ℂ), Continuous τ →
    FiniteDimensional ℂ (gkIntertwiners ρ d τ)

end General

section Real

variable (n : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- `(ρ, π)` is a `(𝔤𝔩_n(ℝ), O(n))`-module (Getz–Hahn, Definition 4.4.6): every vector is
`O(n)`-finite; for every vector `v` and every linear functional `ℓ`, `k ↦ ℓ(ρ(k) v)` is
continuous; along every curve `γ` in `O(n)` with `γ(0) = 1` whose entries are differentiable
at `0` with derivative matrix `X`, the function `t ↦ ℓ(ρ(γ(t)) v)` has derivative
`ℓ(π(1 ⊗ X) v)` at `0`; and `ρ(k) π(1 ⊗ X) = π(1 ⊗ k X kᵀ) ρ(k)`. -/
def IsRealGKModule (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V) : Prop :=
  (∀ v : V, FiniteVectors.IsFiniteVector ρ v) ∧
  (∀ (v : V) (ℓ : V →ₗ[ℂ] ℂ), Continuous fun k : Matrix.unitaryGroup (Fin n) ℝ => ℓ (ρ k v)) ∧
  (∀ (γ : ℝ → Matrix.unitaryGroup (Fin n) ℝ) (X : Matrix (Fin n) (Fin n) ℝ), γ 0 = 1 →
    (∀ i j, HasDerivAt (fun t => (γ t : Matrix (Fin n) (Fin n) ℝ) i j) (X i j) 0) →
      ∀ (v : V) (ℓ : V →ₗ[ℂ] ℂ),
        HasDerivAt (fun t => ℓ (ρ (γ t) v)) (ℓ (π (1 ⊗ₜ X) v)) 0) ∧
  ∀ (k : Matrix.unitaryGroup (Fin n) ℝ) (X : Matrix (Fin n) (Fin n) ℝ) (v : V),
    ρ k (π (1 ⊗ₜ X) v) =
      π (1 ⊗ₜ ((k : Matrix (Fin n) (Fin n) ℝ) * X * (star k : Matrix (Fin n) (Fin n) ℝ)))
        (ρ k v)

/-- `π` is generic: there is a nonzero linear functional `ℓ` on `V` and real numbers
`a₀, …, a_{n-2}`, all nonzero, such that every strictly upper triangular real matrix `X`
acts on `ℓ` by the differential `i · ∑ᵢ aᵢ X_{i,i+1}` of the nondegenerate character
`u ↦ exp(i ∑ᵢ aᵢ u_{i,i+1})` of the upper unipotent group: `ℓ(π(1 ⊗ X) v) =
(i ∑ᵢ aᵢ X_{i,i+1}) ℓ(v)`. -/
def IsRealGenericGKModule (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V) :
    Prop :=
  ∃ ℓ : V →ₗ[ℂ] ℂ, ℓ ≠ 0 ∧ ∃ a : Fin n → ℝ, (∀ i : Fin n, (i : ℕ) + 1 < n → a i ≠ 0) ∧
    ∀ X : Matrix (Fin n) (Fin n) ℝ, (∀ i j : Fin n, (j : ℕ) ≤ i → X i j = 0) →
      ∀ v : V, ℓ (π (1 ⊗ₜ X) v) =
        (Complex.I * ((∑ i : Fin n, ∑ j : Fin n,
          if (j : ℕ) = i + 1 then a i * X i j else 0 : ℝ) : ℂ)) * ℓ v

end Real

section Complex

variable (n : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- `(ρ, π)` is a `(𝔤𝔩_n(ℂ), U(n))`-module (Getz–Hahn, Definition 4.4.6), with
`𝔤𝔩_n(ℂ)` regarded as a real Lie algebra and complexified: every vector is `U(n)`-finite;
for every vector `v` and every linear functional `ℓ`, `k ↦ ℓ(ρ(k) v)` is continuous; along
every curve `γ` in `U(n)` with `γ(0) = 1` whose entries are differentiable at `0` with
derivative matrix `X`, the function `t ↦ ℓ(ρ(γ(t)) v)` has derivative `ℓ(π(1 ⊗ X) v)` at
`0`; and `ρ(k) π(1 ⊗ X) = π(1 ⊗ k X k*) ρ(k)`. -/
def IsComplexGKModule (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V) : Prop :=
  (∀ v : V, FiniteVectors.IsFiniteVector ρ v) ∧
  (∀ (v : V) (ℓ : V →ₗ[ℂ] ℂ), Continuous fun k : Matrix.unitaryGroup (Fin n) ℂ => ℓ (ρ k v)) ∧
  (∀ (γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ) (X : Matrix (Fin n) (Fin n) ℂ), γ 0 = 1 →
    (∀ i j, HasDerivAt (fun t => (γ t : Matrix (Fin n) (Fin n) ℂ) i j) (X i j) 0) →
      ∀ (v : V) (ℓ : V →ₗ[ℂ] ℂ),
        HasDerivAt (fun t => ℓ (ρ (γ t) v)) (ℓ (π (1 ⊗ₜ X) v)) 0) ∧
  ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (X : Matrix (Fin n) (Fin n) ℂ) (v : V),
    ρ k (π (1 ⊗ₜ X) v) =
      π (1 ⊗ₜ ((k : Matrix (Fin n) (Fin n) ℂ) * X * (star k : Matrix (Fin n) (Fin n) ℂ)))
        (ρ k v)

/-- `π` is generic: there is a nonzero linear functional `ℓ` on `V` and complex numbers
`a₀, …, a_{n-2}`, all nonzero, such that every strictly upper triangular complex matrix `X`
acts on `ℓ` by the differential `i · Re(∑ᵢ aᵢ X_{i,i+1})` of the nondegenerate character
`u ↦ exp(i Re(∑ᵢ aᵢ u_{i,i+1}))` of the upper unipotent group: `ℓ(π(1 ⊗ X) v) =
(i Re(∑ᵢ aᵢ X_{i,i+1})) ℓ(v)`. -/
def IsComplexGenericGKModule
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V) : Prop :=
  ∃ ℓ : V →ₗ[ℂ] ℂ, ℓ ≠ 0 ∧ ∃ a : Fin n → ℂ, (∀ i : Fin n, (i : ℕ) + 1 < n → a i ≠ 0) ∧
    ∀ X : Matrix (Fin n) (Fin n) ℂ, (∀ i j : Fin n, (j : ℕ) ≤ i → X i j = 0) →
      ∀ v : V, ℓ (π (1 ⊗ₜ X) v) =
        (Complex.I * (((∑ i : Fin n, ∑ j : Fin n,
          if (j : ℕ) = i + 1 then a i * X i j else 0 : ℂ).re : ℝ) : ℂ)) * ℓ v

end Complex

section Parameters

open Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator

-- As in `StandardModule`: the charts on units need reduction through the normed-ring
-- instances of matrices.
set_option backward.isDefEq.respectTransparency false

variable (n : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- `(ρ, π)` has the standard-module parameter of the real blocks `ds`, in the given order:
the blocks have total rank `n`, and there is an injective linear map `A` from the
`O(n)`-finite functions of their standard module into `V` carrying right translation by
`k ∈ O(n)` to `ρ(k)` and the right derivative along `X ∈ 𝔤𝔩_n(ℝ)` to `π(1 ⊗ X)`. -/
def HasRealStandardParameter (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V) (ds : List RealBlock) :
    Prop :=
  realRank ds = n ∧
    ∃ A : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) →ₗ[ℂ] V,
      Function.Injective A ∧
      (∀ (k : unitaryCompact ℝ n)
          (f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)),
        ∃ hf : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
            (k : Langlands.GeneralLinear n ℝ) (f : Langlands.GeneralLinear n ℝ → ℂ) ∈
              kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n),
          A ⟨_, hf⟩ =
            ρ ⟨((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ), k.2⟩ (A f)) ∧
      ∀ (X : Matrix (Fin n) (Fin n) ℝ)
          (f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)),
        ∃ hf : rightDerivative (matrixModel ℝ n) X (f : Langlands.GeneralLinear n ℝ → ℂ) ∈
            kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n),
          A ⟨_, hf⟩ = π (1 ⊗ₜ X) (A f)

/-- `(ρ, π)` has the standard-module parameter of the complex blocks `ds`, in the given
order: there are `n` blocks, and there is an injective linear map `A` from the `U(n)`-finite
functions of their standard module into `V` carrying right translation by `k ∈ U(n)` to
`ρ(k)` and the right derivative along a real direction `X ∈ 𝔤𝔩_n(ℂ)` to `π(1 ⊗ X)`. -/
def HasComplexStandardParameter (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (ds : List ComplexCharacterData) : Prop :=
  ds.length = n ∧
    ∃ A : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n) →ₗ[ℂ] V,
      Function.Injective A ∧
      (∀ (k : unitaryCompact ℂ n)
          (f : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)),
        ∃ hf : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ)
            (k : Langlands.GeneralLinear n ℂ) (f : Langlands.GeneralLinear n ℂ → ℂ) ∈
              kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n),
          A ⟨_, hf⟩ =
            ρ ⟨((k : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ), k.2⟩ (A f)) ∧
      ∀ (X : Matrix (Fin n) (Fin n) ℂ)
          (f : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)),
        ∃ hf : rightDerivative (matrixModel ℂ n) X (f : Langlands.GeneralLinear n ℂ → ℂ) ∈
            kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n),
          A ⟨_, hf⟩ = π (1 ⊗ₜ X) (A f)

end Parameters

/-! ## The local statements -/

open Langlands.LocalFactor.Archimedean

/-- Every irreducible admissible generic `(𝔤𝔩_n(ℝ), O(n))`-module has the standard-module
parameter of some list of real blocks. Its content is the Langlands classification of
`GL_n(ℝ)` together with the irreducibility of the standard module of a generic irreducible
representation (Vogan, Kostant, Matumoto, Jacquet); see the Markdown. -/
def RealGenericStandardParameterStatement : Prop :=
  ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V),
    IsRealGKModule n ρ π → IsIrreducibleGKModule ρ π → IsAdmissibleGKModule ρ →
      IsRealGenericGKModule n π → ∃ ds : List RealBlock, HasRealStandardParameter n ρ π ds

/-- Every irreducible admissible generic `(𝔤𝔩_n(ℂ), U(n))`-module has the standard-module
parameter of some list of complex characters, that is, embeds in a principal series of
`GL_n(ℂ)` that it then exhausts. See the Markdown for the sources. -/
def ComplexGenericStandardParameterStatement : Prop :=
  ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V),
    IsComplexGKModule n ρ π → IsIrreducibleGKModule ρ π → IsAdmissibleGKModule ρ →
      IsComplexGenericGKModule n π →
        ∃ ds : List ComplexCharacterData, HasComplexStandardParameter n ρ π ds

end Langlands.Archimedean
