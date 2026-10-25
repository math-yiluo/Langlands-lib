import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Smooth vectors and generic Banach representations of real Lie groups

A representation is a group homomorphism into the bounded complex operators of a
complex normed space. Smoothness is real smoothness of orbit maps on a Lie group
modelled by a real normed space `𝔤`; the model vector space is the tangent space at
the identity, so it plays the role of the real Lie algebra.
-/

noncomputable section

open scoped Manifold ContDiff Matrix

namespace Langlands.Archimedean

universe u𝔤 uH uG uE

variable {𝔤 : Type u𝔤} [NormedAddCommGroup 𝔤] [NormedSpace ℝ 𝔤]
  {H : Type uH} [TopologicalSpace H] (I : ModelWithCorners ℝ 𝔤 H)
  {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Joint continuity of the action map `G × E → E`. -/
def IsContinuousRepresentation (π : G →* (E →L[ℂ] E)) : Prop :=
  Continuous fun p : G × E => π p.1 p.2

/-- The orbit map `g ↦ π(g)v`. -/
def orbitMap (π : G →* (E →L[ℂ] E)) (v : E) : G → E :=
  fun g => π g v

/-- A smooth vector: its orbit map is real `C^∞`. -/
def IsSmoothVector (π : G →* (E →L[ℂ] E)) (v : E) : Prop :=
  ContMDiff I 𝓘(ℝ, E) ∞ (orbitMap π v)

/-- The complex subspace of smooth vectors. -/
def smoothVectors (π : G →* (E →L[ℂ] E)) : Submodule ℂ E where
  carrier := {v | IsSmoothVector I π v}
  zero_mem' := by
    change ContMDiff I 𝓘(ℝ, E) ∞ (fun g => π g 0)
    simp only [map_zero]
    exact contMDiff_const
  add_mem' {v w} hv hw := by
    change ContMDiff I 𝓘(ℝ, E) ∞ (fun g => π g (v + w))
    simp only [map_add]
    exact hv.add hw
  smul_mem' c v hv := by
    change ContMDiff I 𝓘(ℝ, E) ∞ (fun g => π g (c • v))
    simp only [map_smul]
    exact ((c • ContinuousLinearMap.id ℂ E).restrictScalars ℝ).contDiff.contMDiff.comp hv

theorem mem_smoothVectors_iff (π : G →* (E →L[ℂ] E)) (v : E) :
    v ∈ smoothVectors I π ↔ ContMDiff I 𝓘(ℝ, E) ∞ (fun g => π g v) :=
  Iff.rfl

/-- Topological irreducibility: a nonzero space without nontrivial closed invariant
subspaces. -/
def IsTopologicallyIrreducible (π : G →* (E →L[ℂ] E)) : Prop :=
  Nontrivial E ∧ ∀ W : Submodule ℂ E, IsClosed (W : Set E) →
    (∀ (g : G), ∀ w ∈ W, π g w ∈ W) → W = ⊥ ∨ W = ⊤

/-- The `K`-intertwiners from the matrix representation `τ` of `K` to `π`. -/
def intertwiners (π : G →* (E →L[ℂ] E)) (K : Subgroup G) (d : ℕ)
    (τ : K →* Matrix (Fin d) (Fin d) ℂ) : Submodule ℂ ((Fin d → ℂ) →ₗ[ℂ] E) where
  carrier := {T | ∀ (k : K) (x : Fin d → ℂ), T (τ k *ᵥ x) = π (k : G) (T x)}
  zero_mem' := by
    intro k x
    simp
  add_mem' {S T} hS hT := by
    intro k x
    simp [hS k x, hT k x]
  smul_mem' c T hT := by
    intro k x
    simp [hT k x]

/-- Admissibility for `K`: every continuous finite-dimensional representation of `K`
has a finite-dimensional space of intertwiners into `π`. -/
def IsAdmissible (π : G →* (E →L[ℂ] E)) (K : Subgroup G) : Prop :=
  ∀ (d : ℕ) (τ : K →* Matrix (Fin d) (Fin d) ℂ), Continuous τ →
    FiniteDimensional ℂ (intertwiners π K d τ)

/-- The derivative `dπ(X)v` of the orbit map at the identity in the tangent direction
`X`. -/
def lieDerivative (π : G →* (E →L[ℂ] E)) (X : 𝔤) (v : E) : E :=
  mfderiv I 𝓘(ℝ, E) (orbitMap π v) 1 X

/-- The iterated derivative `dπ(X₁)(dπ(X₂)(⋯ dπ(Xₖ)v))` of the word `[X₁, …, Xₖ]`. The
empty word gives `v`. -/
def iteratedLieDerivative (π : G →* (E →L[ℂ] E)) : List 𝔤 → E → E
  | [] => fun v => v
  | X :: Xs => fun v => lieDerivative I π X (iteratedLieDerivative π Xs v)

@[simp]
theorem iteratedLieDerivative_nil (π : G →* (E →L[ℂ] E)) (v : E) :
    iteratedLieDerivative I π [] v = v :=
  rfl

@[simp]
theorem iteratedLieDerivative_cons (π : G →* (E →L[ℂ] E)) (X : 𝔤) (Xs : List 𝔤) (v : E) :
    iteratedLieDerivative I π (X :: Xs) v =
      lieDerivative I π X (iteratedLieDerivative I π Xs v) :=
  rfl

/-- Continuity for the smooth-vector topology: a bound by finitely many of the seminorms
`v ↦ ‖dπ(X₁ ⋯ Xₖ)v‖`. -/
def IsContinuousOnSmoothVectors (π : G →* (E →L[ℂ] E))
    (ℓ : smoothVectors I π →ₗ[ℂ] ℂ) : Prop :=
  ∃ (S : Finset (List 𝔤)) (C : ℝ), ∀ v : smoothVectors I π,
    ‖ℓ v‖ ≤ C * ∑ Xs ∈ S, ‖iteratedLieDerivative I π Xs v‖

variable [LieGroup I ∞ G]

/-- Smooth vectors are invariant: the orbit map of `π(h)v` is right translation by `h`
of the orbit map of `v`. -/
theorem isSmoothVector_apply (π : G →* (E →L[ℂ] E)) {v : E} (hv : IsSmoothVector I π v)
    (h : G) : IsSmoothVector I π (π h v) := by
  have hr : ContMDiff I I ∞ (fun g : G => g * h) := contMDiff_mul_right
  have hc := hv.comp hr
  change ContMDiff I 𝓘(ℝ, E) ∞ (fun g => π g (π h v))
  have he : (fun g => π g (π h v)) = (orbitMap π v) ∘ (fun g : G => g * h) := by
    funext g
    simp [orbitMap, map_mul]
  rw [he]
  exact hc

/-- The representation of `G` on its smooth vectors. -/
def smoothRepresentation (π : G →* (E →L[ℂ] E)) :
    G →* (smoothVectors I π →ₗ[ℂ] smoothVectors I π) where
  toFun g :=
    { toFun v := ⟨π g v, isSmoothVector_apply I π v.property g⟩
      map_add' v w := Subtype.ext (map_add (π g) v.val w.val)
      map_smul' c v := Subtype.ext (map_smul (π g) c v.val) }
  map_one' := by
    ext v
    simp
  map_mul' g h := by
    ext v
    simp

@[simp]
theorem smoothRepresentation_apply (π : G →* (E →L[ℂ] E)) (g : G) (v : smoothVectors I π) :
    (smoothRepresentation I π g v : E) = π g v :=
  rfl

/-- A `χ`-Whittaker functional (Shahidi 1985, (1.1)): a continuous functional on
smooth vectors with `ℓ(π(u)v) = χ(u)ℓ(v)` for `u ∈ N`. -/
def IsWhittakerFunctional (π : G →* (E →L[ℂ] E)) (N : Subgroup G) (χ : N →* ℂˣ)
    (ℓ : smoothVectors I π →ₗ[ℂ] ℂ) : Prop :=
  IsContinuousOnSmoothVectors I π ℓ ∧
    ∀ (u : N) (v : smoothVectors I π),
      ℓ (smoothRepresentation I π (u : G) v) = (χ u : ℂ) * ℓ v

/-- `χ`-generic: a nonzero `χ`-Whittaker functional exists. -/
def IsGeneric (π : G →* (E →L[ℂ] E)) (N : Subgroup G) (χ : N →* ℂˣ) : Prop :=
  ∃ ℓ : smoothVectors I π →ₗ[ℂ] ℂ, ℓ ≠ 0 ∧ IsWhittakerFunctional I π N χ ℓ

/-- An irreducible admissible `χ`-generic Banach representation (Shahidi 1985, §3). -/
def IsIrreducibleAdmissibleGeneric [CompleteSpace E] (π : G →* (E →L[ℂ] E))
    (K N : Subgroup G) (χ : N →* ℂˣ) : Prop :=
  IsContinuousRepresentation π ∧ IsTopologicallyIrreducible π ∧ IsAdmissible π K ∧
    IsGeneric I π N χ

end Langlands.Archimedean
