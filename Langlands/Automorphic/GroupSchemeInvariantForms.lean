import Langlands.Automorphic.GroupSchemeForms

/-! # Automorphic functions on `Γ \ G(𝔸)` for an arbitrary subgroup `Γ`

Mœglin–Waldspurger I.2.17: for a standard parabolic `P = MU`, a function on
`U(𝔸)M(F) \ G(𝔸)` is automorphic if it has moderate growth, is smooth,
`K`-finite and `𝔷`-finite. The conditions are formulated here for plain
complex functions on the actual adelic points `G(𝔸)` that are left invariant
under an arbitrary subgroup `Γ`, using the same smooth slices, finite level,
infinite compact subgroup, enveloping-algebra center and adelic norm as the
existing forms on `G(F) \ G(𝔸)`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.InfiniteAdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]

/-- The infinite slice `a ↦ φ(a, b)` of a function on the actual adelic points
at a fixed finite adelic point `b`. -/
def functionInfiniteSlice (φ : AdelicGroupPoints F G → ℂ) (b : FiniteAdelicGroupPoints F G) :
    InfiniteAdelicGroupPoints F G → ℂ :=
  fun a => φ (AdelicGroupPoints.pair F G a b)

/-- Left invariance of a function on the actual adelic points under a subgroup. -/
def IsLeftInvariantUnder (Γ : Subgroup (AdelicGroupPoints F G))
    (φ : AdelicGroupPoints F G → ℂ) : Prop :=
  ∀ x ∈ Γ, ∀ g : AdelicGroupPoints F G, φ (x * g) = φ g

/-- Smoothness (Mœglin–Waldspurger I.2.5): the function is continuous, every
infinite slice is plot-smooth, and one open subgroup of the finite adelic
points fixes the function under right translation. -/
def IsAdelicSmoothFunction (φ : AdelicGroupPoints F G → ℂ) : Prop :=
  Continuous φ ∧
    (∀ b : FiniteAdelicGroupPoints F G,
      functionInfiniteSlice F G φ b ∈ InfinitePlotSmoothFunctions F G) ∧
    ∃ L : Subgroup (FiniteAdelicGroupPoints F G), IsOpen (L : Set (FiniteAdelicGroupPoints F G)) ∧
      ∀ l ∈ L, ∀ g : AdelicGroupPoints F G, φ (g * AdelicGroupPoints.ofFinite F G l) = φ g

/-- Finiteness under a specified subgroup `Kinf` of the infinite adelic points:
the right translates of the function by `Kinf` span a finite-dimensional space. -/
def IsInfiniteSubgroupFiniteFunction (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))
    (φ : AdelicGroupPoints F G → ℂ) : Prop :=
  FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : Kinf =>
    fun g : AdelicGroupPoints F G => φ (g * AdelicGroupPoints.ofInfinite F G k)))

/-- Moderate growth for the exact adelic norm of a specified matrix
representation: `|φ(g)| ≤ C ‖g‖^r` for some `C > 0` and real `r`. -/
def HasModerateGrowthFunction {N : ℕ} (rho : Langlands.GroupScheme.MatrixRepresentation G (Fin N))
    (φ : AdelicGroupPoints F G → ℂ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ r : ℝ, ∀ g : AdelicGroupPoints F G,
    ‖φ g‖ ≤ C * RepresentationGrowth.adelicSourceNorm F G rho g ^ r

variable {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)

/-- `𝔷`-finiteness: one ideal of finite codimension in the center of the actual
complex enveloping algebra annihilates every infinite slice of the function
under the existing center action. -/
def IsCenterFiniteFunction (φ : AdelicGroupPoints F G → ℂ) : Prop :=
  ∃ J : Ideal (AdelicEnvelopingCenter F G hsmooth),
    Module.Finite ℂ (AdelicEnvelopingCenter F G hsmooth ⧸ J.restrictScalars ℂ) ∧
    ∀ z ∈ J, ∀ b : FiniteAdelicGroupPoints F G,
      ∀ h : functionInfiniteSlice F G φ b ∈ InfinitePlotSmoothFunctions F G,
        plotSmoothCenterAction F G hsmooth hcalc z ⟨functionInfiniteSlice F G φ b, h⟩ = 0

/-- Automorphic functions on `Γ \ G(𝔸)` (Mœglin–Waldspurger I.2.17): left
invariance under `Γ`, smoothness, finiteness under the specified infinite
compact subgroup `Kinf`, `𝔷`-finiteness and moderate growth. -/
def IsAutomorphicFunctionOn (Γ : Subgroup (AdelicGroupPoints F G))
    (Kinf : Subgroup (InfiniteAdelicGroupPoints F G)) {N : ℕ}
    (rho : Langlands.GroupScheme.MatrixRepresentation G (Fin N))
    (φ : AdelicGroupPoints F G → ℂ) : Prop :=
  IsLeftInvariantUnder F G Γ φ ∧ IsAdelicSmoothFunction F G φ ∧
    IsInfiniteSubgroupFiniteFunction F G Kinf φ ∧ IsCenterFiniteFunction F G hsmooth hcalc φ ∧
    HasModerateGrowthFunction F G rho φ

end Langlands.Automorphic.GroupSchemeFunctions
