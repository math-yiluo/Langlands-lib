import Langlands.Automorphic.CochainCompactDifferentiation
import Langlands.Global.ArchimedeanReducedProjection
import Langlands.Global.ArchimedeanHorizontal

/-! # Actual infinitesimal compact equivariance on reduced horizontal cochains -/

noncomputable section

universe u v

open scoped TensorProduct Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] (n : ℕ) [NeZero n]
  {V : Type v} [AddCommGroup V] [Module ℂ V]

/-- Extend a reduced alternating cochain by the actual split-center retraction. -/
def reducedCochainExtension (q : ℕ) :
    ((ReducedComplexLieAlgebra K n) [⋀^Fin q]→ₗ[ℂ] V) →ₗ[ℂ]
      ((ComplexLieAlgebra K n) [⋀^Fin q]→ₗ[ℂ] V) where
  toFun f := f.compLinearMap (reducedComplexProjection K n).toLinearMap
  map_add' f g := by
    apply AlternatingMap.ext
    intro X
    rfl
  map_smul' z f := by
    apply AlternatingMap.ext
    intro X
    rfl

@[simp]
theorem reducedCochainExtension_apply (q : ℕ)
    (f : (ReducedComplexLieAlgebra K n) [⋀^Fin q]→ₗ[ℂ] V)
    (X : Fin q → ComplexLieAlgebra K n) :
    reducedCochainExtension K n q f X =
      f (fun i => reducedComplexProjection K n (X i)) := rfl

@[simp]
theorem reducedCochainExtension_inclusion (q : ℕ)
    (f : (ReducedComplexLieAlgebra K n) [⋀^Fin q]→ₗ[ℂ] V)
    (X : Fin q → ReducedComplexLieAlgebra K n) :
    reducedCochainExtension K n q f (fun i => reducedComplexInclusion K n (X i)) =
      f X := by
  simp only [reducedCochainExtension_apply, reducedComplexProjection_inclusion]

theorem reducedCochainExtension_injective (q : ℕ) :
    Function.Injective (reducedCochainExtension K n q (V := V)) := by
  intro f g h
  apply AlternatingMap.ext
  intro X
  have he := congrArg
    (fun A : (ComplexLieAlgebra K n) [⋀^Fin q]→ₗ[ℂ] V =>
      A (fun i => reducedComplexInclusion K n (X i))) h
  simpa only [reducedCochainExtension_inclusion] using he

/-- Full compact equivariance is preserved by the actual reduced extension. -/
theorem reducedCochainExtension_equivariant
    (ρ : Representation ℂ (standardInfiniteCompact K n) V) (q : ℕ)
    (f : (ReducedComplexLieAlgebra K n) [⋀^Fin q]→ₗ[ℂ] V)
    (hf : f ∈ HorizontalAlternating.equivariant
      (reducedCompactRepresentation K n) ρ q) :
    reducedCochainExtension K n q f ∈ HorizontalAlternating.equivariant
      (complexCompactRepresentation K n) ρ q := by
  intro k X
  change f (fun i => reducedComplexProjection K n (complexLieConjugation K n k.val (X i))) =
    ρ k (f (fun i => reducedComplexProjection K n (X i)))
  simp only [reducedComplexProjection_conjugation]
  exact hf k (fun i => reducedComplexProjection K n (X i))

end Langlands.Global.ArchimedeanGL

namespace Langlands.Automorphic

open Langlands.Global
open ArchimedeanGL

variable {F : Type u} [Field F] [NumberField F] {n : ℕ} [NeZero n]

local instance : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

namespace OperatorRealization

variable (S : OperatorRealization F n)

local instance : AddCommGroup S.Space := Submodule.addCommGroup _

/-- Differentiate actual full compact equivariance on the reduced complex algebra. -/
theorem reducedCochain_compact_complex (q : ℕ)
    (f : (ReducedComplexLieAlgebra F n) [⋀^Fin q]→ₗ[ℂ] S.Space)
    (hf : f ∈ HorizontalAlternating.equivariant
      (reducedCompactRepresentation F n) S.compactRepresentation q)
    (Y : CompactComplexLieAlgebra F n) (X : Fin q → ReducedComplexLieAlgebra F n) :
    S.compactLieAction Y (f X) =
      ∑ i, f (Function.update X i ⁅compactToReducedComplex F n Y, X i⁆) := by
  have he := S.cochain_compact_complex q (reducedCochainExtension F n q f)
    (reducedCochainExtension_equivariant F n S.compactRepresentation q f hf)
    Y (fun i => reducedComplexInclusion F n (X i))
  have hvalue := congrArg (S.compactLieAction Y)
    (reducedCochainExtension_inclusion F n q f X).symm
  refine hvalue.trans (he.trans ?_)
  apply Finset.sum_congr rfl
  intro i _
  rw [reducedCochainExtension_apply]
  apply congrArg f
  funext j
  by_cases hj : j = i
  · subst j
    simp only [Function.update_self, (reducedComplexProjection F n).map_lie,
      reducedComplexProjection_compact, reducedComplexProjection_inclusion]
  · simp only [Function.update_of_ne hj, reducedComplexProjection_inclusion]

/-- Reduced cochains satisfying the actual complex compact insertion identity. -/
def reducedInfinitesimalCompactCochains (q : ℕ) :
    Submodule ℂ ((ReducedComplexLieAlgebra F n) [⋀^Fin q]→ₗ[ℂ] S.Space) where
  carrier := {f | ∀ (Y : CompactComplexLieAlgebra F n)
      (X : Fin q → ReducedComplexLieAlgebra F n),
    S.compactLieAction Y (f X) =
      ∑ i, f (Function.update X i ⁅compactToReducedComplex F n Y, X i⁆)}
  zero_mem' := by
    intro Y X
    simp
  add_mem' hf hg := by
    intro Y X
    simpa only [AlternatingMap.add_apply, map_add, Finset.sum_add_distrib] using
      congrArg₂ (· + ·) (hf Y X) (hg Y X)
  smul_mem' z f hf := by
    intro Y X
    simpa only [AlternatingMap.smul_apply, map_smul, Finset.smul_sum] using
      congrArg (fun v : S.Space => z • v) (hf Y X)

omit [NeZero n] in
@[simp]
theorem mem_reducedInfinitesimalCompactCochains (q : ℕ)
    (f : (ReducedComplexLieAlgebra F n) [⋀^Fin q]→ₗ[ℂ] S.Space) :
    f ∈ S.reducedInfinitesimalCompactCochains q ↔
      ∀ (Y : CompactComplexLieAlgebra F n) (X : Fin q → ReducedComplexLieAlgebra F n),
        S.compactLieAction Y (f X) =
          ∑ i, f (Function.update X i ⁅compactToReducedComplex F n Y, X i⁆) := Iff.rfl

/-- The identity inclusion whose infinitesimal membership is derived by differentiation. -/
def reducedCompactEquivariantLieInclusion (q : ℕ) :
    HorizontalAlternating.equivariant
      (reducedCompactRepresentation F n) S.compactRepresentation q →ₗ[ℂ]
        S.reducedInfinitesimalCompactCochains q where
  toFun f := ⟨f.val, S.reducedCochain_compact_complex q f.val f.property⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

@[simp]
theorem reducedCompactEquivariantLieInclusion_coe (q : ℕ)
    (f : HorizontalAlternating.equivariant
      (reducedCompactRepresentation F n) S.compactRepresentation q) :
    (S.reducedCompactEquivariantLieInclusion q f).val = f.val := rfl

theorem reducedCompactEquivariantLieInclusion_injective (q : ℕ) :
    Function.Injective (S.reducedCompactEquivariantLieInclusion q) := by
  intro f g h
  exact Subtype.ext (congrArg
    (fun v : S.reducedInfinitesimalCompactCochains q => v.val) h)

/-- Horizontal reduced cochains satisfying the infinitesimal compact identity. -/
def infinitesimalHorizontalCochains (q : ℕ) :
    Submodule ℂ ((ReducedComplexLieAlgebra F n) [⋀^Fin q]→ₗ[ℂ] S.Space) :=
  HorizontalAlternating.horizontal (compactInReducedSubmodule F n) q ⊓
    S.reducedInfinitesimalCompactCochains q

/-- Retain horizontality while deriving infinitesimal membership from the full compact group. -/
def horizontalCompactLieInclusion (q : ℕ) :
    horizontalEquivariantSubmodule F n S.compactRepresentation q →ₗ[ℂ]
      S.infinitesimalHorizontalCochains q where
  toFun f := ⟨f.val, f.property.1, S.reducedCochain_compact_complex q f.val f.property.2⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

@[simp]
theorem horizontalCompactLieInclusion_coe (q : ℕ)
    (f : horizontalEquivariantSubmodule F n S.compactRepresentation q) :
    (S.horizontalCompactLieInclusion q f).val = f.val := rfl

theorem horizontalCompactLieInclusion_injective (q : ℕ) :
    Function.Injective (S.horizontalCompactLieInclusion q) := by
  intro f g h
  exact Subtype.ext (congrArg
    (fun v : S.infinitesimalHorizontalCochains q => v.val) h)

end OperatorRealization
end Langlands.Automorphic
