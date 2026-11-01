import Langlands.Representation.Aubert.SignedCutComplex
import Mathlib.Algebra.Exact.Basic

/-! Natural equivalences of actual signed cut diagrams. -/

noncomputable section

namespace Langlands.Aubert.CutComplex.Diagram

open scoped BigOperators

universe uI uM uN

variable {ι : Type uI} [LinearOrder ι]

/-- Coordinate linear equivalences commuting with every inclusion map. -/
structure Equivalence (D : Diagram.{uI,uM} ι) (E : Diagram.{uI,uN} ι) where
  obj : ∀ s, D.Obj s ≃ₗ[ℂ] E.Obj s
  natural : ∀ {s t : Finset ι} (h : s ⊆ t) (x : D.Obj s),
    obj t (D.map h x) = E.map h (obj s x)

namespace Equivalence

variable {D : Diagram.{uI,uM} ι} {E : Diagram.{uI,uN} ι}
  (e : Equivalence D E)

/-- Product of the coordinate equivalences. -/
def totalEquiv : D.Total ≃ₗ[ℂ] E.Total := LinearEquiv.piCongrRight e.obj

@[simp] theorem totalEquiv_apply (x : D.Total) (s : Finset ι) :
    e.totalEquiv x s = e.obj s (x s) := rfl

/-- Product of the coordinate equivalences in a fixed cut degree. -/
def degreeEquiv (k : ℕ) : D.Degree k ≃ₗ[ℂ] E.Degree k :=
  LinearEquiv.piCongrRight (fun s => e.obj s.1)

@[simp] theorem degreeEquiv_apply (k : ℕ) (x : D.Degree k)
    (s : {s : Finset ι // s.card = k}) :
    e.degreeEquiv k x s = e.obj s.1 (x s) := rfl

theorem totalEquiv_extend (k : ℕ) (x : D.Degree k) :
    e.totalEquiv (D.extend k x) = E.extend k (e.degreeEquiv k x) := by
  funext s
  by_cases hs : s.card = k <;> simp [hs]

theorem degreeEquiv_restrict (k : ℕ) (x : D.Total) :
    e.degreeEquiv k (D.restrict k x) = E.restrict k (e.totalEquiv x) := rfl

/-- Naturality preserves each exterior insertion with its original sign. -/
theorem totalEquiv_step (i : ι) (x : D.Total) :
    e.totalEquiv (D.step i x) = E.step i (e.totalEquiv x) := by
  funext s
  by_cases hi : i ∈ s
  · simp only [totalEquiv_apply, step_apply, hi, ↓reduceIte, map_smul, e.natural]
  · simp [hi]

variable [Fintype ι]

/-- Naturality preserves the sum of signed insertions. -/
theorem totalEquiv_differential (x : D.Total) :
    e.totalEquiv (D.differential x) = E.differential (e.totalEquiv x) := by
  simp only [differential_apply, map_sum, e.totalEquiv_step]

/-- The actual homogeneous signed differentials are intertwined. -/
theorem degreeEquiv_differential (k : ℕ) (x : D.Degree k) :
    e.degreeEquiv (k + 1) (D.degreeDifferential k x) =
      E.degreeDifferential k (e.degreeEquiv k x) := by
  change e.degreeEquiv (k + 1) (D.restrict (k + 1)
    (D.differential (D.extend k x))) = _
  rw [e.degreeEquiv_restrict, e.totalEquiv_differential, e.totalEquiv_extend]
  rfl

include e

/-- Injectivity is invariant under a natural coordinate equivalence. -/
theorem degreeDifferential_injective_iff (k : ℕ) :
    Function.Injective (D.degreeDifferential k) ↔
      Function.Injective (E.degreeDifferential k) := by
  constructor
  · intro hf x y hxy
    apply (e.degreeEquiv k).symm.injective
    apply hf
    apply (e.degreeEquiv (k + 1)).injective
    simpa only [e.degreeEquiv_differential, LinearEquiv.apply_symm_apply] using hxy
  · intro hg x y hxy
    apply (e.degreeEquiv k).injective
    apply hg
    rw [← e.degreeEquiv_differential, ← e.degreeEquiv_differential, hxy]

/-- Middle exactness is invariant under a natural coordinate equivalence. -/
theorem degreeDifferential_exact_iff (k : ℕ) :
    LinearMap.range (D.degreeDifferential k) =
        LinearMap.ker (D.degreeDifferential (k + 1)) ↔
      LinearMap.range (E.degreeDifferential k) =
        LinearMap.ker (E.degreeDifferential (k + 1)) := by
  have h := LinearMap.exact_iff_of_surjective_of_bijective_of_injective
    (D.degreeDifferential k) (D.degreeDifferential (k + 1))
    (E.degreeDifferential k) (E.degreeDifferential (k + 1))
    (e.degreeEquiv k).toLinearMap (e.degreeEquiv (k + 1)).toLinearMap
    (e.degreeEquiv (k + 1 + 1)).toLinearMap
    (LinearMap.ext (fun x => (e.degreeEquiv_differential k x).symm))
    (LinearMap.ext (fun x => (e.degreeEquiv_differential (k + 1) x).symm))
    (e.degreeEquiv k).surjective (e.degreeEquiv (k + 1)).bijective
    (e.degreeEquiv (k + 1 + 1)).injective
  constructor
  · intro hex
    exact (LinearMap.exact_iff.mp (h.mp (LinearMap.exact_iff.mpr hex.symm))).symm
  · intro hex
    exact (LinearMap.exact_iff.mp (h.mpr (LinearMap.exact_iff.mpr hex.symm))).symm

omit [Fintype ι] in
/-- Vanishing of a homogeneous carrier is preserved by the equivalence. -/
theorem degree_subsingleton_iff (k : ℕ) :
    Subsingleton (D.Degree k) ↔ Subsingleton (E.Degree k) :=
  (e.degreeEquiv k).toEquiv.subsingleton_congr

end Equivalence
end Langlands.Aubert.CutComplex.Diagram
