import Langlands.GroupScheme.Reductive.RankOneRingSquareRoots
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # An fppf cover with a unit whose square minus one is a unit -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.QuadraticUnitExtension

variable (R : Type u) [CommRing R]

/-- The monic quadratic equation `X² = X + 1`. -/
def polynomial : Polynomial R := Polynomial.X ^ 2 - (Polynomial.X + 1)

/-- The quadratic extension used to make a root commutator invertible. -/
abbrev Ring := AdjoinRoot (polynomial R)

/-- The coefficient map into the quadratic extension. -/
def inclusion : R →+* Ring R := AdjoinRoot.of (polynomial R)

theorem polynomial_monic : (polynomial R).Monic := by
  apply Polynomial.monic_X_pow_sub
  compute_degree!

theorem inclusion_injective : Function.Injective (inclusion R) := by
  cases subsingleton_or_nontrivial R with
  | inl h => exact Function.injective_of_subsingleton _
  | inr h =>
    apply AdjoinRoot.of.injective_of_monic_of_degree_pos (polynomial_monic R)
    have hdegree : (polynomial R).degree = 2 := by
      unfold polynomial
      compute_degree!
    rw [hdegree]
    decide

/-- This extension is faithfully flat, including over the zero ring. -/
theorem inclusion_faithfullyFlat : (inclusion R).FaithfullyFlat := by
  cases subsingleton_or_nontrivial R with
  | inl h =>
    have : Subsingleton (Ring R) := subsingleton_of_zero_eq_one (by
      rw [← (inclusion R).map_zero, ← (inclusion R).map_one,
        Subsingleton.elim (0 : R) 1])
    exact RingHom.FaithfullyFlat.of_bijective
      ⟨Function.injective_of_subsingleton _, fun x => ⟨0, Subsingleton.elim _ _⟩⟩
  | inr h =>
    have : Module.Free R (Ring R) := (polynomial_monic R).free_adjoinRoot
    have : Nontrivial (Ring R) := Function.Injective.nontrivial (inclusion_injective R)
    exact RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance

/-- A quotient by this single equation is finitely presented. -/
theorem inclusion_finitePresentation : (inclusion R).FinitePresentation :=
  RingHom.finitePresentation_algebraMap.mpr inferInstance

theorem root_sq : AdjoinRoot.root (polynomial R) ^ 2 =
    AdjoinRoot.root (polynomial R) + 1 := by
  have h := AdjoinRoot.eval₂_root (polynomial R)
  change (Polynomial.X ^ 2 - (Polynomial.X + 1) : Polynomial R).eval₂ (inclusion R)
    (AdjoinRoot.root (polynomial R)) = 0 at h
  simpa only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_add, Polynomial.eval₂_one, sub_eq_zero] using h

/-- The root is a unit with inverse `X - 1`. -/
def rootUnit : (Ring R)ˣ where
  val := AdjoinRoot.root (polynomial R)
  inv := AdjoinRoot.root (polynomial R) - 1
  val_inv := by
    calc
      _ = AdjoinRoot.root (polynomial R) ^ 2 - AdjoinRoot.root (polynomial R) := by ring
      _ = 1 := by rw [root_sq]; ring
  inv_val := by
    calc
      _ = AdjoinRoot.root (polynomial R) ^ 2 - AdjoinRoot.root (polynomial R) := by ring
      _ = 1 := by rw [root_sq]; ring

theorem rootUnit_sq_sub_one : (rootUnit R : Ring R) ^ 2 - 1 = (rootUnit R : Ring R) := by
  change AdjoinRoot.root (polynomial R) ^ 2 - 1 = AdjoinRoot.root (polynomial R)
  rw [root_sq]
  ring

theorem isUnit_rootUnit_sq_sub_one : IsUnit ((rootUnit R : Ring R) ^ 2 - 1) := by
  rw [rootUnit_sq_sub_one]
  exact (rootUnit R).isUnit

/-- Every affine test has a surjective fppf refinement with such a unit. -/
theorem exists_unit_test {S : Scheme.{u}} (Z : Over S) [IsAffine Z.left] :
    ∃ (W : Over S) (j : W ⟶ Z), IsAffine W.left ∧
      Flat j.left ∧ Surjective j.left ∧ LocallyOfFinitePresentation j.left ∧
      ∃ t : Γ(W.left, ⊤)ˣ, (t : Γ(W.left, ⊤)) ^ 2 - 1 = t := by
  let A := Γ(Z.left, ⊤)
  let φ : A ⟶ CommRingCat.of (Ring A) := CommRingCat.ofHom (inclusion A)
  let j₀ : Spec (CommRingCat.of (Ring A)) ⟶ Z.left := Spec.map φ ≫ Z.left.isoSpec.inv
  let W : Over S := Over.mk (j₀ ≫ Z.hom)
  let j : W ⟶ Z := Over.homMk j₀
  have hflat := (flat_and_surjective_SpecMap_iff φ).mpr (inclusion_faithfullyFlat A)
  have : Flat (Spec.map φ) := hflat.1
  have : Surjective (Spec.map φ) := hflat.2
  have : LocallyOfFinitePresentation (Spec.map φ) :=
    (LocallyOfFinitePresentation.SpecMap_iff φ).mpr (inclusion_finitePresentation A)
  let ψ := (Scheme.ΓSpecIso (CommRingCat.of (Ring A))).inv.hom
  refine ⟨W, j, inferInstanceAs (IsAffine (Spec (CommRingCat.of (Ring A)))),
    inferInstanceAs (Flat j₀), inferInstanceAs (Surjective j₀),
    inferInstanceAs (LocallyOfFinitePresentation j₀),
    Units.map ψ.toMonoidHom (rootUnit A), ?_⟩
  simp only [W, Over.mk_left]
  convert congrArg ψ (rootUnit_sq_sub_one A) using 1 <;>
    simp only [map_sub, map_pow, map_one, Units.coe_map] <;> rfl

end Langlands.GroupScheme.QuadraticUnitExtension
