import Langlands.Geometry.Building.IntegerValuation
import Langlands.GroupScheme.Rational.CharacterPolynomialGrowth
import Langlands.GroupScheme.Rational.CharacterLatticeProof
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.Data.Fintype.Pi

/-! # Finite character-valuation images of algebraically bounded sets -/

noncomputable section

universe u

open AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building.IntegerValuation

variable {k : Type u} [Field k] [ValuativeRel k]
    (v : Valuation k (WithZero (Multiplicative ℤ))) [v.Compatible]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]

/-- Every character coordinate of an algebraically bounded set lies in a finite
integer interval. No subgroup or compactness assumption is needed. -/
theorem exists_characterValuation_bounds_of_isAlgebraicallyBounded
    (X : Set (rationalPoints G)) (hX : IsAlgebraicallyBounded k G.X X)
    (χ : rationalCharacters G) :
    ∃ l r : ℤ, ∀ g ∈ X,
      l ≤ (rationalCharacterValuation v G g).toAdd χ ∧
      (rationalCharacterValuation v G g).toAdd χ ≤ r := by
  have lower (ψ : rationalCharacters G) :
      ∃ l : ℤ, ∀ g ∈ X, l ≤ (rationalCharacterValuation v G g).toAdd ψ := by
    obtain ⟨b, hb, hbound⟩ := hX (rationalCharacterSection ψ)
    refine ⟨-WithZero.log (v b), fun g hg => ?_⟩
    have hv := (v.vle_iff_le).1 (hbound g hg)
    rw [rationalPointAlgebraHom_rationalCharacterSection] at hv
    have hl := (WithZero.log_le_log
      (v.ne_zero_of_unit _) (v.ne_zero_iff.mpr hb)).2 hv
    rw [rationalCharacterValuation_eval]
    omega
  obtain ⟨l, hl⟩ := lower χ
  obtain ⟨r, hr⟩ := lower (-χ)
  refine ⟨l, -r, fun g hg => ⟨hl g hg, ?_⟩⟩
  have h := hr g hg
  rw [map_neg] at h
  omega

/-- Finite rank of the actual character lattice turns the separate coordinate
bounds into finiteness of the full integer character-valuation image. -/
theorem finite_characterValuation_image_of_isAlgebraicallyBounded
    (hG : IsConnectedReductive G)
    (X : Set (rationalPoints G)) (hX : IsAlgebraicallyBounded k G.X X) :
    (rationalCharacterValuation v G '' X).Finite := by
  classical
  obtain ⟨hfree, hfinite⟩ := rationalCharacterLattice k G hG
  let := hfree
  let := hfinite
  let b := Module.Free.chooseBasis ℤ (rationalCharacters G)
  let e : Multiplicative (rationalCharacters G →+ ℤ) →
      (Module.Free.ChooseBasisIndex ℤ (rationalCharacters G) → ℤ) :=
    fun f j => f.toAdd (b j)
  have he : Function.Injective e := by
    intro f g h
    change f.toAdd = g.toAdd
    apply AddMonoidHom.toIntLinearMap_injective
    apply b.ext
    exact fun j => congrFun h j
  have hcoord (j : Module.Free.ChooseBasisIndex ℤ (rationalCharacters G)) :
      ((fun g => e (rationalCharacterValuation v G g) j) '' X).Finite := by
    obtain ⟨l, r, h⟩ :=
      exists_characterValuation_bounds_of_isAlgebraicallyBounded v G X hX (b j)
    exact (Set.finite_Icc l r).subset (by
      rintro _ ⟨g, hg, rfl⟩
      exact h g hg)
  have hprod := Set.Finite.pi' hcoord
  have himage : (e '' (rationalCharacterValuation v G '' X)).Finite :=
    hprod.subset (by
      rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
      exact fun j => ⟨g, hg, rfl⟩)
  exact himage.of_finite_image he.injOn

/-- A bounded set meets only finitely many cosets of the actual character
kernel, with representatives chosen in that same bounded set. -/
theorem exists_finite_characterKernel_representatives_of_isAlgebraicallyBounded
    (hG : IsConnectedReductive G)
    (X : Set (rationalPoints G)) (hX : IsAlgebraicallyBounded k G.X X) :
    ∃ T : Set (rationalPoints G), T ⊆ X ∧ T.Finite ∧
      ∀ g ∈ X, ∃ t ∈ T, t⁻¹ * g ∈ characterValuationKernel v G := by
  have hf := finite_characterValuation_image_of_isAlgebraicallyBounded v G hG X hX
  obtain ⟨T, hTX, hT, heq⟩ := hf.exists_subset_finite_image_eq (Set.Subset.refl _)
  refine ⟨T, hTX, hT, fun g hg => ?_⟩
  obtain ⟨t, ht, htg⟩ := heq.symm ▸ Set.mem_image_of_mem (rationalCharacterValuation v G) hg
  refine ⟨t, ht, ?_⟩
  rw [← rationalCharacterValuation_ker]
  exact (MonoidHom.eq_iff _).1 htg.symm

/-- Algebraic boundedness over any compatible integer-valued field gives
finite image under the actual rational-character valuation. -/
def BoundedCharacterValuationImageStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k]
    (v : Valuation k (WithZero (Multiplicative ℤ))) [v.Compatible]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left],
    IsConnectedReductive G →
    ∀ X : Set (rationalPoints G), IsAlgebraicallyBounded k G.X X →
      (rationalCharacterValuation v G '' X).Finite

/-- The finite-basis argument proves the exact arbitrary-universe statement. -/
theorem boundedCharacterValuationImage : BoundedCharacterValuationImageStatement.{u} := by
  intro k _ _ v _ G _ hG X hX
  exact finite_characterValuation_image_of_isAlgebraicallyBounded v G hG X hX

end Langlands.Geometry.Building.IntegerValuation
