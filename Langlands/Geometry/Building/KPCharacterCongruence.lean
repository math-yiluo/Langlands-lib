import Langlands.LocalField.AddValuationUnitFiltration
import Langlands.GroupScheme.Rational.PointTopology
import Langlands.GroupScheme.Torus.KernelDiagonalizable
import Mathlib.Algebra.Module.ZMod

/-! # Congruence subgroups tested on actual rational characters -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.LocalField
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Geometry.Building

variable {k : Type u} [Field k] (ω : AddValuation k (WithTop ℝ))
  (G : GroupScheme (Spec (CommRingCat.of k)))

/-- The subgroup on which every actual rational character is congruent to one
to depth `r` and has valuation zero. -/
def characterCongruence (r : ℝ≥0) : Subgroup (rationalPoints G) :=
  ⨅ χ : rationalCharacters G,
    (addValuationUnitFiltration ω r).comap (rationalCharacterEval χ)

@[simp] theorem mem_characterCongruence (r : ℝ≥0) (g : rationalPoints G) :
    g ∈ characterCongruence ω G r ↔
      ∀ χ : rationalCharacters G, rationalCharacterEval χ g ∈
        addValuationUnitFiltration ω r := by
  simp only [characterCongruence, Subgroup.mem_iInf, Subgroup.mem_comap]

/-- Character congruence subgroups decrease with depth. -/
theorem characterCongruence_antitone : Antitone (characterCongruence ω G) := by
  intro r s hrs g hg
  rw [mem_characterCongruence] at hg ⊢
  exact fun χ => addValuationUnitFiltration_antitone ω hrs (hg χ)

/-- At zero only the character valuation-zero conditions remain. -/
theorem mem_characterCongruence_zero (g : rationalPoints G) :
    g ∈ characterCongruence ω G 0 ↔
      ∀ χ : rationalCharacters G, ω (rationalCharacterEval χ g : k) = 0 := by
  simp only [mem_characterCongruence, mem_addValuationUnitFiltration_zero]

/-- The intersection consists precisely of the points killed by every
actual rational character. -/
theorem mem_iInf_characterCongruence (g : rationalPoints G) :
    g ∈ ⨅ r : ℝ≥0, characterCongruence ω G r ↔
      ∀ χ : rationalCharacters G, rationalCharacterEval χ g = 1 := by
  simp only [Subgroup.mem_iInf, mem_characterCongruence]
  constructor
  · intro h χ
    exact eq_one_of_mem_addValuationUnitFiltration ω _ (fun r => h r χ)
  · intro h r χ
    rw [h χ]
    exact (addValuationUnitFiltration ω r).one_mem

private def congruenceEvaluationAt (g : rationalPoints G) :
    rationalCharacters G →+ Additive kˣ where
  toFun χ := Additive.ofMul (rationalCharacterEval χ g)
  map_zero' := congrArg Additive.ofMul (rationalCharacterEval_zero g)
  map_add' χ ψ := congrArg Additive.ofMul (rationalCharacterEval_add χ ψ g)

/-- A generating family of the character module tests the same congruence
subgroup as all characters. -/
theorem mem_characterCongruence_iff_generators
    {Index : Type*} (s : Index → rationalCharacters G)
    (hs : Submodule.span ℤ (Set.range s) = ⊤) (r : ℝ≥0) (g : rationalPoints G) :
    g ∈ characterCongruence ω G r ↔
      ∀ i, rationalCharacterEval (s i) g ∈ addValuationUnitFiltration ω r := by
  rw [mem_characterCongruence]
  refine ⟨fun h i => h (s i), fun h χ => ?_⟩
  let f := (congruenceEvaluationAt G g).toIntLinearMap
  let W := (addValuationUnitFiltration ω r).toAddSubgroup.toIntSubmodule
  have htop : (⊤ : Submodule ℤ (rationalCharacters G)) ≤ W.comap f := by
    rw [← hs]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact h i
  exact htop (Submodule.mem_top : χ ∈ (⊤ : Submodule ℤ (rationalCharacters G)))

variable {G} {H : GroupScheme (Spec (CommRingCat.of k))}

/-- Every actual group-scheme homomorphism preserves character congruence
at every depth. -/
theorem map_characterCongruence_le (f : H ⟶ G) (r : ℝ≥0) :
    (characterCongruence ω H r).map (rationalPoints.map f) ≤
      characterCongruence ω G r := by
  rintro _ ⟨g, hg, rfl⟩
  have hg' := (mem_characterCongruence ω H r g).mp hg
  rw [mem_characterCongruence]
  intro χ
  rw [← rationalCharacterEval_characterRestrict]
  exact hg' _

/-- Actual rational characters separate points of a split torus from one. -/
theorem eq_one_of_rationalCharacters_of_isSplitTorus
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsSplitTorus T.toGrp)
    (t : rationalPoints T.toGrp)
    (ht : ∀ χ : rationalCharacters T.toGrp, rationalCharacterEval χ t = 1) :
    t = 1 := by
  apply (characterLattice.pointCharacters_bijective T hT
    (Over.mk (𝟙 (Spec (CommRingCat.of k))))).1
  apply MonoidHom.ext
  intro χ
  apply Units.map_injective
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).hom).1
  change rationalCharacterEval χ.toAdd t = rationalCharacterEval χ.toAdd 1
  simpa only [map_one] using ht χ.toAdd

/-- On a split torus the character congruence subgroups are separated. -/
theorem iInf_characterCongruence_eq_bot_of_isSplitTorus
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsSplitTorus T.toGrp) :
    ⨅ r : ℝ≥0, characterCongruence ω T.toGrp r = ⊥ := by
  apply le_antisymm _ bot_le
  intro t ht
  exact Subgroup.mem_bot.mpr
    (eq_one_of_rationalCharacters_of_isSplitTorus T hT t
      ((mem_iInf_characterCongruence ω T.toGrp t).mp ht))

section Topology

variable [TopologicalSpace k] [IsAffine G.X.left]

local instance : TopologicalSpace (rationalPoints G) := rationalPointTopology k G.X

/-- For a finitely generated actual character module, scalar openness
implies openness of the common character congruence subgroup. -/
theorem isOpen_characterCongruence [Module.Finite ℤ (rationalCharacters G)]
    (r : ℝ≥0) (hopen : IsOpen (addValuationUnitFiltration ω r : Set kˣ)) :
    IsOpen (characterCongruence ω G r : Set (rationalPoints G)) := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := rationalCharacters G)
  have he : (characterCongruence ω G r : Set (rationalPoints G)) =
      ⋂ i, (rationalCharacterEval (s i)) ⁻¹'
        (addValuationUnitFiltration ω r : Set kˣ) := by
    ext g
    simp only [Set.mem_iInter, Set.mem_preimage]
    exact mem_characterCongruence_iff_generators ω G s hs r g
  rw [he]
  exact isOpen_iInter_of_finite (fun i =>
    hopen.preimage (continuous_rationalCharacterEval G (s i)))

end Topology

end Langlands.Geometry.Building
