import Langlands.GroupScheme.Reductive.RankOneRootReducednessStatement
import Langlands.GroupScheme.Reductive.RankOnePositiveRootStatement
import Langlands.GroupScheme.Rational.RelativeRootNegationStatement
import Langlands.GroupScheme.Torus.MaximalSplitComparison
import Langlands.GroupScheme.Absolute.RegularPerturbation

/-! # Reducedness in semisimple rank one from negation and positive-root uniqueness

A conditional assembly: `RankOneRootReducednessStatement` follows from
`RelativeRootNegationStatement` and `RankOnePositiveRootUniquenessStatement`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A nonzero character of a split torus is positive on some cocharacter. -/
theorem IsSplitTorus.exists_latticePairing_pos (hT : IsSplitTorus T.toGrp)
    {α : characterLattice T} (hα : α ≠ 0) :
    ∃ ν : cocharacterLattice T, 0 < latticePairing T α ν := by
  by_contra h
  simp only [not_exists, not_lt] at h
  apply hα
  apply hT.isPerfPair_latticePairing.separatingLeft α
  intro ν
  have h1 := h ν
  have h2 := h (-ν)
  rw [map_neg] at h2
  omega

/-- A cocharacter on which a given nonzero character of a split torus is positive, chosen
using `IsSplitTorus.exists_latticePairing_pos`. -/
def IsSplitTorus.positiveCocharacter (hT : IsSplitTorus T.toGrp) {α : characterLattice T}
    (hα : α ≠ 0) : cocharacterLattice T :=
  (hT.exists_latticePairing_pos hα).choose

/-- A nonzero character is positive on its chosen positive cocharacter. -/
theorem IsSplitTorus.latticePairing_positiveCocharacter_pos (hT : IsSplitTorus T.toGrp)
    {α : characterLattice T} (hα : α ≠ 0) :
    0 < latticePairing T α (hT.positiveCocharacter hα) :=
  (hT.exists_latticePairing_pos hα).choose_spec

/-- Let `α, β` be characters of a split torus that are linearly dependent over `ℤ`, with
`β ≠ 0`. Then `β` pairs nontrivially with every cocharacter that pairs nontrivially with `α`. -/
theorem IsSplitTorus.latticePairing_ne_zero_of_not_linearIndependent
    (hT : IsSplitTorus T.toGrp) {α β : characterLattice T} (hβ : β ≠ 0)
    (hdep : ¬ LinearIndependent ℤ ![α, β]) {ν : cocharacterLattice T}
    (hν : latticePairing T α ν ≠ 0) :
    latticePairing T β ν ≠ 0 := by
  intro hβν
  apply hdep
  rw [LinearIndependent.pair_iff]
  intro m n hmn
  have hpair : ∀ μ : cocharacterLattice T,
      m * latticePairing T α μ + n * latticePairing T β μ = 0 := by
    intro μ
    have := congrArg (fun χ => latticePairing T χ μ) hmn
    simpa using this
  have hm : m = 0 := by
    have h := hpair ν
    rw [hβν, mul_zero, add_zero] at h
    exact (mul_eq_zero.mp h).resolve_right hν
  refine ⟨hm, ?_⟩
  by_contra hn
  apply hβ
  apply hT.isPerfPair_latticePairing.separatingLeft β
  intro μ
  have h := hpair μ
  rw [hm, zero_mul, zero_add] at h
  exact (mul_eq_zero.mp h).resolve_left hn

/-- **Reducedness in semisimple rank one, conditionally.** Negation stability of the roots
(`RelativeRootNegationStatement`) and uniqueness of a root positive on a given cocharacter
(`RankOnePositiveRootUniquenessStatement`) imply `RankOneRootReducednessStatement`. -/
theorem rankOneRootReducedness_of_negation_of_positiveRootUniqueness
    (hneg : RelativeRootNegationStatement.{u})
    (hpos : RankOnePositiveRootUniquenessStatement.{u}) :
    RankOneRootReducednessStatement.{u} := by
  intro k _ G hG T hT i hi
  have := hG.isAffineHom
  intro hdep α hα β hβ
  set ν := hT.positiveCocharacter hα.1
  have hαν : 0 < latticePairing T α ν := hT.latticePairing_positiveCocharacter_pos hα.1
  have hβν : latticePairing T β ν ≠ 0 :=
    hT.latticePairing_ne_zero_of_not_linearIndependent hβ.1 (hdep α hα β hβ) hαν.ne'
  rcases lt_or_gt_of_ne hβν with hlt | hgt
  · right
    have hβ' : -β ∈ roots i := by
      rw [← relativeRoots_eq_roots]
      exact hneg k G hG T i (hi.isMaximalSplitTorus hT) β (by rwa [relativeRoots_eq_roots])
    refine hpos k G hG T hT i hi hdep ν α hα (-β) hβ' hαν ?_
    rw [map_neg, LinearMap.neg_apply]
    exact neg_pos.mpr hlt
  · left
    exact hpos k G hG T hT i hi hdep ν α hα β hβ hαν hgt

end Langlands.GroupScheme
