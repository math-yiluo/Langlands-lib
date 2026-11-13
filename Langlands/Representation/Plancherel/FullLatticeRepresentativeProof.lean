import Langlands.Representation.Plancherel.RenardLatticeComparisonStatement
import Langlands.Representation.Plancherel.SplitComponentLatticeProof
import Langlands.Representation.Plancherel.RenardDominantSections

/-! # Finite representatives of the full character-valuation lattice (Renard V.3.23)

From the finite index of the split-component valuation image and the bijection from `C0`
onto it, a finite transversal of `Λ(Z)/splitValuationImage s` exists, and every such
transversal `F0` makes `C0 · F0` a valuation section with injective valuation on pairs.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.Plancherel.RenardCartan

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {Z : GroupScheme (Spec (CommRingCat.of F))}

/-- Every residue class of `Λ(Z)/splitValuationImage s` is the residue of an actual point. -/
theorem latticeResidue_surjective (s : T.toGrp ⟶ Z) :
    Function.Surjective (latticeResidue s) := by
  intro q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (splitValuationImage s) q
  obtain ⟨z, rfl⟩ := (rationalCharacterValuation Z).rangeRestrict_surjective y
  exact ⟨z, rfl⟩

/-- If the split-component valuation image has finite index, a finite lattice transversal
exists: the image of a section of the surjective residue map. -/
theorem exists_isFiniteLatticeTransversal_of_finiteIndex (s : T.toGrp ⟶ Z)
    (hfin : (splitValuationImage s).FiniteIndex) :
    ∃ F0 : Set (rationalPoints Z), IsFiniteLatticeTransversal s F0 := by
  have hsurj := latticeResidue_surjective s
  let σ := Function.surjInv hsurj
  refine ⟨Set.range σ, Set.finite_range σ, ?_, ?_⟩
  · rintro ⟨_, q, rfl⟩ ⟨_, q', rfl⟩ h
    have hq : q = q' := by
      have h' : latticeResidue s (σ q) = latticeResidue s (σ q') := h
      rwa [Function.surjInv_eq hsurj, Function.surjInv_eq hsurj] at h'
    subst hq
    rfl
  · intro q
    exact ⟨⟨σ q, q, rfl⟩, Function.surjInv_eq hsurj q⟩

/-- Renard V.3.23: finite actual-point representatives of the full lattice cosets exist, and
for every such transversal `F0` the set `C0 · F0` is a valuation section of the full actual
valuation image, with injective valuation on the pairs of `C0 × F0`. -/
theorem fullLatticeRepresentative : FullLatticeRepresentativeStatement.{u} := by
  intro F _ _ _ _ Z hZ T s hs
  obtain ⟨hfin, hbij⟩ := splitComponentLattice F Z hZ T s hs
  exact ⟨exists_isFiniteLatticeTransversal_of_finiteIndex s hfin,
    fun F0 hF0 => isValuationSection_tildeC0_of_bijOn s hbij hF0⟩

end Langlands.Plancherel.RenardCartan
