import Langlands.Representation.Archimedean.RealStandardModuleGKModule

/-! # Uniqueness of the positive-weight real standard parameters

An isomorphism between irreducible real standard modules identifies the block lists up to
permutation when all induced weights are strictly positive. The modules and intertwiners
are the Library's actual `(𝔤𝔩_n(ℝ), O(n))` models. See the paired Markdown.
-/

noncomputable section
set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean

/-- An isomorphism of irreducible real standard modules with strictly positive induced
weights implies that the two lists of blocks are permutations. -/
def RealPositiveWeightStandardUniqueStatement : Prop :=
  ∀ (n : ℕ) (ds es : List RealBlock), realRank ds = n → realRank es = n →
    (∀ d : ComplexCharacterData, .induced d ∈ ds → 0 < d.weight) →
    (∀ d : ComplexCharacterData, .induced d ∈ es → 0 < d.weight) →
    IsIrreducibleGKModule (realStandardRep n ds) (realStandardLie n ds) →
    IsIrreducibleGKModule (realStandardRep n es) (realStandardLie n es) →
    ∀ T : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) →ₗ[ℂ]
        kFiniteFunctions (realStandardModule n es) (unitaryCompact ℝ n),
      IsRealStandardIntertwiner n (realStandardRep n es) (realStandardLie n es) ds T →
      Function.Bijective T → ds.Perm es

end Langlands.Archimedean
