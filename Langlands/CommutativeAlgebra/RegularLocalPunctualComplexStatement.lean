import Langlands.Cohomology.PerfectModuleComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.RegularLocalRing.Defs

/-! # Punctual perfect complexes over a regular local ring -/

universe u

open CategoryTheory CategoryTheory.Limits IsLocalRing
open Langlands.Cohomology.ModuleComplex

namespace Langlands.CommutativeAlgebra

/-- Let `R` be a regular local ring of Krull dimension `g` with residue field
`k`, and let `K` be a bounded complex of finite projective `R`-modules. Assume
that `K ⊗ k` has homology only in degrees `0, …, g`, that its degree-zero
homology is one-dimensional, that every homology module of `K` is killed by a
power of the maximal ideal `m`, and that for every ideal `J` with
`m² ≤ J ⋖ m` the degree-zero homology of `K ⊗ R/J` is not isomorphic to
`R/J`. Then `K` has homology only in degree `g`, where it is `k`.
This is the algebra of Edixhoven, van der Geer and Moonen, *Abelian
Varieties*, (9.6)–(9.9). -/
def RegularLocalPunctualComplexStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R] (g : ℕ),
    ringKrullDim R = g →
    ∀ (K : CochainComplex (ModuleCat.{u} R) ℤ),
      IsStrictlyPerfect K →
      (∀ i : ℤ, (i < 0 ∨ (g : ℤ) < i) →
        IsZero (((baseChange (algebraMap R (ResidueField R))).obj K).homology i)) →
      Module.finrank (ResidueField R)
        (((baseChange (algebraMap R (ResidueField R))).obj K).homology 0) = 1 →
      (∀ i : ℤ, ∃ N : ℕ, maximalIdeal R ^ N ≤ Module.annihilator R (K.homology i)) →
      (∀ J : Ideal R, maximalIdeal R ^ 2 ≤ J → J ⋖ maximalIdeal R →
        IsEmpty (((baseChange (Ideal.Quotient.mk J)).obj K).homology 0 ≅
          ModuleCat.of (R ⧸ J) (R ⧸ J))) →
      (∀ i : ℤ, i ≠ g → IsZero (K.homology i)) ∧
        Nonempty (K.homology (g : ℤ) ≅ ModuleCat.of R (ResidueField R))

end Langlands.CommutativeAlgebra
