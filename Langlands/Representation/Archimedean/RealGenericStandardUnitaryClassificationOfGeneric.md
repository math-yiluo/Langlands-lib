# The real generic unitary classification on irreducible generic standard modules

Module `Langlands.Representation.Archimedean.RealGenericStandardUnitaryClassificationOfGeneric`,
namespace `Langlands.Archimedean`.

## Statement

`RealGenericStandardUnitaryClassificationOfGenericStatement` is the Library proposition
`RealGenericStandardUnitaryClassificationStatement` with one more explicit binder: the
standard module is generic. For every `n : ℕ` and every `ds : List RealBlock` with
`realRank ds = n` it assumes that the `O(n)`-finite functions of `realStandardModule n ds`,
with right translation `realStandardRep n ds` and right derivatives `realStandardLie n ds`, form

- an irreducible `(𝔤, K)`-module (`IsIrreducibleGKModule`),
- a generic one (`IsRealGenericGKModule n (realStandardLie n ds)`: a nonzero linear functional
  transforms under the strictly upper triangular matrices by the differential of a
  nondegenerate unitary character of the upper unipotent group),
- an infinitesimally unitary one (`IsRealUnitarizableGKModule`).

It concludes that there is a list `es` with `IsRealGenericUnitaryInducingData es` and
`HasRealStandardParameter n (realStandardRep n ds) (realStandardLie n ds) es`. The first says
that `es` is a concatenation of factors, each either `[δ]` or
`[realBlockTwist α δ, realBlockTwist (-α) δ]` with `0 < α < 1/2`. Here `δ` is a unitary
square-integrable block (`IsRealUnitaryDiscreteBlock`: real exponent zero, positive weight if
induced). The second gives `realRank es = n` and an injective compact and Lie intertwiner from
the `O(n)`-finite standard module of `es` into that of `ds`.

The theorem `realGenericStandardUnitaryClassification_of_generic` proves the proposition.

## Provenance

With the genericity premise the proposition is the real case of Badulescu–Renard, *Unitary
dual of GL(n) at archimedean places and global Jacquet–Langlands correspondence* (2010),
Theorem 8.2, p. 1131 (PDF p. 18), stated for the Library's standard models. Their basis
`u(δ,1)` and `π(δ,1;α)`, `α ∈ ]0,1/2[`, corresponds to the two kinds of factors. The
complementary pair uses `ν_δ = ν = |det|` for `A = ℝ` (Definition 7.1, pp. 1129–1130,
PDF pp. 16–17, and Proposition 9.4, p. 1133, PDF p. 20), so it is the determinant twist
`realBlockTwist (±α)`. The source proves Theorem 8.2 from the Tadić–Vogan classification. The
Lean proof below does not follow that route; it uses only results already in the Library.

The published target `RealGenericStandardUnitaryClassificationStatement` has no genericity
premise. Its Markdown derives genericity from the irreducible standard presentation by the
remark after Badulescu–Renard Theorem 8.1. This module does not prove that step. With a proof
of genericity for irreducible real standard modules, this theorem gives the target
immediately.

## Proof

All cited declarations are in the Library.

1. **Uniqueness.** `realStandardEllipticCartanReduction` applied to
   `RealStandardEllipticCartan.realStandardEllipticCartanComparison` gives
   `RealPositiveWeightStandardUniqueStatement`.
2. **Normalization.** Put `fs = ds.flatMap realBlockNormalize`: every induced block of weight
   zero splits into two characters and every negative weight becomes positive.
   `realRank_flatMap_normalize` and `realStandardModule_flatMap_normalize` show that `fs` has rank
   `n` and the same standard function space. So the identity is an injective intertwiner, and
   `fs` is a standard parameter of the given module. `realStandardParameter_model` then transfers
   irreducibility, genericity and infinitesimal unitarity to the standard module of `fs`. All
   induced weights of `fs` are positive (`weight_pos_of_mem_flatMap_normalize`).
3. **Hermitian grouping.** `realStandardHermitianPairDecomposition` uses the uniqueness of
   step 1. It returns a list `factors` with `factors.flatten` a permutation of `fs`, and each
   factor is `IsRealHermitianInducingFactor`: `[δ]` or `[realBlockTwist α δ, realBlockTwist (-α) δ]`
   with `0 < α` and `δ` unitary square-integrable.
4. **Unlinkage and reordering.** `realStandard_moeglinUnlinked_of_unitaryGeneric` says that the
   blocks of `fs` are pairwise Mœglin-unlinked. With `List.pairwise_flatMap` this gives pairwise
   unlinkage of the blocks (`AreRealBlocksUnlinked`). The private lemma `linked_symm` shows that
   linkage of Mœglin data is symmetric, so unlinkage passes along the permutation to
   `es = factors.flatten`. `realUnlinkedStandardPermutation` gives an injective intertwiner from
   the standard module of `es` into that of `fs`. Composing with step 2 gives
   `HasRealStandardParameter … es`, and `realStandardParameter_model` transfers irreducibility
   and infinitesimal unitarity to the standard module of `es`.
5. **Factors.** Every factor `A` is pairwise unlinked, as a sublist of `es`. Writing `es` as
   `s.flatten ++ A ++ t.flatten`, `realStandardIrreducibilityInStages` shows that the standard
   module of `A` is irreducible. `realHermitianInducingFactor_dualEquiv` then gives its
   Hermitian-dual equivalence. `realStandardFactorUnitarity` makes the standard module of each
   factor infinitesimally unitary.
6. **Bounds.** A singleton factor is a generic unitary factor. For a pair with twist `α > 0`:
   - If `δ` is a character, the pair is a principal series of `GL₂(ℝ)`.
     `RealGLTwoPrincipalSeriesUnitaryBound.exponent_difference` bounds the real part of the
     exponent difference `2α` by `|2α| < 1` (private `character_pair_bound`).
   - If `δ` is induced with positive weight, `realRankFourUnitaryBound` gives `|α| < 1/2`
     from the unlinkage of the two twists (private `induced_pair_bound`).

   So `α < 1/2`, and the private `genericFactor_of_hermitian` shows that every factor satisfies
   `IsRealGenericUnitaryInducingFactor`. Then `es` satisfies `IsRealGenericUnitaryInducingData`
   with the witness `factors`, and step 4 supplies the standard parameter.

The genericity premise is used as a hypothesis of the Library theorems in steps 3 and 4: the
Hermitian decomposition and Mœglin unlinkage. `realStandardParameter_model` transports it from
`ds` to `fs`, where those theorems apply.
