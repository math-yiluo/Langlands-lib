# Actual free quotients and projective summands

Authors: Worker 6 (shared proof draft revision 1: Lean and proof
explanation), Worker 1210 (source and dependency checks, documentation
revision, fresh compilation and submission).

This proof establishes
`Langlands.Algebra.NonUnitalModuleFreeStatements.FreeModuleAssertions.{uA,uM}`,
the two positive
assertions in Renard I.5.3, printed p.27 / PDF p.33 of the French edition dated
9 July 2026. The proof imports the unchanged public statement pair and its actual
regular-sum construction by Lean name. The entry module is
`Langlands.Algebra.NonUnitalModuleFreeProof`; its closed theorem is
`Langlands.Algebra.NonUnitalModuleFreeProof.freeModuleAssertions`.

The registered original is David Renard, *Représentations des groupes
réductifs p-adiques*, `renard-2026-representations-groupes-reductifs-padiques`,
SHA-256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The exact-Hom convention is A.VIII.1–2, printed pp.266–267 / PDF pp.272–273:
projectivity means exactness of the covariant Hom functor to integer modules.
The supplementary 2010-edition errata
`renard-2010-corrections-complements`, SHA-256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
were consulted at PDF pp.1–3 for the Chapter I corrections. The governing
I.5.3 passage was read directly in the 2026 edition.

## Scope and source correspondence

Renard works with a complex algebra with idempotents and defines free modules
as objects isomorphic to sums of copies of the regular module. The public
statement extends the two positive assertions to every arbitrary idempotented
nonunital ring `A`. This proof establishes that generalization: the quotient
uses only the additive action laws and a fixing idempotent, while the
summand conclusion uses the published abelian structure and projective
splitting. Neither step uses a complex scalar structure.

The free source is exactly `NonUnitalModuleFree.object hA I`, whose carrier
is the actual finite-support sum of `ULift.{uM} A` with original left
multiplication in each coordinate. The lift only places the original regular
carrier in the common universe. Both target carriers and indices lie in
`Type (max uA uM)`, while `uA` and `uM` remain independent.

## The original quotient map

For an actual nondegenerate module `M`, `quotientMap` uses `M.obj` itself as
the index type of the regular sum. It assembles the original orbit maps
`a ↦ a • m` using `NonUnitalModuleFree.fromFamily`, then bundles the resulting
original intertwiner as a morphism of the full nondegenerate subcategory.

Given `m`, nondegeneracy supplies an idempotent `e` with `e • m = m`. The
singleton with value `ULift.up e` in the summand indexed by `m` is an actual
preimage. The equation is exactly `fromFamily_single` followed by the fixing
equation. This proves surjectivity on the original additive carrier.
The published `NondegenerateModuleExactnessConcrete.epi_iff` converts that
surjectivity to a categorical epimorphism, giving `freeQuotient`.

## Splitting for a projective target

The proof installs the named abelian data on the original full subcategory.
The published `Langlands.Renard.homProjectiveComparison` converts the sole
source exact-Hom projectivity premise into categorical projectivity of `P`.
Apply the just-proved free quotient assertion to obtain `q : F ⟶ P`.

The actual kernel sequence `kernel q ⟶ F ⟶ P` is exact by
`ShortComplex.kernelSequence_exact`, its first map is monic, and its last map
is the given epimorphism. Thus it is short exact.
`ShortExact.splittingOfProjective` splits it. The implemented biproduct
isomorphism gives `F ≅ kernel q ⊞ P`; composing with the biproduct braiding
gives the required `F ≅ P ⊞ kernel q`. This is an actual isomorphism of
original nondegenerate modules.

The aggregate `freeModuleAssertions` pairs these proofs. The construction
and splitting retain independent coefficient and module universes; the file
also specializes the complete theorem at both unequal universe pairs `(0, 1)`
and `(1, 0)`.

The first proof implements the explicit orbit-map construction in I.5.3.
For the second assertion the source refers to the unital proof in Lang's
*Algebra*. The implemented route uses the published exact-Hom comparison and
Mathlib's short-exact-sequence splitting, with no appeal to that external
reference. Projectivity is assumed only for `P`; it is not assumed for the
regular summands. No enough-projectives or finite-dimensional hypothesis is
used.

The separate negative assertion in I.5.3, that regular or free objects and
their direct summands need not be projective, remains outside this proof.
In particular, this file proves no converse from being a summand of a free
object to projectivity.
