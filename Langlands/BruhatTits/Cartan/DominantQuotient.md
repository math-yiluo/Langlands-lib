# Restricted dominant centralizer quotients

This is an internal definition and intrinsic-law unit. It constructs the set
quotients and representative maps needed to express the later actual-group
Cartan statements. It proves only elementary consequences of explicitly supplied
algebraic hypotheses and of the existing normalized valuation. It supplies no
Cartan decomposition, geometric subgroup, or building-existence assertion.

## The restricted right-coset quotient

For any group `Z`, set `D ⊆ Z` and subgroup `N ≤ Z`,
`RestrictedRightQuotient.setoid D N` is Mathlib's right-coset relation restricted
to the subtype `D`. Its relation is exactly

`z ~ z' ↔ z' * z⁻¹ ∈ N`.

`RestrictedRightQuotient.Quotient D N` is the resulting set quotient, with class
map `mk` and exact equality law `mk_eq_mk`. It requires neither normality of `N`
nor stability of `D` under `N`. No group structure on the restricted quotient is
claimed. This direction of the coset relation matches the corrected KP
centralizer criterion; it is retained even when no normality argument is yet
available.

For a homomorphism `j : Z →* G` and subgroup `H ≤ G`, `Respects D N j H`
means that equivalent elements of `D` have equal `H` double cosets in `G`.
`doubleCosetMap` is the quotient lift under precisely this well-definedness
condition. Its representative law `doubleCosetMap_mk` sends the class of `z` to
`H j(z) H`.

`doubleCosetMap_bijective` requires two further inputs: every double coset has
an image representative from `D`, and equality of image double cosets implies
`z' * z⁻¹ ∈ N`. The proof descends to representatives for injectivity and chooses
an existing dominant representative for surjectivity.
`doubleCosetEquiv` packages the construction when coverage and the full
if-and-only-if criterion are supplied. Its representative law
`doubleCosetEquiv_mk` specifies the map of the equivalence. Coverage alone does
not establish injectivity or well-definedness.

These are generic algebraic helpers. The subgroup parameter `H` is not asserted
to be a parahoric or maximal compact subgroup, and `N` is not asserted to be a
particular geometric kernel. The hypotheses of the constructor are explicit
arguments, not a typeclass or existence certificate. Its intended later
specializations must separately state and prove their actual-group coverage and
equality criteria.

## The actual dominant norm quotient

Take a nonarchimedean local field `F`, actual group schemes `G` and `Z`, a
commutative group scheme `S`, maps `i : S → G` and `s : S → Z`, and the existing
explicit comparison `h : Bijective (restrictionEvaluation s)`. The definitions
have the same scope as `dominantCentralizer` and require affineness of `G` for
its relative roots. They do not assume maximality, reductivity, a centralizer
representation, or genericity; those geometric hypotheses belong to the
subsequent actual-centralizer statements. Both field characteristics remain
allowed.

The valuation is the existing positive character-normalized map:
evaluating a restricted rational character on `centralizerValuation s h z`
gives its positive integer field order. The set `D = dominantCentralizer i ν s h`
uses nonnegative evaluation on every actual positive relative root selected by
`ν`. Its image chamber is the existing `dominantValuationImage i ν s h`, a subset
of the actual range in `V(S)`, with no full cocharacter-lattice identification.

`centralizerValuation_eq_iff` proves equality of two valuation values exactly
when `z' * z⁻¹` belongs to `rationalCommonNormKernel Z`. It rewrites the previously
proved kernel equality and applies the homomorphism kernel criterion.
`DominantNormQuotient` restricts this actual common-norm-kernel relation to `D`.
`dominantNormValue` sends a class to its representative's actual valuation in
the chamber. Kernel equality proves well-definedness and injectivity. Every
actual image value already has an actual preimage, whose dominance follows
from that value, proving surjectivity. `dominantNormQuotientEquiv` is the resulting
bijection, with the displayed representative formula proved by
`dominantNormQuotientEquiv_mk`.

For an actual centralizer, this is the quotient by `Z(F)^1`. KP Theorem 5.2.1
uses `Z(F)^0` for the parahoric quotient. The present file does not identify these
two subgroups. It also does not identify either quotient with double cosets of
a geometric `P_x` or `K0`. The former requires the actual `Z(F)^0` and parahoric
objects and the KP equality criterion. The latter requires the separately
geometrically defined shared `K0` and its actual double-coset criterion. Only
after that comparison can this norm quotient be used as a maximal-compact
indexing set. No canonical topology, compactness or discreteness result is
proved here; these are set equivalences on the existing rational-point objects.

## Provenance and retained obligations

All new constructions are internal algebraic consequences, rather than a
transcription of a new literature theorem. They reuse Mathlib's
`QuotientGroup.rightRel`, `Setoid.comap`, quotient lift and double-coset quotient,
and the existing `CentralizerValuationConsequences` kernel equality. The proofs
are the quotient universal property, the equality-of-kernel criterion, and the
definition of an actual homomorphism range. The preceding paragraphs describe
the implemented proofs.

The source-facing motivation remains KP Theorem 5.2.1 and corrected equation
(5.2.2), book PDF217–219/printed186–188 with the 1 November 2024 corrections
PDF24–25 and30. Their corrected signs and their distinct `Z(F)^0` quotient are
preserved by the existing imported valuation definitions. Renard's maximal
compact interpretation and finite representative comparisons remain separate
statement obligations. No split, quasi-split, tame or residue-characteristic
specialization is used to discharge any of those obligations.
