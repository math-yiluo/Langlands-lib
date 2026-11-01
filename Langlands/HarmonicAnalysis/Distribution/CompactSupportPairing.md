# Compactly supported distributions paired with locally constant functions

Worker 6 authored the construction and initial explanation. Worker 451 checked
the original passage and public interfaces, verified the complete declaration
types, and prepared this pair for the focused construction task.
It constructs the algebraic pairing E′(X) × C∞(X) → ℂ from David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, II.1.2, printed p.31 / PDF p.37, the final paragraph. The
registered source is `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 6 read that entire original page and its preceding functional-space
conventions on printed p.30 / PDF p.36. Worker 451 independently read both
pages and visually checked the source formula on PDF page 37. The original is retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.

The declarations belong to
`Langlands.HarmonicAnalysis.Distribution`. This is a construction unit with
intrinsic evaluation and linearity laws. It makes no nondegeneracy,
full-dual-identification, continuous-duality or further tensor assertion.

## Actual objects and scope

The existing `SchwartzBruhat X` is the submodule of actual complex functions
that are locally constant and have compact topological support.
`Distribution X` is its full algebraic complex dual, with no continuity
condition. The published `Distribution.support` is the complement of the
union of opens where the actual open restriction is zero.
`compactlySupported` is the published complex submodule whose elements have
compact support in that precise sense. Its subtype is E′(X).

Mathlib `LocallyConstant X ℂ` is C∞(X). It has no compact-support constraint.
Its complex module operations are pointwise. The construction imports the
existing support, closed descent and closed restriction proof modules; it
does not copy their carriers or assume their results as new hypotheses.

The ambient `X : Type u` has its supplied topology, together with
Hausdorffness, local compactness and total disconnectedness. These three
classes express the source locally profinite condition by the published
`Langlands.Topology.isLocallyProfinite_iff_mathlib`. Subsets have their
actual induced topologies. There is no countability, group, nonemptiness or
ambient compactness restriction.

## Restriction to a compact set

`restrictLocallyConstantCompact hK` is a complex-linear map from
`LocallyConstant X ℂ` to `SchwartzBruhat K` for each compact subset K.
It sends f to the function x ↦ f(x) on the subtype K.
Local constancy follows by composition with the continuous subtype
inclusion. The compact subtype instance obtained from hK gives compact
support for every function on K. Addition and scalar multiplication are
pointwise, so both linear-map laws are definitional.
`restrictLocallyConstantCompact_apply` states the actual evaluation formula.
This restriction alone requires only the ambient topology and compactness
of K.

`exists_testFunction_agrees_on_compact` is a helper under the source
topological hypotheses. It applies the published
`SchwartzBruhat.closedRestrictionSurjective` to the compact K, which is
closed by Hausdorffness, and to the just-defined restriction of f.
Evaluating the resulting equality on every point of K gives an ambient
scalar test g equal to f on K. This is a derived construction helper; the
ambient representative is not used in the definition of the pairing.

## Descent formula and agreement law

For T in E′(X), let F be `support (T : Distribution X)`. This is compact by
T's subtype property and closed by `isClosed_support`. The published
`mem_supportedOn_support` places T in the existing pointwise-annihilator
submodule `supportedOn F`. Consequently the inverse of the actual
`closedPushforwardSupportedEquiv` supplies a distribution T₀ on F whose
closed pushforward is T. The existing inverse and uniqueness laws explain
why this is the unique distribution used in Renard's definition.

`compactSupportFunctional T` is the composition of T₀ with
`restrictLocallyConstantCompact T.property`. It is therefore complex-linear
in f by construction. `compactSupportFunctional_apply` states the defining
formula T₀(f restricted to F). It is exactly the formula in the original
final paragraph, with no cutoff or externally supplied descent.

`compactSupportFunctional_eq_of_agrees` says that if an ambient scalar
test g agrees with f at every point of F, then this formula equals T(g).
Indeed, the restriction of g to F equals the compact restriction of f by
extensionality. The published inverse-equiv evaluation law on restricted
test functions then gives T(g). This also proves that any two such ambient
representatives give the same value.

## Bilinear pairing

`compactSupportPairing` packages `compactSupportFunctional` into the actual
complex-linear map from E′(X) to the complex-linear maps C∞(X) → ℂ.
For addition in T, the helper extends f from the compact union of the two
supports to one ambient scalar test g. The support of their sum lies in
that union by the published `support_add_subset`. The agreement law
therefore expresses all three pairings using this same g. Pointwise
addition of ambient distributions proves the required additivity.

For scalar multiplication in T, take a representative on the original
compact support. The published `support_smul_subset` puts the support of
the scalar multiple inside that set. The same agreement law and the
pointwise scalar operation on the ambient algebraic dual prove the second
outer linear-map law, including scalar zero. The linearity in f is already
provided by the composition defining `compactSupportFunctional`.

`compactSupportPairing_apply` is the source formula for this bundled pairing,
and `compactSupportPairing_eq_of_agrees` is its representative agreement
law. `compactSupportPairing_testFunction` applies that law to an original
scalar test g, viewed as the same locally constant function, and gives
exactly the original evaluation T(g). The four explicit add/smul laws
expose both complex linearities without conjugating either argument.

All constructions and arguments include empty X, compact set K equal to
the empty set, and distributions with empty support. No representative
needs a nonempty support, and the compact-subtype and surjectivity results
retain those cases. This module defines the bilinear evaluation pairing;
additional assertions about that pairing require separate statement and
proof units.
