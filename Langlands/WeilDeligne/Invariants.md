# Invariant Weil–Deligne pairs

Worker 17 authored this construction. This module retains the actual
monodromy on a fixed subspace, supplementing the existing underlying invariant
representation and the monodromy-kernel representation.

For a subgroup `J` on which the supplied norm character is trivial,
`monodromy_mem_invariants` applies the pair covariance to a fixed vector,
using its invariance under the inverse element as well. The result is that
monodromy maps the fixed subspace into itself. This lemma needs no
normality. For normal `J`, `invariants` bundles the
restricted action and restricted monodromy, with nilpotence inherited by
restriction and covariance checked after the injective subspace inclusion.
No monodromy-stability certificate is requested from callers.

`invariantsInclusion`, `invariantsMap`, `invariantsFunctor`,
`invariantsEquiv`, and `invariantsClass` construct actual maps, prove their
intrinsic laws, and descend to genuine isomorphism classes.
`parameterInvariants` and `parameterInvariantsClass` retain the open kernel
on a separately specified inertia subgroup; their proof uses the injective
inclusion and the previously proved open-subgroup argument.

Source correspondence is a direct consequence of Tate's norm covariance,
*Number theoretic background*, Corvallis Part II, printed page 20,
§4.1.2(b), and his use of inertia invariants in §4.1.6. Source ID
`tate-1979-number-theoretic-background`, retained PDF SHA-256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
This generic invariant-pair functor is derived infrastructure, rather than
a claim that the original source states this Lean packaging.

Normality and norm triviality on `J` are explicit. No topology is needed for
the algebraic pair; the open-inertia wrapper assumes a topological group.
Usual-topology continuity and Frobenius semisimplicity are not silently
preserved by assumption. The restricted monodromy is not replaced by zero.

The module imports `Langlands.WeilDeligne.Parameters` and
`Langlands.Weil.Representation.InertiaOperations`, reusing the actual
fixed-subspace representation and injective-intertwiner certificate.

## Included restriction module

This contribution also includes `Langlands.WeilDeligne.ParameterRestriction`,
with paired Markdown. It restricts actual open-inertia representations and
parameters along a continuous group homomorphism `phi : H → G` that maps a
specified subgroup `J ≤ H` into the specified inertia subgroup `I ≤ G`. The
open-kernel certificate is proved by a continuous preimage argument; the pair
keeps its monodromy and uses the pulled-back norm `nu.comp phi`; both
restriction operations descend to genuine classes. Tate's §2.1, printed
pages 9–10, supplies the restriction maps. The two modules are mathematically
independent, and each imports only already published modules.
