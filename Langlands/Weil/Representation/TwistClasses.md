# Character twists on genuine representation classes

Workers 4 and 62 authored this internal construction from published scalar-twist
operations, quotient definitions and operation-closure proofs. Worker 4 supplied
the shared construction draft; Worker 62 reconciled it with an independently
developed draft, added explicit object-rank and representative formulas,
two-sided inverse application lemmas, and the specialized unramified forgetful
formula, and checked the final combined interface. It introduces
no new model of representation classes and uses no literature theorem beyond
those already represented by its published imports.

The algebraic part works over an arbitrary field, with independent coefficient,
group and carrier universes. `twistOneEquiv` and `twistMulEquiv` use the identity
linear equivalence after rewriting the actual representation by the published
scalar-twist algebra laws. The existing `twistClass` therefore preserves rank,
acts identically for the trivial character, and composes by multiplication of
characters. Twisting successively by a character and its inverse is the identity
in both orders. `twistClassEquiv` packages these maps as an equivalence of the
existing isomorphism-class quotient. Its formula on representatives is the class
of the actual twisted representation. `rank_twist` and
`twistClassEquiv_classOf` expose these formulas directly. In the `_mul` laws,
`(twistClassEquiv eta).trans (twistClassEquiv chi)` means first twist by `eta`,
then by `chi`, and equals the equivalence for `chi * eta`.

The generic helper `forgetPropertyClass_injective` proves that forgetting a
property of representatives is injective on the existing property quotient.
Both quotients use exactly the same linear-intertwining equivalence relation;
quotient induction, `Quotient.exact` and `Quotient.sound` give this fact without
assuming invariance of the predicate.

For complex representations, `isContinuous_twist` applies the published
`Weil.OperationClosure.continuous_twist` in the usual complex module topology.
`continuousIrreducibleTwist` pairs this with the published
`irreducible_twist_iff` to twist objects carrying genuine continuity and
irreducibility proofs. Descent uses the existing `twistEquiv` on genuine
intertwiners. The resulting `continuousIrreducibleTwistClass` commutes with
`forgetPropertyClass`; injectivity of that forgetful map transfers identity,
composition and inverse laws from the unconditioned quotient.

`continuousIrreducibleTwistEquiv chi n` restricts this operation to the existing
`ContinuousIrreducibleClasses G n`. The rank certificate follows from the
forgetful formula and the unchanged carrier of the scalar twist. Its inverse
is the action of `chi` inverse, with both inverse laws proved. The representative
formula, forgetful square, identity, composition and inverse-equivalence laws
are provided. This construction requires only a group with a topology and a
continuous complex character; continuity of the group operations is unnecessary.
The group and carrier universes are independent, and every natural rank is
allowed, including zero as in the existing class definition.
The lemmas `continuousIrreducibleTwistEquiv_inv_apply` and
`continuousIrreducibleTwistEquiv_apply_inv` expose the two cancellation orders
directly for rewriting.

`continuousIrreducibleUnramifiedTwistEquiv d z n` specializes to the published
`Weil.Local.unramifiedCharacter d z` for an arbitrary unit `z` of the complex
numbers. Identity, product and inverse laws follow from
`unramifiedCharacterHom` and the general class equivalences. Thus both phase
and magnitude of the value at degree one are retained. The degree map remains
an explicit continuous input; no actual local Weil assembly, reciprocity map,
or finite-image reduction theorem is selected here. Arbitrary unramified
twists are not claimed to preserve finite image.
The specialized forgetful formula identifies this with the existing algebraic
`twistClass`, and the specialized `_inv_apply` and `_apply_inv` lemmas cancel
the parameter `z` with `z⁻¹` in both orders.

All project imports are published Library modules, checked against Library
`f56650f18ac0d69910527cecd1e4749a1cbba717`:
`Langlands.Weil.Representation.Basic` (through `Twist`),
`Langlands.Weil.Representation.Twist`,
`Langlands.Weil.Representation.Predicates`,
`Langlands.Weil.Representation.OperationClosureProof`,
`Langlands.Representation.Twist.AlgebraProof`, and
`Langlands.Weil.Local.DegreeCharacters`.
The constructions and their intrinsic laws are derived from these existing
objects and proofs; no new translation of an original literature claim is
asserted. In particular, this module does not prove intrinsic Weil unramified
reduction or local field/Frobenius assembly.

The two additional Mathlib
imports provide the group structure on algebraic character homomorphisms and
the topological group structure on units with their usual induced topology.
The environment is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.

Development compilation and direct assignments of the unapplied constructors
to the full intended types succeeded with independent universes. Consumer
checks also verified inverse-character rewriting for the continuous action
and its unramified specialization at rank zero. Only the standard axioms
`propext`, `Classical.choice` and `Quot.sound` occur in the main constructor.
These checks do not replace independent review and publication.

## Shared twist interface correction

Worker 111 extracted the four common helpers into
`Langlands.Weil.Representation.TwistProperties`, with Worker 21 supplying the
original declaration comparison and consumer validation. The original authorship
and mathematical provenance above remain unchanged. This module imports the
shared interface and retains its original import path. All four fully qualified
names in `Langlands.FiniteRepresentation` remain available: `rank_twist`,
`twistOneEquiv`, `twistMulEquiv`, and `isContinuous_twist`.

The canonical continuity call is `isContinuous_twist chi hA`, or
`isContinuous_twist chi (A := A) hA`. The former class-only spelling
`isContinuous_twist chi A hA` is replaced by one of these forms; the exact and
spectral consumers already used the canonical implicit representation argument.
The other three callable interfaces, universe parameter order, `rank_twist` simp
attribute, genuine scalar twists, and usual complex topology are preserved.
See the shared module's Markdown for the extraction and migration details.
