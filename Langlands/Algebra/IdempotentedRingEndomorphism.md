# The actual right-linear endomorphism model

This module constructs the right-linear endomorphism model and its specified
pointwise uniformities for Renard I.1.6. Worker 6 supplied the construction and
interface checks; Worker 702 checked the source correspondence and completed
the function identities and documentation; Worker 345 audited the sources,
Markdown, complete declaration types and competing structures. The imported
constructions retain their original authorship.

The source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The source scope is the right-module remark of I.1.4, printed p.10/PDF16,
and the right-linear description and pointwise topology in I.1.6,
printed pp.11–12/PDF17–18. Chapter I conventions and I.1.1–I.1.6,
printed pp.5–12/PDF11–18, were read. Rings need not have an identity,
and their original multiplication need not be commutative.

## Actual algebraic constructions

All declarations below are in
`Langlands.Algebra.IdempotentedRingEndomorphism`.
For the original `A : Type uA` with `NonUnitalRing A`, `rightLinearEnd A`
is a `Subring (AddMonoid.End A)` whose membership is exactly
`β (a*b) = β a * b` for all original `a,b : A`. `RightLinearEnd A`
is its actual subtype. Addition is pointwise; multiplication is actual
composition, with the left factor applied after the right factor.
Zero and identity satisfy the equation directly. Addition and negation
use distributivity, and composition uses right linearity twice.
`mem_rightLinearEnd` and `rightLinearEnd_apply_mul` expose this equation.

`leftMultiplication : A →ₙ+* AddMonoid.End A` sends `a` to the
actual additive map `b ↦ a*b`. Its additive field is exactly Mathlib's
`AddMonoid.End.mulLeft`. The proof of multiplicativity is associativity
of the original ring. `leftMultiplicationRight` factors this map through
the concrete subring. Its value, evaluation, and the equality of the
entire composed nonunital ring map with `leftMultiplication` are exposed
by the corresponding `_val`, `_apply`, and `_subtype_comp` lemmas.
`leftMultiplication_coe` and `leftMultiplicationRight_coe` also identify
the complete underlying functions.

Under `hA : IsIdempotented A`, `toEnd hA x` is the actual additive
endomorphism with value `IdempotentedRingRightLimit.applyOriginal hA x a`.
`toEnd_coe` identifies its entire underlying function with that evaluation.
`toEndRingHom hA` installs exactly the published
`IdempotentedRingRightLimit.ring hA` on the published family carrier.
The existing intrinsic zero, addition, product and unit evaluation laws
prove it is a unital ring homomorphism into actual additive endomorphisms.
`toEndRingHom_coe` identifies its entire underlying function with `toEnd hA`.
`toRightLinearEnd hA` is its actual codomain restriction; its full
underlying endomorphism and the equality of the composed ring homomorphism
are retained by `_val` and `_subtype_comp`. `toRightLinearEnd_coe` also
identifies its complete underlying endomorphism map as families vary.

`toEndRingHom_apply_eq` gives `x.val e * a` for every idempotent `e`
with `e*a=a`, using the predecessor's choice-independent formula.
`toEndRingHom_idempotent` gives exactly `x.val e` at `a=e`.
`toRightLinearEnd_apply`, `toRightLinearEnd_apply_eq` and
`toRightLinearEnd_idempotent` expose these same actual evaluations directly
in the subring.
`toEndRingHom_canonical` identifies the entire endomorphism of the
published canonical family with `leftMultiplication a`;
`toRightLinearEnd_canonical` gives the same equality in the subring.

`idempotentEvaluation : RightLinearEnd A →+ IdempotentedRingRightLimit A`
sends `β` to the family `e ↦ β.val e`. Right linearity, `e*e=e`, and
`f*e=e` for `e≤f` prove fixedness and coherence in the actual family
carrier. Zero and addition are pointwise. `idempotentEvaluation_val`
is the exact coordinate formula, and `idempotentEvaluation_coe` identifies
the whole coordinate-function map. This construction needs no local units.

## Specified pointwise uniformities

`functionUniformSpace A` is the actual product uniformity on `A → A`
with exactly `idempotentedRingUniformSpace A` on every value coordinate.
`pointwiseUniformSpace A` is its comap through the actual function
inclusion of `AddMonoid.End A`. `rightLinearEndUniformSpace A` is its
restriction through the actual subtype inclusion. These named structures
are installed only locally. The `_eq_comap` lemmas record the exact
constructions, and `_eq_function_comap` composes the two actual inclusions.
The `_toTopologicalSpace` lemmas record the corresponding induced
pointwise and subspace topologies.

The actual function inclusion and subtype inclusion are uniformly
continuous by the comap construction. Every evaluation at an original
`a : A` is uniformly continuous, first by composition with a product
projection and then by composition with the subtype inclusion.
`uniformContinuous_evaluation` and `uniformContinuous_rightLinearEvaluation`
name both conclusions with the exact original value uniformity explicit.
No uniformity is a supplied certificate, and the values use the original
right-annihilator uniformity of Renard I.1.3 rather than discrete values.

## Provenance and limits

The right-linear model and the pointwise topology are source constructions.
The explicit `Subring`, nonunital and unital ring homomorphisms,
`UniformSpace` comaps and intrinsic interface lemmas are internal packaging
of those constructions. The actual family, ring, internal evaluation,
canonical map and original uniformity are imported by their published
Lean names, with their original authorship retained.

All constructions retain the arbitrary original universe `uA`; the
endomorphism and family carriers remain in that universe. No identity,
nontriviality, field, dimension, countability, completeness or density
hypothesis is added. Zero rings need no extra hypothesis.
The two inverse identities, a ring equivalence, comparison with the
specified family topology, the I.1.6 closure lemma, natural endomorphisms
of the forgetful functor and categorical centres are later obligations.
This unit makes no topological-ring assertion about the full endomorphism
ring.

The supplementary *Corrections et compléments* for the 2010 edition,
registered as `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was checked at PDF1–3. Its p.13 correction to a barred completed-ring
intersection belongs to the later topology comparison, and is reflected
in the governing 2026 text. It does not alter this unit's definitions.

## Declaration and edge-case checks

The source contains complete unapplied assignments of the principal
construction constants and their evaluation, full-map, canonical,
comap, induced-topology and uniform-continuity interfaces. Every such
assignment includes the entire original-ring telescope; all are repeated
at arbitrary `uA`, `uA = 0` and `uA = 1`. These checks exercise the actual
published family ring in the ring-homomorphism types and the exact named
uniformities in every uniform-continuity type.

A further section makes a competing ring on
`IdempotentedRingRightLimit A` and competing uniformities on `A`, `A → A`,
`AddMonoid.End A` and `RightLinearEnd A` available to typeclass search.
It checks that the named constructions, their complete ring maps and
coordinate formulas, exact comaps and induced topologies, and uniform
continuity interfaces continue to refer to the specified constructions.
The additive idempotent-coordinate formula also remains unchanged.

The final examples assume only `Subsingleton A` in addition to the original
`NonUnitalRing A`. The zero idempotent supplies the finite local units,
both family-to-endomorphism maps have zero values, idempotent evaluation
is zero, and every original left multiplication in the subring is zero.
These proofs use extensionality and subsingleton elimination, with no
original identity or nontriviality assumption.
