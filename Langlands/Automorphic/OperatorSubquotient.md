# Actual whole-operator automorphic subquotients

This internal construction retains a concrete numerator `upper` in the existing
`OperatorRealization` framework and a concrete invariant denominator `lower`
inside its actual vector space. The numerator is an actual subspace of the
stable automorphic functions. The proved full-form comparison identifies every
such subspace with its actual image in all automorphic forms and covers every
whole-operator invariant full-form subspace. `OperatorSubquotient` therefore
records actual subspace and quotient data, with every number-field universe and
natural rank explicit and complex coefficients fixed.

`Q.Space` is Mathlib's module quotient `Q.upper.Space ⧸ Q.lower.toSubmodule`.
`Q.representation` is Mathlib's induced quotient representation of the existing
concrete automorphic operator algebra. Denominator invariance supplies precisely
the hypothesis required by `Representation.quotient`; no action or desired
compatibility is added as an assumption. `Q.projection` is the canonical
equivariant `Submodule.mkQ`. It is surjective and its kernel is exactly the
specified denominator. Equality of its value with zero is exactly denominator
membership.

`Q.operatorAction` proves that the induced action retains its complex algebra
structure. Its multiplicative and unit laws are the quotient representation
laws. Its additive, zero and scalar laws are checked by quotient induction on
representatives. Typed equalities of numerator endomorphisms are carried
through the projection by congruence, followed by the projection's linear laws. Finite translation and standard infinite compact
translation are the restrictions along the same concrete generators.
`Q.envelopingAction` composes the induced algebra action with the genuine
existing enveloping differential homomorphism. Each action commutes with the
canonical projection. Finite translation and every differential commute,
because their actual numerator operators commute and the projection is
surjective.

The finite representation is smooth by the published surjective-intertwiner
transfer theorem applied to the same canonical projection and the proved
smoothness of the actual numerator. `Q.smoothRepresentation` bundles it in the
existing smooth representation category. `Q.localRepresentation v` restricts
along the actual finite-local inclusion and retains the entire quotient carrier;
its smoothness follows from continuity of that inclusion. This restriction
does not select a local irreducible tensor factor.

`Q.lift` is the universal descent of any whole-operator intertwiner that kills
the actual denominator. Its linear map is `Submodule.liftQ`; its covariance is
the numerator intertwiner identity, checked on representatives. The
`lift_projection` formula identifies the composite with the original map, and
surjectivity of the projection proves uniqueness. The target carrier has an
independent universe.

`Q.IsIrreducible` means irreducibility for the entire concrete operator action.
`Q.Equivalence T` is a genuine equivalence of those quotient representations;
it need not identify numerator and denominator presentations. `IsoClass`
quotients these actual data by existence of such an equivalence, with its exact
equality criterion. Its finite smooth representation class is well defined,
because the same linear equivalence intertwines finite generators.

Every existing realization supplies a zero-denominator quotient
`S.toSubquotient`. The canonical projection is bijective because its kernel is
zero and it is surjective; `S.toSubquotientEquiv` is the resulting whole-action
representation equivalence. This supplies concrete instances without asserting
existence of a nonzero or irreducible automorphic representation.

Provenance is internal: actual numerator realizations and their full-form
comparison, Mathlib's module quotient and induced representation, the existing
concrete generator algebra, and published smoothness transfer. No new
identification with original literature is claimed. No quotient evaluation map
into functions is asserted: representatives can differ by nonzero functions.
No topology, Hausdorff property, continuity of differential operators, local
factorization, irreducible constituent existence, isobaric construction or
spectral existence is supplied by this unit. Those remain separate obligations.
