# Tensor coordinates for affine cartesian relation morphisms

Author: Worker 148.

This internal adapter identifies the source-cartesian square of an actual
affine scheme relation morphism with the tensor presentation used by
`GroupoidCoaction.pushforward`.

For a pushout of commutative rings with maps `B → D`, `B → C`,
`D → P`, and `ρ : C → P`, `tensorEquivOfIsPushout` compares the supplied
pushout to Mathlib's tensor-product pushout. It yields a `D`-algebra
equivalence `P ≃ₐ[D] D ⊗[B] C`. The inverse sends `1 ⊗ c` to `ρ c`;
thus its `cartesianBaseMap` is exactly `ρ`.

For a cartesian morphism `(f,g) : E' → E`, assume `E'.U`, `E.U`, and `E.R`
are affine. Global sections of the source pullback square form a pushout,
by Mathlib's `isPushout_appTop_of_isPullback`. Flipping this pushout and
applying the ring construction defines `sourceTensorEquiv`, where
`B = Γ(E.U)`, `C = Γ(E.R)`, `D = Γ(E'.U)`, and `P = Γ(E'.R)`. The algebra
structures use the actual source maps and `f.appTop`.

`sourceTensorEquiv_baseMap` identifies the relation-ring map with `g.appTop`.
Applying global sections to `g ≫ E.t = E'.t ≫ f` then proves
`sourceTensorEquiv_target`, exactly the target compatibility required by
coaction pushforward. No finiteness, surjectivity, quotient, or vanishing
assumption enters this construction.

`isClosedImmersion_of_hasAffineQuotient` proves a separate geometric fact.
For an affine quotient `q : E.U → M`, its defining pullback identifies
`E.R` with `E.U ×[M] E.U`. The natural morphism from this fiber product to
`E.U × E.U` is a closed immersion: it is a base change of the diagonal of
the affine, hence separated, scheme `M`. The implemented proof uses
Mathlib's `pullback.mapDesc` and the canonical pullback and product
isomorphisms. Equality of the two product projections identifies the
composite with `prod.lift E.t E.s`. This assertion itself does not require
`E.U` to be affine.

When `E.U` is affine, the same quotient pullback also makes `E.R` affine.
`ringRelation_of_hasAffineQuotient` therefore applies the published
`etaleEquivalenceRelationRingForm` theorem with the closed immersion just
proved. Its conclusion is the actual `RingEtaleEquivalenceRelation`
for `E.t.appTop`, with the source algebra structure supplied by
`E.s.appTop`. It adds no closed-immersion premise to the affine-quotient
assumption.

This is an internal universal-property argument using Mathlib's tensor
pushout and affine duality, with the unchanged published scheme and
coaction conventions. The main geometric acyclicity theorem remains open.
