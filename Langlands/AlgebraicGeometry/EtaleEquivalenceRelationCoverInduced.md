# Acyclic induced modules pushed from an affine quotient cover

Author: Worker 148.

This internal adapter combines the actual scheme source-cartesian tensor
coordinates with the affine quotient's invariant-ring presentation and the
coaction pushforward theorem. It supplies the induced-cover case needed in the
planned proof of `EtaleEquivalenceRelationComodulesAcyclicStatement`; it does not
prove that full statement.

Let `E' → E` have object map `f` and relation map `g`, with the unchanged
`E'.IsCartesianHom E f g` property. Assume `E'.U`, `E.U` and `E.R` are affine,
that `(E.t, E.s)` is a closed immersion, and that `E'.HasAffineQuotient` holds.
Set `B = Γ(E.U, ⊤)`, `C = Γ(E.R, ⊤)`, `D = Γ(E'.U, ⊤)` and
`P = Γ(E'.R, ⊤)`. The source maps supply the `B`-algebra structure on `C` and
the `D`-algebra structure on `P`; `f.appTop` supplies `B → D`.
Let `A'` be the published invariant ring of the covering relation, using that
source algebra structure. For any `A'`-module `N`, the coefficient module is
`D ⊗[A'] N`, with its natural `B`-action on the first tensor factor through
`f.appTop`. The scheme universe `u` and module universe `v` are independent.

`coverInduced` constructs a `GroupoidCoaction E.t.appTop.hom` on this module.
It pushes forward the actual `GroupoidCoaction.induced E'.t.appTop.hom N`
through `sourceTensorEquiv`, using `sourceTensorEquiv_target` for target
compatibility. The composite `B → D → P` provides the auxiliary compatible
scalar tower. The base ring relation laws come from
`etaleEquivalenceRelationRingForm`; the covering laws come from
`ringRelation_of_hasAffineQuotient`. No affine assumption on `E'.R` is added:
the cartesian square and quotient constructions supply the needed consequences.

`coverInduced_oneCohomologyVanishes` applies
`invariantPresentation_of_hasAffineQuotient` to the actual covering quotient.
This gives faithful flatness of `D` over the actual `A'`, together with
`D ⊗[A'] D ≃ₐ[D] P` taking `1 ⊗ d` to the target of `d`. The proved
`pushforward_induced_oneCohomologyVanishes` then gives the published degree-one
cocycle predicate's vanishing for `coverInduced`.

`coverInduced_isAcyclic` uses the same presentation and
`pushforward_induced_isAcyclic`. Its conclusion is exactly the unchanged
`GroupoidCoaction.IsAcyclic` invariant-lifting property for this base coaction.
It is not an assertion about every base coaction or an independently defined
sheaf-cohomology theory.

These are internal consequences of the imported universal-property,
faithfully flat, induced-module and pushforward results; no additional
literature assertion is introduced. In particular, neither the finite
surjectivity of `f` nor Noetherian hypotheses are needed for this induced-cover
case. Passing from these modules to arbitrary base comodules remains a separate
obligation. No affine-descent conclusion is assumed.
