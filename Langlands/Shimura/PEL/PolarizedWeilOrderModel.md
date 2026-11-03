# Polarized rational actions on actual integral order models

This internal construction assembles the existing actual integral order-model
results into the published `PolarizedWeilLevel.PolarizedAction`. It is a
supporting step for the rational-isogeny comparison in the Harris CM problem.
It assumes a supplied integral order model and selected dual witnesses for its
abelian scheme; it does not prove their existence or representability.

Let `X` be an actual polarized faithful rational action of a possibly
noncommutative rational algebra `R` with a star-ring structure on an abelian
scheme `A` over `S`. The original involution equation is part of `X`. Let `O`
be an integer subalgebra whose underlying submodule is a full rational lattice,
let `b` be an integer basis of `O`, and let `M` be an `IntegralOrderModel` of
the restriction of the original action to `O`. Thus `M` contains an actual
abelian scheme `B`, its actual integral action, integral maps `f : A → B` and
`g : B → A`, and a positive integer `N` with both composites equal to
multiplication by `N`. The model includes equivariance of its forward map.
The index universe of `b` is arbitrary; this assembly requires no new
finiteness premise on that index.

The existing `Prerequisites` package supplies the named tensor, Picard and
base-change propositions. A `DualWitness B` selects the actual model dual,
its geometry, an inverse Poincare bundle and an evaluation isomorphism.
The base has a structural map to the spectrum of a characteristic-zero field
in the same universe. The declarations retain exactly the hypotheses needed
by their underlying constructions; no new dual-isogeny or polarization
compatibility hypothesis is added.

`PolarizedAction.dualWitness` merely bundles the selected dual data already
contained in `X`.

`PolarizedAction.orderModel` has rational action equal to the existing full
rational extension of `M.action` using `b`. Its actual polarization is the
existing `IntegralOrderModel.dualPullbackHom`, namely
`g ≫ X.polarization ≫ gᵛ`, with the actual constructed contravariant dual.
Its geometric polarization proof is
`IntegralOrderModel.dualPullback_isPolarization_overField`: the same nonzero
integer is a global unit over the characteristic-zero field scheme, and the
actual inverse-multiple data certify the original and dual isogenies.
Faithfulness follows from `rationalExtension_injective_iff`. The full original
involution equation follows from `dualPullback_involutionCompatible`, using
reverse equivariance for every element of `R`. Actual dual-map additivity for
each ordered pair is supplied by `relativeDualSchemeMapAdditivity`; it is not
an additional assumption on the model.

`PolarizedAction.orderModelIso` is the existing `rationalAlgebraIso`. Its
forward rational map is exactly the rationalization of `f`; its inverse is
`N⁻¹` times the rationalization of `g`.
`PolarizedAction.orderModelRestriction` uses exactly `M.action` on that same
polarized representative. Its agreement on each order element is the published
`integralActionRationalExtension_coe` identity.

`PolarizedAction.orderModelMultiple_pos` proves positivity of `N²` from
nonvanishing of `N`. `PolarizedAction.orderModelMultiple` proves the existing
`Multiple` relation for the displayed rational isomorphism and the unit with
value `N²`. It is precisely the identity
`f ≫ (g ≫ X.polarization ≫ gᵛ) ≫ fᵛ = N² • X.polarization`
after rationalization, supplied by
`IntegralOrderModel.dualPullback_multiple`. The relation retains the given
`PairAdditivity` proof of the existing polarized-class construction; proof
irrelevance identifies it with the published actual additivity proofs.
No multiplier or rational representative is replaced.

This module constructs no integral order model, relative dual, determinant
condition, level orbit, moduli scheme or natural comparison of presheaves.
It supplies the polarized action and exact algebraic comparison for an already
constructed model. The full division-case CM representability statement
remains a separate obligation.
