# Common-image multiplicity-one criterion

`Langlands.Classification.CommonImageMultiplicityOneStatement` is an internal
abstract criterion for constructing strong irreducible endpoints. Its group
`G`, monoid `H`, smooth carrier, functor-image carrier and test carrier have
independent universe parameters.

Let `F` be an additive functor from complex smooth `G`-representations to
complex `H`-representations which preserves epimorphisms and monomorphisms.
Suppose the images of two actual smooth representations `A` and `B` each
have Jordan–Hölder multiplicity one at the same test representation `τ`.
These multiplicity hypotheses retain actual finite simple-series witnesses.
Suppose also that every actual nonzero surjective map from `A`, and every
actual nonzero injective map into `B`, has a functor-image target or source,
respectively, with a positive finite-series `τ`-count. The detection
hypotheses apply to arbitrary smooth representations, without an
irreducibility restriction.

For every actual nonzero map `f : A ⟶ B`, the assertion supplies a smooth
representation `P` and actual maps `q : A ⟶ P` and `j : P ⟶ B`. The map `q`
is surjective, `j` is injective, and `f = q ≫ j`. Moreover, `P` is a strong
irreducible head of `A` and a strong irreducible socle of `B`. The head
conclusion includes equality of the kernels of all irreducible quotient
maps of `A`; the socle conclusion includes equality of the images of all
irreducible embeddings into `B`, in the smooth carrier universe.

This statement neither assumes ambient finite length nor assumes the
existence of a simple endpoint. It does assume finite simple series and
positive counts for the particular functor images specified above. There
is no assertion that an arbitrary induction or Jacquet functor satisfies
these hypotheses.

The provenance is an internal elementary deduction intended to supplement
the published `MultiplicityOneConstituentCriterionStatement` and
`SimpleEndpointMultiplicityOneStatement`. The proposed argument uses the
actual image of `f`, the subrepresentation and quotient constructions in
`Category.Subquotients`, and Jordan–Hölder additivity and monotonicity.
It is not an attribution of this abstract assertion to a printed theorem.
This module defines the proposition; its proof is a separate unit.
