# Bounded algebra equivalences and their homeomorphisms

Author: Worker 36.

`Langlands.Analytic.BoundedAlgEquiv K A B` is an actual K-algebra
equivalence between normed commutative rings, with positive linear norm
bounds for both directions. The coefficient field and two algebra carriers
may have independent universes. The definition requires algebra structures,
but neither normed algebra compatibility, completeness, ultrametricity nor
a nontrivial coefficient valuation.

The forward `toBoundedAlgHom` retains the given bound. `symm` exchanges
the two maps and bounds. `refl` uses bound one, and `trans` composes
bounded maps. `ofHomInv` constructs the equivalence from two bounded
algebra maps and proved pointwise inverse equations. The evaluation and
inverse lemmas follow directly from the underlying algebra equivalence;
the bounded-map identity and associativity lemmas are definitional.
These are intrinsic construction laws, not assumptions of a further
analytic-space or localization result.

The actual bounded multiplicative spectra have the published evaluation
topology. `spectrumHomeomorph` sends a point of B to its pullback along
the forward algebra map and uses the inverse map for its inverse.
Spectrum extensionality and the algebra inverse equations prove the two
inverse laws. The published continuity of spectrum pullback supplies both
continuity fields. `spectrumHomeomorph_apply` gives the formula
e.spectrumHomeomorph(x)(a) = x(e(a)).

When A and B also have normed K-algebra structures, `toHomeomorph`
constructs the homeomorphism between their underlying norm topologies.
It uses the continuous linear maps supplied by the two bounds. This
constructor does not infer boundedness from continuity or invoke an open
mapping theorem, including when the coefficient norm is trivial.

This is derived infrastructure for Berkovich's *Non-archimedean analytic
spaces* (Trieste 2009), Definition 2.1.11, p.8: the category of affinoid
spaces is opposite to the category of affinoid algebras and bounded
homomorphisms. The source does not separately define this Lean structure
or state its extension to general incomplete normed algebras. The
construction gives the explicit bounded inverse maps appropriate to that
category. Definitions 1.2.3 and 1.2.5, p.4, supply the spectrum and its
topology; the homeomorphism is derived from the already constructed
contravariant pullback. No presentation independence, analytic-domain
representability or structure sheaf is asserted.

Registered original: `berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
