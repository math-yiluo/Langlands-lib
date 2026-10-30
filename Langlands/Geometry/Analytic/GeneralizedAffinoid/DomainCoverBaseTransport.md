# Finite full-domain covers under bounded base equivalences

Worker 56 transports a supplied finite cover by actual full affinoid domains
along a bounded equivalence of the base algebras. This internal construction
uses the published `DomainBaseTransport` and `DomainTopology` modules.

The field is a complete ultrametric normed field. Both bases are actual
presented positive-polyradius affinoid quotient algebras, and the bounded
equivalence has bounded forward and inverse algebra maps. Each component's
full domain representation is transported by the published construction,
which retains its representing algebra and bounded restrictions while changing
the structural base map and taking the homeomorphism preimage of the locus.

The family coverage equivalence uses surjectivity of the actual base-spectrum
homeomorphism in one direction and direct preimage membership in the other.
It applies to any supplied index type, without a finiteness assumption.
`transportBase` applies it to the finite family of a supplied cover. The size,
objects, representing algebras and actual bounded restrictions are exposed by
the accompanying projection lemmas. The concrete singleton identity cover is
preserved.

The transported loci are homeomorphic to the original loci. The component
and total spectrum-map equations prove that the cover diagrams commute over
these homeomorphisms. Each component's representing algebra and index are
retained, so the original and transported disjoint unions of actual spectra
are definitionally the same. The component equation follows by subtype
extensionality and the published structural spectrum equation; evaluating it
on each disjoint-union component proves the total-map equation.

The original is Berkovich, *Non-archimedean analytic spaces* (Trieste lectures,
2009), source `berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Definition 2.1.11 on printed/PDF p.8 gives the bounded affinoid morphisms,
and Definition 2.2.1 on p.9 gives full affinoid-domain representations.
These are the imported source inputs. The finite-cover transport and commuting
diagrams are internally derived from the actual bounded equivalence and its
published domain transport, rather than separately named source theorems.

The construction allows zero cover size, empty loci, trivial valuation and
zero quotient algebras. It is transport along a bounded base equivalence;
arbitrary analytic base change, intersections, analytic sheaves, atlases,
and sites remain separate construction obligations.
