# Rational formal atlas maps over supplied scalar structures

This internal construction combines rational coefficient extension from
`AtlasRationalBaseChange` with the supplied-target atlas and actual integral
formal-map transport from `AtlasBaseChangeAlong`. It makes no additional
original-literature assertion.

Let `O`, `R` and `S` be commutative rings, with specified `O`-algebra structures
where used, and let `F` be a field with an `O`-algebra structure. All coefficient
rings and coefficient tests have the same universe. The formal atlases have
finite, possibly different, coordinate types and equal original principal
covers. Rational Hom means the actual global tensor
`F ⊗[O] BasicAtlas.Hom`.

For two equal `O`-algebra structures `α` and `β` on `R`,
`RationalHom.reAlgebra` is an `F`-linear equivalence from rational Hom over
`α` to rational Hom of the transported atlases over `β`. Equality elimination
reduces its construction to the identity equivalence. The accompanying
theorems identify its action on rationalized integral maps,
prove preservation of the rational identity and composition, and identify
reflexive transport with the identity on every rational map.

For an `O`-algebra homomorphism `f : R →ₐ[O] S`,
`RationalHom.baseChangeAlong` is the composite of rational coefficient
extension to the coefficient algebra defined by `f` and transport to the
supplied `O`-algebra structure on `S`. The equality of these scalar structures
is the existing `coefficientAlgebraAlong_eq f`, proved from `f.commutes`.
The map is `F`-linear. The target atlases are exactly the previously constructed
`X.baseChangeAlong f` and `Y.baseChangeAlong f`; their principal covers are the
images of the original covers, and the equality of those image covers is
`baseOpens_eq (coefficientTest f) h`.

`baseChangeAlong_ofHom` identifies the extension of a rationalized integral
map with rationalization of its supplied-target integral extension. Its proof
uses the ambient rationalization law followed by scalar transport. The theorems
`baseChangeAlong_id` and `baseChangeAlong_comp` prove preservation of the
actual rational identity and formal composition using the corresponding
ambient and transport laws. `baseChangeAlongRingHom` bundles the endomorphism
case as a ring homomorphism for composition.

When `O` is also a domain and `F` is its fraction field,
`QuasiIsogeny.baseChangeAlong` applies the same map separately to the original
forward and inverse rational formal maps. Preservation of composition and
identity transports both inverse equations. The projection lemmas identify
both fields. Extension preserves `refl`, `symm`, `trans` and rationalization
`ofIso` of an actual integral atlas isomorphism. These proofs use
forward-map extensionality, the rational extension laws, and identification
of the supplied-target integral isomorphism's forward map.

This construction keeps the supplied target scalar structure, the selected
preimage generators of the image cover and global finite tensor sums.
It asserts no independence of those choices, injectivity, surjectivity,
successive base-change coherence, full-order equivariance, local rational
gluing, heights, framing, polarization, descent, levels or representability.
