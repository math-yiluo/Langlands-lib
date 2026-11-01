# Character twists on exact finite-length smooth K0

This internal adapter constructs the scalar-character twist on the existing
exact finite-length smooth Grothendieck group. It applies to any commutative
coefficient ring `R`, group `G` with a supplied topology, and independent
coefficient, group and carrier universes. The character `χ : G →* Rˣ` has open
kernel so that the actual twisted action is smooth.

The algebraic theorem `Langlands.length_twist` identifies the group-algebra
module lengths before and after a scalar twist, including infinite length.
The proof composes Mathlib's subrepresentation/submodule order isomorphisms
with the published `twistSubrepresentationOrderIso`, and uses invariance of
Krull dimension under that order isomorphism. The finite-length equivalence
`Langlands.finiteLength_twist_iff` follows because a module has finite length
exactly when its length is not infinity. These two algebraic assertions need
neither a topology nor an open-kernel hypothesis.

`SmoothRep.twistFunctor_preservesFiniteLength` applies that equivalence to the
published actual `SmoothRep.twistFunctor`. The functor leaves the underlying
linear maps unchanged, so `twistFunctor_preservesShortExact` retains
injectivity, surjectivity and the equality of range with kernel for every
actual short exact sequence. This applies to nonsplit sequences as well.

`SmoothRep.FiniteLengthGrothendieckGroup.twist` is the integer-linear map
induced by that functor through the published exact quotient's `map`
construction. Its generator theorem `twist_ofRepresentation` sends every
actual finite-length smooth representation to the canonical class of its
literal character twist. Any finite-length proof for the output is accepted;
proof irrelevance identifies it with the internally constructed witness.

The theorems `twist_one` and `twist_mul` reduce to the actual-object generator
formula and the published smooth isomorphisms `twistOneIso` and
`twistTwistIso`. The multiplication formula is

```text
twist (χ * η) = twist χ ∘ twist η.
```

Each character occurring in that generic formula has an explicit open-kernel
proof. There is no assumption that the supplied topology makes `G` a
topological group. The inverse character has exactly the same kernel as the
original, which proves its open-kernel condition without such an assumption.
The inverse-composition theorems use the published equality of actual actions
under successive inverse twists. They yield `twistEquiv`, an integer-linear
automorphism of the full exact finite-length K0 whose inverse function is the
inverse-character map.

The construction uses actual smooth objects with finite length over `R[G]`.
It requires neither finite dimension over `R` nor admissibility, irreducibility,
a central character or a splitting of exact sequences. It preserves the
supplied carrier universe. In particular it applies to the existing complex
GL and product-Levi exact groups with saturated carriers `Type (max uF uV)`.

The provenance is derived internal content: the published scalar action,
subrepresentation order isomorphism, smooth twist functor, actual-object
isomorphisms, and universal exact-additive K0 map are combined directly. No
original-literature theorem is transcribed. This adapter supplies neither
commutation of Aubert with twists, a segment socle/quotient comparison, nor an
analytic square-integrability or classification theorem; those remain separate
proof obligations.
