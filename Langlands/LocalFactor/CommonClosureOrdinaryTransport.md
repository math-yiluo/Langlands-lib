# Actual ordinary spectral transport to the standalone extension

Worker 40 authored this derived compatibility construction. Its namespace is
`Langlands.LocalFactor.CommonClosureSpectral.Transport`. It attaches the existing
continuous exact virtual group and its spectral twists to the actual standalone
Weil group of an extension field.

## Fields and spectral characters

Fix a prime `p`, fields `F : PadicField.{uF} p` and
`E : PadicField.{uE} p`, and an actual algebra homomorphism
`f : F.Carrier →ₐ[Padic p] E.Carrier`. The field universes are independent.
Write `J = LocalClassField.extensionFiniteIntermediate F E f` for the published
image field in the chosen common closure of `F`, and
`e = extensionImageWeilEquiv F E f` for the published topological group
equivalence from `W_E` to the fixing subgroup `W_J` in `W_F`.

Let `r = extensionResidueDegree F E f` and let `q_F`, `q_E` be the actual
canonical residue-field cardinalities. The published arithmetic identities are

\[
q_E=q_F^r,\qquad d_F(e(w))=r\,d_E(w).
\]

Here `d_F` on `W_J` is the ambient base-field integer degree; it has not been
renormalized. In particular it takes the value `r` on the image of a
standalone geometric degree-one element.

`spectralParameter_residueDegree` proves, for every `s : ℂ`, the equality
of nonzero complex units

\[
 \exp(-s\log q_E)=\exp(-s\log q_F)^r.
\]

The proof uses the actual cardinality identity, the real logarithm of a natural
power, and the exponential of a natural multiple. It casts real logarithms into
`ℂ`; no branch of the complex logarithm is used.

`character_comp` identifies the pullback along `e` of
`CommonClosureSpectral.character F J s` with
`SpectralTwist.character (localDegree E) q_E hq_E s`. The equality is an equality
of continuous homomorphisms to `ℂˣ`, not an additional input. At `w` it reads

\[
 \exp(-s\log q_F)^{d_F(e(w))}
 =\exp(-s\log q_E)^{d_E(w)}.
\]

Its proof uses the two arithmetic identities above and the power law in `ℂˣ`.
The complex coordinate `s` is unchanged. Equality of the cardinalities of `E`
and `J` alone would not prove this comparison, since the common-closure
character uses `q_F` and the ambient degree.

## The exact virtual equivalence

`StandaloneVirtual E` abbreviates the published
`SpectralTwist.ContinuousVirtual (G := localWeilGroup E)` with an independent
vector-space universe. This is the existing exact Grothendieck group of
finite-dimensional complex representations satisfying `IsContinuous`.
It imposes the actual short exact sequence relations on isomorphism classes;
it is not a free group on irreducibles or a quotient by only direct sums.
Continuity is the published endomorphism-topology continuity predicate.

`virtualEquiv F E f` is the integer-linear equivalence

```lean
CommonClosure.Virtual.{uF, uV} F J ≃ₗ[ℤ]
  StandaloneVirtual.{uE, max uF uV} E
```

constructed by `ExactGrothendieckGroup.continuousRestrictEquivalence e`.
The vector-space universe is `max uF uV` on both sides. Its forward map
restricts a representation along `e`; the inverse restricts along `e.symm`.
The underlying vector spaces and linear maps are retained, so actual
short exactness is retained. The published restriction construction proves
continuity and descent to the exact quotient, as well as the inverse laws.

`virtualEquiv_ofRepresentation` exposes this forward map on each continuous
representation generator: the class of `A` maps to the class of
`FiniteRepresentation.restrict e.toMonoidHom A`. Its continuity certificate
comes from the continuity of `e` and of `A`.

`degree_virtualEquiv` proves preservation of the genuine virtual dimension
in `ℤ`. It specializes the published dimension identity for continuous
restriction. In particular dimension-zero elements remain dimension zero;
this file does not introduce a separate equivalence of those subgroups.

`virtualEquiv_twist` proves that transport commutes with spectral twisting:

\[
 T(\operatorname{Tw}_{F,J}(s)x)
   =\operatorname{Tw}_E(s)(T(x)),\qquad T=\texttt{virtualEquiv F E f}.
\]

This holds for every virtual class and every complex `s`. The proof first
compares the two composite integer-linear maps. Extensionality for the exact
Grothendieck group reduces to representation generators. On a generator,
the identity on its underlying vector space intertwines the two
representations by `character_comp`. Equality of their classes then supplies
the identity on the entire exact quotient.

## Provenance and scope

The original conventions are in Tate, *Number theoretic background* (1979),
§3.6, printed page 17 / Part II PDF page 26, for twists by the complex power
of the norm in the Deligne and Langlands conventions, and §4.1.3, printed
page 20 / PDF page 29, for the integer degree defined by
`ν(w)=q^(-d(w))`. These pages were read directly during development.
Registered source: `tate-1979-number-theoretic-background`; PDF SHA-256:
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.

The attachment itself is internal derived content. The existing
`ClassFieldTheory.Local.ReciprocityTransport` supplies `e` and its degree law;
the published local-field residue construction supplies
`extensionResidueCardinality`. `CommonClosureSpectral` and `SpectralTwist`
supply the characters and twists; `VirtualRepresentation.ExactRestriction`
supplies restriction on the exact quotient. The proof combines these actual
constructions rather than assuming a character or virtual-group comparison.
No separate cross-closure comparison theorem is attributed to Tate.

This unit concerns continuous ordinary representations and their exact virtual
classes. It assumes no semisimplicity, no independent open-inertia condition,
no local reciprocity isomorphism, and no supplied epsilon assignment. It does
not identify this category with every representation category in Tate.
It neither constructs nor transports a full nonabelian epsilon system and
does not prove its existence, a functional equation, or existence of self-dual
measure. It does not compare different closure choices or prove coherence
under composition of field embeddings. Those obligations and completion of
the broad host task remain separate.
