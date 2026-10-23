# Spectra and actual unramified principal-series constituents

This module connects unordered nonzero complex spectra to the existing actual
unramified characters, normalized principal series, and irreducible admissible
smooth representation objects. Its provenance is internal: it specializes and
composes the published constructions in `Group/GL/UnramifiedCharacter`,
`Correspondence/UnramifiedNormalization`, `Correspondence/AutomorphicRelations`,
and `Representation/Unramified/Eigenvalues`. The new proofs are character
reconstruction and transport along actual equivariant linear equivalences. No
external classification theorem is claimed.

## Fields, coefficients and universes

The field is `F : PadicField.{uF} p` with `[Fact p.Prime]`. Field topology and
topologies on the actual matrix groups are the canonical ones supplied by `F`.
All characters have values in the units of the usual complex field; all
representations are complex representations. There is no unitarity or
finite-dimensionality restriction on their carriers.

Character tuples have arbitrary natural rank `n`, including zero. Principal
series and constituent relations have positive rank `r + 1`, following the
existing `Correspondence` API. The representation carrier universe `uV` is
independent of `uF`. Equivalence transport allows independent target carrier
universes `uV` and `uW`; the general subquotient lemma also allows an independent
source carrier universe `uU`.

The declarations below are in `Langlands.Unramified`.

## Actual characters and their values

`character F z` is the existing continuous unramified character
`x ↦ z ^ ord(x)`, for any `z : ℂˣ`. The order is the canonical normalized
additive valuation. Its uniformizer value is exactly `z`, and it is trivial on
the kernel of the canonical normalized absolute-value character, the actual
valuation-unit subgroup. The module reuses the proved continuity,
unramifiedness and uniformizer evaluation; it does not supply these facts as
assumptions.

`character_eq_of_unramified` proves that an arbitrary continuous unramified
character is recovered from its uniformizer value. It applies the existing
classification of unramified monoid characters and then continuous-homomorphism
extensionality.

`characterTuple F z` applies this construction to every entry of a tuple.
`characterValues F χ` evaluates each continuous character at the chosen
canonical uniformizer. `characterSpectrum F χ` forgets the order of those unit
values through `Eigenvalues.ofTuple`, retaining multiplicities. The last two
definitions also accept ramified characters, but no classification or
reconstruction assertion is made for such characters.

The module proves both reconstruction identities: evaluating `characterTuple`
recovers its input tuple, and reconstructing from `characterValues` recovers
`χ` when every character is unramified. It also proves
`characterSpectrum F (characterTuple F z) = Eigenvalues.ofTuple z`.
`exists_characterTuple` uses tuple enumeration of the symmetric power and the
explicit character construction to realize every spectrum by continuous
unramified characters. This is character existence, not existence of an
irreducible constituent.

## Principal series and the object relation

`principalSeriesOfTuple F z` is literally
`Correspondence.principalSeries F r (characterTuple F z)`. Thus it is the
existing normalized induction from the upper Borel, with `r + 1` blocks of
size one, whose factors are the characters composed with the actual `GL₁`
determinant. The normalizing character and induced carrier are inherited from
the published construction. No new normalization or arbitrary representation
carrier is introduced.

`IsSphericalConstituent F z A` requires two conditions on an actual
`AutomorphicObject F r.succPNat`:

- its fixed-vector submodule under `Correspondence.sphericalSubgroup F r` is
  nonzero;
- it is a subquotient of `principalSeriesOfTuple F z` in the existing sense:
  an actual subrepresentation of that principal series has a surjective
  intertwining map onto `A.obj.representation`.

The object already carries smoothness, irreducibility and admissibility.
Despite its inherited `AutomorphicObject` name it is a local representation
object; global automorphy is not asserted. Genericity is not required. In
particular this relation does not restrict the construction to the generic
constituents of Rankin–Selberg theory.

`HasSphericalSpectrum F A s` says that some tuple `z` enumerating the multiset
`s` has `IsSphericalConstituent F z A`. The existential enumeration makes this a
relation on the actual unordered spectrum. It does not assert that every
ordering has the same constituents. Nor does it select a constituent, assume
one exists, or impose uniqueness by a field in a data structure.

`hasSphericalSpectrum_iff_characters` proves an alternative formulation using
any unramified inducing character tuple `χ`: its uniformizer spectrum is `s`,
`A` has nonzero spherical fixed vectors, and `A` is a subquotient of the existing
`principalSeries F r χ`. The forward direction uses `characterTuple`; the
reverse direction uses `characterValues` and the proved reconstruction of
unramified characters.

## Equivalence invariance and classes

`isSubquotientOf_iff_of_equiv` proves that equivalence of target representations
preserves the actual subquotient relation. The source subrepresentation is
unchanged, and its surjective intertwiner is composed with the target
equivalence. The reverse direction composes with the inverse equivalence.
This argument permits different target carrier universes.

`isSphericalConstituent_iff_of_equiv` combines that lemma with the existing
transport of nonzero fixed spaces. `hasSphericalSpectrum_iff_of_equiv` then
transports the existential tuple witness. These are proved invariance laws,
not assumptions in the relation.

`HasSphericalSpectrumClass F π s` says that a representative of the actual
quotient class `π` satisfies `HasSphericalSpectrum`. The theorem
`hasSphericalSpectrumClass_classOf` identifies this with the object relation
on every chosen representative: equality of genuine quotient classes supplies
an equivariant linear equivalence, to which the preceding invariance law
applies. Thus the relation does not depend on a preferred carrier or a chosen
class representative.

`HasSphericalSpectrumClass.isSpherical` extracts the nonzero fixed space and
proves the existing `Correspondence.IsSphericalClass F π` condition.

## Remaining theorem boundaries

The module proves neither existence of a spherical irreducible constituent for
each inducing spectrum, nor exhaustion of spherical representations, uniqueness
of the associated spectrum or constituent, nor the one-dimensionality of the
spherical fixed space. It also does not compare the spectrum with spherical
Hecke eigenvalues. These remain separate representation-theoretic and
normalization obligations. In particular no Satake parameter function or
bijection is obtained here by choice from an assumed classification.

The Euler polynomials and all natural power traces of a spectrum remain those
of the imported `Eigenvalues` module. This module introduces no additional
power of the residue cardinality into the inducing uniformizer values. The
interpretation of these quantities as invariants of a spherical representation
requires the separate existence, uniqueness and Hecke comparison theorems.
