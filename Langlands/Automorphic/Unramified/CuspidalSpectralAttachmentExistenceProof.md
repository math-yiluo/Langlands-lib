# Genuine cuspidal spectra in an independent factor universe: proof

Module: `Langlands.Automorphic.Unramified.CuspidalSpectralAttachmentExistenceProof`.

The theorem `Langlands.Automorphic.Unramified.cuspidalSpectralAttachmentExistence`
proves the published proposition
`Langlands.Automorphic.Unramified.CuspidalSpectralAttachmentExistenceStatement.{uF, uV}`
of [CuspidalSpectralAttachmentExistenceStatement](CuspidalSpectralAttachmentExistenceStatement.md).
Both universe parameters stay independent: the number field lives in `uF`, the
local factor carriers in `uV`, and `uV` may lie below, at or above `uF`
(`uV = 0` included). The only axioms are `propext`, `Classical.choice` and
`Quot.sound`.

## Statement proved

Take a number field `F : Type uF` with `[CompactSpace (AdeleQuotient F)]`, a
natural number `r` and a cuspidal operator realization
`T : CuspidalOperatorRealization F r`. Then some
`s : SpectralSystem (FinitePlace F) (r + 1)` satisfies
`IsoClass.HasSpectralSystem.{uF, uV} T.isoClass s`. In other words, an actual
`CuspidalSpectralPresentation.{uF, uV}` of a realization in the class of `T`
has numerical spectrum `s`. The theorem uses exactly these hypotheses: it
assumes nothing arithmetic or spectral about `T`.

## The implemented proof

1. `Langlands.Automorphic.cuspidalIrreducibleAdmissibleFiniteSliceExistence`
   ([CuspidalAdmissible/Existence](../CuspidalAdmissible/Existence.md)) gives a
   finite slice `A` of `T` whose finite adelic action is irreducible and
   admissible.
2. `CuspidalOperatorRealization.exists_presentation_of_finiteSlice`
   ([CuspidalSlicePresentation](../CuspidalSlicePresentation.md)) applies
   Flath's factorization theorem for restricted products,
   `FlathRestrictedProductExistenceStatement`, to the finite adelic action on
   `A`; the hypothesis that almost all spherical Hecke algebras commute is
   Gelfand's commutativity theorem. The result is a presentation
   `P : CuspidalSpectralPresentation.{uF, uF} T` whose local factors lie in the
   field universe, with an irreducible admissible actual local component at
   every finite place.
3. `CuspidalSpectralPresentation.exists_small`
   ([CuspidalPresentationUniverse](../CuspidalPresentationUniverse.md)) turns
   `P` into a presentation `Q : CuspidalSpectralPresentation.{uF, uV} T` of the
   same realization, still built on the actual finite slice `A`. At each place
   it picks an irreducible smooth factor with carrier in `Type uV` that is
   equivalent to the factor of `P`, using `exists_small_finiteLocalFactor`, which
   specializes the published `Langlands.padicIrreducibleSmoothSmallRealization`.
   That theorem takes a nonzero vector. Its open stabilizer makes its orbit
   countable in the separable local group, and by irreducibility the orbit
   spans the representation over `ℂ`. A countable linearly independent subset of
   the orbit is then a basis, which gives a carrier of finitely supported complex
   functions in `Type uV`. `CuspidalSpectralPresentation.mapFactors` carries the
   reference vectors and the restricted tensor equivalence onto the same embedded
   finite realization along these equivariant linear equivalences. It then
   builds the spherical spectra again from the transported local actions.
4. `CuspidalOperatorRealization.IsoClass.hasSpectralSystem_iff`
   ([CuspidalSpectralPresentation](../CuspidalSpectralPresentation.md)) at the
   representative `T` turns `Q` and the equation
   `Q.spectralSystem = Q.spectralSystem` into
   `HasSpectralSystem.{uF, uV} T.isoClass Q.spectralSystem`. The witness `s` is
   therefore `Q.spectralSystem`.

Step 3 covers every factor universe, so the proof does not use the universe
raising construction `CuspidalSpectralPresentation.universeLift` of
`Langlands.Automorphic.CuspidalSpectralUniverseLift`.

## Sources

Step 2 rests on Flath (1979), *Decomposition of representations into tensor
products* (`flath-1979-tensor-products`), Proceedings of Symposia in Pure
Mathematics 33, part 1. The direct source of the existence assertion
`FlathRestrictedProductExistenceStatement`, which
`CuspidalOperatorRealization.exists_presentation_of_finiteSlice` uses, is §2,
Theorem 2, printed p. 181 (PDF p. 177 of the Corvallis Part I volume): if the
spherical Hecke algebras of a restricted product of locally compact totally
disconnected groups are commutative at almost all places, then every
admissible irreducible representation is a restricted tensor product of
admissible irreducible local factors, almost all with one-dimensional
spherical fixed spaces. The restricted tensor construction it refers to is
§2, printed pp. 180–181 (Example 2). Theorem 3 of §3, printed pp. 181–182,
is the corresponding statement for the full adelic group `G(𝔸)`, with
admissible `(𝔤ᵥ, Kᵥ)`-modules at the archimedean places of a number field. It
gives the context of the argument but is not the statement used here, since
the slice carries only the finite adelic action. The universe statement is a
derived Library interface and has no literature counterpart. Steps 3 and 4 are constructions inside the Library. The target
Markdown explains why an attached spectrum is wanted at every degree: weak
transfer in Arthur–Clozel (1989) (`arthur-clozel-1989-base-change`), III.1.1,
printed p. 199, uses one.
