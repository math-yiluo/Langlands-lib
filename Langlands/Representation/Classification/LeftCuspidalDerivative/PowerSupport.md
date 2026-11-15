# Powers of a supercuspidal representation and `A`-pure supports

Lean module: `Langlands.Representation.Classification.LeftCuspidalDerivative.PowerSupport`.

An internal module of the proof of
`Langlands.Classification.LeftCuspidalDerivative.LeftCuspidalDerivativeLemma`. Fix a
supercuspidal representation `A` of `GL_d` with `d > 0`. The module studies the cuspidal
product `A^K = A × ⋯ × A` (`K` factors) and the irreducible representations whose
supercuspidal support is a multiple of `A` ("`A`-pure"). The facts used are standard
(Bernstein–Zelevinsky 1977, Zelevinsky 1980): `A^K` is irreducible
(Zelevinsky 1980, Theorem 4.2, for one-term segments, which are never linked), the
supercuspidal support of a constituent of `ρ₁ × ρ₂` is the sum of the supports of `ρ₁`
and `ρ₂`, every irreducible representation embeds into a cuspidal product of its
supercuspidal support, and Frobenius reciprocity. Each of them is taken from the Library;
no hypothesis beyond those in the Lean statements is used.

## Definitions

* `cuspidalDatumOf hd A`: the cuspidal datum `⟨d, hd, [A]⟩` (rank `d`, isomorphism class
  of `A`), so that `A` represents it (`cuspidalDatumOf_isRepresentedBy`, by `rfl`) and its
  rank is `d` (`cuspidalDatumOf_rank`).
* `IsPure hd A ρ`: there is `j` such that `j` copies of `cuspidalDatumOf hd A` form a
  supercuspidal support of `ρ` (`T.IsSupercuspidalSupport`).
* `cuspidalPower hd A K h`: the cuspidal product `T.cuspidalProductInduced` of `K` copies of
  the datum of `A`, each represented by `A`, on `GL_n` where `h` says that `n` is the sum of
  the `K` ranks `d`.

## Declarations

* `isIrreducible_cuspidalPower`: for `K > 0`, `A^K` is irreducible. Proof: write `A^K` as the
  product of the one-term segment socles of a segment product datum
  (`SegmentProductDatum.ofCuspidals`, `ofCuspidals_hasSegmentSocles`,
  `ofCuspidalsInducedIso`); all segments equal the singleton segment of the datum of `A`,
  and two equal singleton segments are not linked; the Library theorem
  `unlinkedSegmentSocleProductIrreducible` gives irreducibility.
* `isSupercuspidalSupport_cuspidalPower`, `isPure_cuspidalPower`: for `K > 0`, `K` copies
  of the datum of `A` form a supercuspidal support of `A^K` (by definition, `A^K` being
  a subquotient of itself), so `A^K` is `A`-pure.
* `isPure_right_of_isSubquotient_binaryProduct`: if an `A`-pure irreducible `D` is a
  subquotient of `ρ₁ × ρ₂` with `ρ₁, ρ₂` irreducible, then `ρ₂` is `A`-pure. Proof: take
  supports `s, t` of `ρ₁, ρ₂` (`Aubert.SupportGrading.exists_isSupercuspidalSupport`);
  `s + t` is a support of `D` (`binaryProductConstituentSupport`); by uniqueness of
  supports (`Aubert.SupportGrading.isSupercuspidalSupport_unique`) `s + t` consists of
  copies of the datum of `A`, hence so does `t`.
* Helpers: `isSubrepresentation_of_iso` (subrepresentations pass along isomorphisms of the
  ambient representation), `normalizedProductInductionFunctor_obj_congr` (normalized product
  induction is congruent in the block shape), `generalLinearRankCast_obj_eq` (the rank-cast
  functor acts on objects as `castRank`).
* `isFirstBlockConstituent_of_isSubrepresentation_binary`: if an irreducible `Z` on `GL_m`
  embeds into `X × σ` (rank-transported along `a + k = m`, `a, k > 0`) with `X`
  irreducible, then `X` is a first-block constituent of `Z` (in the sense of
  `IsFirstBlockConstituent` from `BinaryGeometricPieceConstituentsStatement`). Proof:
  Frobenius reciprocity gives a nonzero map from the Jacquet module of `Z` to `X ⊠ σ`
  (`exists_jacquet_ne_zero_of_isSubrepresentation`, module `Frobenius`), and then `X` is a
  subquotient of the first-block restriction (`isSubquotient_firstBlock_of_ne_zero`, module
  `Product`).
* `exists_isSubrepresentation_cuspidalPower`: an `A`-pure irreducible `ρ` of positive rank
  is a subrepresentation of some `A^K`. Proof: `ρ` embeds into a cuspidal product of some
  data `κ` (`glSupercuspidalEmbedding`); the data `κ` then form a supercuspidal support of
  `ρ`, so by uniqueness all of them equal the datum of `A`; the embedding is then an
  embedding into `A^K` (`T.isCuspidalSubrepresentation_iff`).
* `nonempty_cuspidalPowerSuccIso`: `A^(K+2) ≅ A × A^(K+1)`, rank-transported along
  `d + m = n`. Proof: the head–tail regrouping of a product
  (`T.headTailProductInductionIso`) writes `A^(K+2)` as the binary product of (the
  universe lift of) its first factor and the product of the remaining `K + 1` factors
  (`SegmentHeadSupport.binaryNormalizedProductFunctor_obj_eq`,
  `normalizedProductInductionFunctor_rankCast_obj`); the universe lift of `A` is
  isomorphic to `A` (`SmoothRep.universeLiftEquiv`), and the tail product is `A^(K+1)`
  (equal block shapes, `normalizedProductInductionFunctor_obj_congr`).
* `cuspidalPowerOneEquiv`: `A^1` is equivalent to `A`, rank-transported along `d = n`
  (`T.singleBlockNormalizedProductEquiv` and `T.castRankEquiv`).
* `isFirstBlockConstituent_of_isPure`: `A` is a first-block constituent of every `A`-pure
  irreducible `ρ` of positive rank. Proof: `ρ` embeds into some `A^K`
  (`exists_isSubrepresentation_cuspidalPower`); `K = 0` contradicts positive rank. For
  `K = 1`, `A^1` is irreducible, so `ρ ≃ A^1 ≃ A` and `A` is a subquotient of `ρ` (the first
  alternative of `IsFirstBlockConstituent`). For `K + 2`, `ρ` embeds into `A × A^(K+1)`
  (`nonempty_cuspidalPowerSuccIso`), and
  `isFirstBlockConstituent_of_isSubrepresentation_binary` applies.
