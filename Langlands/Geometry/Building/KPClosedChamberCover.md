# Rational-point translates of a fixed closed chamber

For supplied `B : ValuationBuildingData G` over a nonarchimedean local
field, `ValuationBuildingData.closedChamberOrbitMap B c` sends a rational
point `g` and a point `y` of `facetClosure B.affineRoots c` to
`g • B.apartmentMap y` in the supplied reduced building. For regular `c`
this domain uses the closure of one fixed chamber.

`exists_normalizer_smul_of_mem_closedChamber` proves the apartment step:
for regular `c`, every apartment point `x` has the form `n • y` for
`y` in that closure and `n` in the actual rational normalizer of `B.i`.
The point `x` first lies in the closure of some chamber represented by
`d`, by local finiteness. The actual affine Weyl group carries the open
chamber of `c` to the open chamber of `d`. Its inclusion in the image of
the rational normalizer lifts this move to `n`. The normalizer preserves
the ordinary affine-root set, so it transports weak root signs and the
chamber closure. Hence `x` has a preimage in the closure of the chamber
of `c`.

`closedChamberOrbitMap_surjective` writes any reduced-building point as
`g • B.apartmentMap x` using the supplied quotient. Substituting the
normalizer move for `x` and using equivariance of the apartment map
makes this `(g * n) • B.apartmentMap y`. Thus rational-point translates
of the closure of the fixed chamber cover the entire reduced building.
This works also at rank zero and does not assert uniqueness of a group
representative, or coverage by a prescribed smaller subgroup.

## Source and limits

The apartment step is the covering part of the fundamental-domain
assertion in Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
Lemma 1.3.17 (printed p. 21 / PDF p. 52). The Library proofs used here
supply the corrected affine-root axioms and the lower inclusion of AS 5
(Axiom 4.1.6, printed pp. 159–160 / PDF pp. 190–191; Proposition 6.3.13,
printed p. 221 / PDF p. 252). The building step uses (7.6.2) and
Corollary 7.6.9 (printed pp. 264–266 / PDF pp. 295–297). This derived
map and its surjectivity give the fixed-chamber reduction at the start
of the proof of Lemma 13.4.4 (printed p. 473 / PDF p. 504); that lemma's
Lie-lattice content is not included.

The 1 November 2024 corrections add the infinite-fibre requirement to
AR 4 (PDF p. 2), included in the Library's root axioms. There is no
correction to §13.4 (PDF p. 49). Neither the apartment class nor the
building of an arbitrary group is constructed here, and no metric,
model, or Lie-filtration compatibility is concluded. No external code
is adapted.
