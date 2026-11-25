# Affine-space normalization of the assembled varying-dimension structure

This derived statement supports the scheme-agreement part of the
analytic-manifold assertion in Brian Conrad, *Weil and Grothendieck approaches
to adelic points*, December 31, 2011, printed p.15, Proposition 5.4, and the
final paragraph of its proof on printed p.16. The registered original is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
Conrad requires the analytic structure on rational points to agree with the
known scheme case. As in the Library's pure-dimensional framework, that
requirement is encoded by the normalization on polynomial affine spaces.
This module contains no proof; the statement is proved as
`smoothSourceDimensionAffineAgreement` in `SmoothSourceDimensionAffineAgreement`.

`SmoothSourceDimensionAffineAgreementStatement` is a proposition definition in
`Langlands.AlgebraicGeometry.AlgebraicSpace`. Let `K` be a nontrivially normed
field with `hK : IsHenselianValuedField K`. Let `σ : AnalyticPointStructure K`
satisfy `σ.IsAdmissible`. This premise is the conjunction of analytic
pure-dimensional manifold structures, analytic functoriality between them,
étale local analytic isomorphisms, and the pure-dimensional affine-space
normalization `σ.AgreesWithAffineSpace`.

The conclusion is `(σ.dimensionStructure hK).AgreesWithAffineSpace`. Here
`σ.dimensionStructure hK` is the `DimensionAnalyticStructure K` whose atlas on
each smooth, quasi-separated, locally separated space is the concrete lifted
atlas `σ.dimensionAtlas hK hX hqs hls`. Unfolding the definition, the
conclusion says the following for every natural number `n`, including `n = 0`.
Let `Aⁿ` be the actual algebraic space of the polynomial affine scheme
`affineSpaceOver K n`, with its proofs `affineSpace_smoothOverBase n`,
`affineSpace_isQuasiSeparated n` and `affineSpace_isLocallySeparated n`.
There is an equivalence `c : RingPoints K Aⁿ K ≃ (Fin n → K)` that agrees
pointwise with the actual polynomial coordinates `affineSpaceCoordinates K n`.
For the original étale-chart topology, `c` and `c.symm` are continuous.
Moreover `c ∘ e.symm` is analytic on `e.target` and `e ∘ c.symm` is analytic
on `c.symm ⁻¹' e.source`, for every dimension `m` and every chart `e` of the
assembled atlas in dimension `m`.

The atlas tested here is not `σ`'s pure-dimensional charted space on `Aⁿ`.
It is the varying-dimension atlas made of lifts of `σ`'s charts on the actual
dimension pieces of `Aⁿ`. So the statement is a genuine transfer.
The intended route of a proof is as follows. Every rational point of `Aⁿ` has
intrinsic dimension `n`, so the lifted charts of other dimensions have empty
sources. The dimension-`n` piece includes into `Aⁿ` by an étale open immersion
that is bijective on rational points. In dimension `n`, `c ∘ e.symm` is the
composite of `σ`'s affine coordinate diffeomorphism with the piece inclusion
and the original chart inverse. Functoriality of `σ` makes this analytic.
The inverse expression uses the analytic inverse of that inclusion, from `σ`'s
étale local analytic isomorphisms.

The field is only assumed henselian, which is what the concrete atlas needs.
No completeness is assumed, because the admissible family is a premise. This
module does not assert the other three admissibility conditions of
`σ.dimensionStructure hK`. Those are the separate assembly,
functoriality and étale statements (`SmoothSourceDimensionAnalyticAssemblyStatement`,
`SmoothSourceDimensionAnalyticFunctorialityStatement` and
`SmoothSourceDimensionEtaleAnalyticIsoStatement`). It also does not assert uniqueness, or
agreement with an analytic structure on arbitrary nonaffine smooth schemes.
