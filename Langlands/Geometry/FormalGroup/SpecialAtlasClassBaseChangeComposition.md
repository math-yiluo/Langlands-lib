# Composition of coefficient maps on actual special-atlas classes

Successive coefficient extensions induce the same map on actual special-atlas
comparison classes as the structural composite. This also holds for classes
inside the subtype carrying actual height d² certificates.

## Source and scope

This is internal derived infrastructure for Drinfeld, *Coverings of p-adic
symmetric regions* (1976), printed p.109 (PDF page 3), the paragraph before
section 2 and section 2 A. The former allows formal groups glued over
localizations; the latter uses isomorphism classes of special formal
order-modules with height d². Registered source:
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The composition laws below are derived from the actual formal atlas comparison,
rather than attributed as a separate theorem to that passage.

The parameters are a nonarchimedean local field K, a finite-dimensional central
division K-algebra D, a supplied K-embedding iota of a field L in D, and a
commutative O_K-algebra R. Input special atlases have their supplied full-degree
unramified integer-subfield and geometric tangent-character certificates, and
coordinates `Fin d` for `d = CentralSimple.reducedDegree K D`. Covers may be
infinite. The extensions are arbitrary `S : CommAlgCat.{v} R` and
`T : CommAlgCat.{v} S`; the direct extension uses T with its structural
R-algebra structure, `BasicAtlas.restrictTest S T`. No flatness or injectivity is
assumed. Structural composite O_K-algebra instances associate definitionally.

## Actual formal comparison and descent

`SpecialAtlas.baseCompComparison X S T` starts with the actual full-order
formal isomorphism `X.order.baseCompIso S T`. It restricts both formal maps to
the reflexive principal refinement of the successive atlas and its retargeting
to the direct atlas. The resulting `Comparison` therefore supplies actual
refinements, equal refined covers, both order-linear formal maps and their
formal inverse equations. It uses the original chart transitions between
potentially different successive and direct source choices. It is not a
comparison supplied as a hypothesis or chosen from an equality of classes.

`SpecialAtlas.classOf_baseChange_comp` applies the established class-equality
criterion to this comparison. `SpecialAtlas.IsoClass.baseChange_comp` proves

    baseChange (baseChange q S) T = baseChange q (restrictTest S T)

by quotient induction. For each actual representative the required equality is
exactly the class equality just constructed; there is no chosen representative
in the resulting coefficient map.

`HeightSquaredAtlas.classOf_baseChange_comp` uses the same underlying actual
comparison between the two extended special atlases. Both inputs already
carry their own height certificates, obtained by successive or direct
coefficient extension. Those certificates include irreducibility of pi,
nilpotence of its actual image in the base, and actual chart scalar-kernel
height d². Equality of certificates is unnecessary: the certified quotient's
relation is existence of actual formal comparison of the underlying atlases.
`HeightSquaredAtlas.IsoClass.baseChange_comp` then applies quotient induction
inside that subtype. No height is inferred for an arbitrary equivalent atlas.

These are two-step class composition laws. Identity comparisons, coefficient
maps between independently supplied O_K-algebra structures, a varying-base
moduli functor, framing, Drinfeld triples, polarizations and representability
remain separate obligations. No invariant 1/d classification or existence of
the supplied integer subfield is asserted.
