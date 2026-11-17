# Actual Deligne determinant subsheaves

This module constructs the two determinant subsheaves in Deligne's
condition (c) independently, restricts their monomorphic inclusions to the
actual Pi-zero loci, and proves that their equality as categorical
subobjects is equivalent to the existing literal stalk-lattice condition.

The original source is V. G. Drinfeld, *Coverings of p-adic symmetric
regions* (1976), Section 2 A: the final paragraph of printed p.109
(PDF p.3) defines the graded sheaves and the rational frame; the opening
paragraph of printed p.110 (PDF p.4), condition (c), requires

\[
  (\bigwedge\nolimits^d \eta^{\,n\bmod d})|_{S_{n\bmod d}}
  =
  \bigl(\pi^{-n}\bigwedge\nolimits^d(\Pi^n rO^d)\bigr)|_{S_{n\bmod d}}
  \qquad(n\in\mathbf Z).
\]

The registered source is
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
Drinfeld writes the fraction field as \(K\); the Lean parameter is \(F\).
The definitions below are derived sheaf realizations of this formula.
The comparison proofs are internal consequences of the actual exterior
subsheaf, germ, inverse-image and stalk constructions in the imported
modules.

All objects lie in one universe. The auxiliary constructions allow an
arbitrary commutative ring \(O\), an \(O\)-algebra field \(F\), and an
arbitrary topological space. The framed and scheme constructions assume
\(d\ne0\); normalized expressions assume that the image of \(\pi\) in
\(F\) is nonzero. The scheme constructions take the existing
`SheafPreDatum`, including its graded lattice and rational frame.
Neither local freeness of a new determinant sheaf nor injectivity of an
integral-to-rational map is asserted. The construction uses images in the
total rational exterior sheaf and does not establish representability of
the moduli problem.

`LatticePiSheaf.componentDeterminantSubsheaf` uses `exteriorSubsheaf`
on the actual map from the \(i\)-th integral component to total rational
eta. Thus its sections are the locally saturated \(O\)-spans of
exterior products of integral-image sections, as constructed in
`DeligneExteriorSubsheaf`. `componentDeterminantInclusion` is its
monomorphic inclusion in the restriction of scalars of the actual top
exterior rational sheaf. Its stalk-image theorem identifies this
subsheaf with `exteriorStalkLattice` of `componentStalkLattice`, after
the canonical exterior-stalk isomorphism.

`FramedLatticePiSheaf.translatedIntegralFrameSheafMap` starts with the
actual map from the constant sheaf of \(O^d\) induced by the rational
frame and postcomposes it with the actual rational \(\Pi^n\)
automorphism, for any integer \(n\). Its stalk image is proved equal to
`translatedFrameStalkLattice`. Taking `exteriorSubsheaf` gives
`translatedFrameDeterminantSubsheaf`.

`coefficientMultiplicationIso` makes multiplication by any nonzero
coefficient an actual sheaf isomorphism. `determinantScalingIso` applies
this construction to \(\pi^{-n}\) on the rational exterior sheaf.
`normalizedFrameDeterminantInclusion` postcomposes the translated
determinant inclusion with that isomorphism, so it remains monomorphic.
The factor \(\pi^{-n}\) is applied once after taking the exterior power.
Its stalk-image theorem identifies the resulting image with the
previously defined `normalizedFrameDeterminant`.

These image computations use the naturality of `restrictionStalkIso`,
the resulting `imageStalkMap_postcomp`, and
`exteriorSubsheafStalkMap_range`. Coefficient multiplication acts on a
stalk by the same scalar: check it on germs, then commute it past the
\(F\)-linear exterior-stalk isomorphism. The translated-frame computation
also uses compatibility of the actual rational \(\Pi\) automorphism
with every integer power on stalks.

For `SheafPreDatum D`, `componentDeterminantOnPiZeroLocus` and
`normalizedFrameDeterminantOnPiZeroLocus` are actual categorical
`Subobject`s of the same sheaf: the inverse image of the total rational
exterior sheaf along the subspace inclusion
`D.piZeroInclusion (n : ZMod d)`. The two subobjects are made by pulling
back the independently constructed monomorphisms.
`D.DeterminantSubsheavesNormalized hπ` requires their equality for every
integer \(n\).

The proof first establishes `stalkImage_inverseImage` by naturality of
the inverse-image stalk isomorphism. Precomposition with its
isomorphism on the source does not change a linear range.
`subobject_inverseImage_eq_iff` then detects equality of the pulled
subobjects by equality of the original stalk images at the image
points, using `subobject_mk_eq_iff_stalkImage_eq` and injectivity of
transport along the target stalk isomorphism.
`determinantOnPiZeroLocus_eq_iff` transports the two original images
through the same exterior-stalk isomorphism and applies their two
computed range formulas. Finally,
`determinantSubsheavesNormalized_iff` quantifies over all integers and
identifies points of the zero-locus subspace with points satisfying its
membership condition. It proves exactly

```lean
D.DeterminantSubsheavesNormalized hπ ↔ D.DeterminantNormalized hπ
```

No equality between the two determinant subobjects is supplied as input
to either construction.
