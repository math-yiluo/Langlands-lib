# Compactness of the full scheme-center point quotient by a split component

Authors: Worker 1232 and Worker 1567.

`Langlands.GroupScheme.centerSplitComponentCompactness` proves exactly the
published `Langlands.GroupScheme.CenterSplitComponentCompactnessStatement.{u}`
for an arbitrary universe `u`. For every nonarchimedean local field `F` in
either characteristic, every actual connected reductive group scheme `M`,
and every actual split component `i : A.toGrp → M`, the full scheme-center
point quotient `CentralPointQuotient i hi.isCentralSplitTorus.isCentral` is
compact in the explicitly selected `centralPointQuotientTopology`.
The numerator retains the full center on all test schemes, and the
denominator is the actual image of `A(F)`.

## Implemented proof

The proof supplies all three inputs of the published
`centerSplitComponentCompactnessAlgebraicReduction`.

First, the published `maximalTorusCentralizer` proves maximal-torus
self-centralization over every field. Restricting its field quantifier to
algebraically closed fields supplies
`AlgClosedMaximalTorusCentralizerStatement`. Applying
`centerMultiplicativeTypeCentralizerReduction` gives
`CenterMultiplicativeTypeStatement` over every field. That reduction passes
the actual full center to the algebraic closure, factors it as a closed
subgroup of a split maximal torus, and uses the diagonalizable
closed-subgroup presentation. Its character group may have torsion, so
the center's nonsmooth and disconnected factors are retained.

Second, `normalSubgroupQuotientExistence` proves unrestricted affine
normal-subgroup quotient existence. Its
`toAffineNormalSubgroupQuotientStatement` adapter only changes the binder
style and the order of the geometric conclusions. The actual fppf
projection and its all-test scheme-kernel equality are preserved.
This quotient theorem applies to the full center without a smoothness
hypothesis.

Third, `multiplicativeTypeSplitQuotientAnisotropy` proves that the quotient
of a multiplicative-type group by a maximal split subtorus has a closed
anisotropic torus with an actual finite schematic fppf quotient. This
supplies the remaining structural input without a characteristic
restriction.

The imported algebraic reduction then represents the full center by
`z : Z → M`, factors the given `i` through it, and forms the actual
quotient `q : Z → C`. The split-torus kernel gives open sections on
canonical rational points. The structural input supplies
`HasAnisotropicTorusFiniteQuotient C`, whose published compactness theorem
combines anisotropic-torus compactness with the finite attained point
image. It retains the finite schematic quotient, including nonreduced
data. The reduction finally uses
`centralPointQuotientModelHomeomorph` to transport compactness of `C(F)`
to the literal point quotient. This homeomorphism uses the actual
kernel/image comparison and the split-torus open sections, and selects
exactly the inherited center topology and quotient topology in the target.

## Provenance

This is an internal composition of the published proofs and reduction
modules imported by the Lean file. Its only new proof term discharges
the three existing algebraic premises as described above. The source
locators and conventions for the target remain in
[CenterSplitComponentCompactnessStatement.md](CenterSplitComponentCompactnessStatement.md);
the composed construction is explained in
[CenterSplitComponentCompactnessAlgebraicReduction.md](CenterSplitComponentCompactnessAlgebraicReduction.md).
Worker 1567 coauthored the structural and finite-extension components of
that construction.
