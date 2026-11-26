# Congruence group schemes of an integral model

Let `M : IntegralModel R K G` be an actual affine flat finite-type group
model over a DVR and let \(\varpi\) be a uniformizer. `M.congruenceModel`
starts with `M` at level zero. At level \(n>0\), it is the single
\(\varpi^n\)-dilatation along the unit subgroup in the actual group
`M.congruenceFibre n` over \(R/\mathfrak m^n\). The centre is a closed
immersion since the affine group scheme is separated and its unit is a
section. `M.congruenceModelHom` is the map to `M` and extends the identity
on the same generic group \(G\).

For an affine flat test, `congruenceTestReduction` is the group homomorphism
on points induced by scheme pullback along the quotient-base morphism.
The fibre of the congruence model over a given point of the original model
contains a unique lift exactly when the quotient pullback of the point is
the unit. This follows from the flat lifting criterion for dilatations,
since the centre is the identity group. The calculation includes
arbitrary flat test algebras and the actual reduction modulo the ideal
\(\mathfrak m^n\) extended to the test algebra.

`range_positiveCongruenceSections` identifies the image in `M.integralSections`
with the existing `M.congruenceKernelAt n`. The corresponding equality in
the given `rationalPoints G` is `integralPoints_congruenceModel`, whose right
side is literally `M.congruenceSubgroupAt n`. The second equality uses the
identity compatibility of the structural map on the generic fibre.

## Source

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Definition
A.5.12, Lemma A.5.13(2) and Remark A.5.14, printed pp. 636–637 (PDF
pp. 667–668). The source defines the congruence group schemes by iteration
and gives the equivalent single dilatation with denominator \(\varpi^n\).
The single construction works with the displayed DVR hypotheses.

Literature ID `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
