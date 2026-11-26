# Affine dilatation and quotient-base lifting

Let \(X\) be an affine scheme over \(\operatorname{Spec} R\) and let \(Y\) be a
closed subscheme of the pullback of \(X\) to \(\operatorname{Spec}(R/J)\).
`centreIdeal` is the kernel of the coordinate homomorphism of the composite
\(Y\to X_{R/J}\to X\). `affineDilatation r j` is the relative spectrum of
\(A[I/r]\), where \(A\) is the relative coordinate algebra returned by
`algΓ` and \(I\) is this kernel. `affineDilatationHom` uses the coordinate
inclusion and the canonical affine comparison to map to the actual \(X\).
If \(R\) is a Dedekind domain and \(X\) is flat and of finite type, the
constructed scheme is affine, flat and of finite type over \(R\).

Suppose \(R\) is a domain and \(J=(r)\) with \(r\ne 0\).
`affineDilatation_lift_iff` states that a map from an affine flat test \(T\)
into \(X\) lifts uniquely through the dilatation map exactly when its pullback
along \(\operatorname{Spec}(R/J)\to\operatorname{Spec} R\) factors through
\(Y\). The coordinate comparison `quotientTestIso` identifies the reduction
of \(T\) with the quotient by the extended ideal \(J\). Because the centre
map is a closed immersion of affine schemes, its coordinate map is
surjective, and factorization is equivalent to sending its kernel to zero in
the quotient. This is the divisibility condition used by `liftBlowup`.
`affineDilatationHom_injective` gives cancellation for every affine flat
test. It only uses the nonzero denominator.

For a flat affine \(X\) over a Dedekind domain, the pullback of the
dilatation map to the specified fraction field is an isomorphism. To construct
the inverse, regard the affine generic fibre of \(X\) as a test over \(R\).
Its coordinates invert \(r\), so the universal property lifts its projection.
Adjunction gives a right inverse on the generic fibre. The corresponding
flat test on the dilatation gives cancellation, hence a two-sided inverse.

## Source

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Definition
A.5.1, Construction A.5.2, Proposition A.5.3 and Fact A.5.5, printed
pp. 632–633 (PDF pp. 663–664), and Remark A.5.14, printed p. 637 (PDF
p. 668). The source works over a Henselian DVR and uses a uniformizer
for the special fibre. The domain and Dedekind-domain hypotheses above
are sufficient for the stated affine comparisons. The quotient-base
formulation also covers the powers of a uniformizer in Remark A.5.14.

Literature ID `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
