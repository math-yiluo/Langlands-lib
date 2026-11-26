# Addition of congruence levels

For positive levels \(m,n\) and every flat affine test, a point of the
level-\(m\) model reduces to the identity at level \(n\) exactly when its
image in the original model reduces to the identity at level \(m+n\).
`congruenceTestReduction_add` uses the actual quotient pullbacks of both
models. On affine tests equality after pullback means agreement of all
coordinates modulo the extended base ideal.

For the coordinate proof, let \(I\) be the level-\(m\) centre ideal in
\(A\). It contains the kernel of the augmentation since the centre is the
unit over the quotient base. A difference of evaluations at \(a\in A\)
can be computed at \(a-\epsilon(a)\in I\). In the blow-up algebra the
latter is \(\varpi^m\) times the divided generator. Thus agreement on the
blow-up algebra modulo \(\varpi^n\) gives agreement on the original
algebra modulo \(\varpi^{m+n}\). Conversely, flatness of the test allows
cancellation of \(\varpi^m\) and gives agreement on the divided generators.
Agreement on the original algebra and the divided generators gives
agreement on the entire blow-up algebra by induction on the adjoin.

The composite of the level maps represents the level-\(m+n\) kernel on
flat affine tests. For existence of the two successive lifts, reduction
at level \(m+n\) implies reduction at level \(m\), and the addition law
then gives the level-\(n\) reduction on the lift. Uniqueness gives the
compatible model isomorphism `positiveCongruenceModelAddIso`. Its generic
map is the identity of the supplied generic group, as follows from the two
structural model squares. The first model is the residue identity-centre
dilatation, by the equalities \(\mathfrak m^1=\mathfrak m\) and
\(\varpi^1=\varpi\).

`congruenceSubgroupAt_positiveCongruenceModel` gives the addition identity
in the existing congruence subgroups of the supplied generic group.
`integralPoints_congruenceModel_add` gives the equality for all nonnegative
levels, with the original model at zero.

## Source

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Definition
A.5.12, Lemma A.5.13(2)–(3), and Remark A.5.14, printed pp. 636–637
(PDF pp. 667–668). The source assumes a Henselian DVR. The point argument
uses the DVR and flatness hypotheses. The model isomorphism follows from
unique representation of the flat-test kernel used in A.5.1 and A.5.3.

Literature ID `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
