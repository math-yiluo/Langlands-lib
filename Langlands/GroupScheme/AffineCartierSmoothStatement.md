# Cartier smoothness for affine algebraic groups in characteristic zero

`Langlands.GroupScheme.AffineCartierSmoothStatement.{u}` states that for every
field `k : Type u` of characteristic zero and every actual group scheme `G`
over `Spec k`, affineness and local finite type of the structure morphism imply
its smoothness. The field need not be algebraically closed. The group need not
be connected, commutative, reduced or smooth in the hypotheses. Since an affine
morphism is quasi-compact, the stated local finite type and affineness give the
usual finite-type affine algebraic group setting.

This is the statement of Cartier's theorem in Milne, *Algebraic Groups* (2017),
Theorem 3.23, printed p. 71 (PDF p. 87). The source's supporting Lemmas 3.19–3.22
are on printed pp. 70–71 (PDF pp. 86–87). Its proof first passes to an
algebraically closed field and shows that nilpotents in the coordinate algebra
belong to the square of the augmentation ideal, then compares tangent spaces
with the reduced subgroup. This paragraph describes the source's proof;
this module only defines the proposition and contains no proof of it.

The registered official errata snapshot dated 2026-11-02 was checked. Its
Chapter 3 corrections concern 3.52 and a stabilizer notation on p. 85; neither
changes Theorem 3.23 or these supporting lemmas.

The intended normal-quotient application uses the resulting reducedness to
apply the existing exact normal-kernel construction in characteristic zero.
This statement introduces no extra premise into the arbitrary-characteristic
quotient-existence target and does not assert that target.
