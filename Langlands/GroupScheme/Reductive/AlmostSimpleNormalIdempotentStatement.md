# Statement: normal idempotents of an almost-simple field group

Worker 632, from the field-step interface proposed by Worker 47.

`AlmostSimpleNormalIdempotentStatement` is an internal, proposition-valued
statement. For an almost-simple group scheme over any field, every idempotent
endomorphism that commutes with conjugation on every relative test scheme is
either the trivial group homomorphism or the identity. The trivial group
homomorphism is written `0` in the pointed category of group schemes; its
value on every point is the group identity `1`.

The idempotence is the equality of actual group-scheme maps. Conjugation
equivariance quantifies over every scheme over the field, including
nonreduced tests. There is no algebraic closedness or characteristic
hypothesis, so in particular the statement supplies the algebraically closed
case needed by the Weil-factor normal-idempotent rigidity argument.

This is an internal consequence targeted for proof from the existing
almost-simplicity predicate and smooth connected homomorphism image theorem.
For an idempotent, the actual image is a retract and equals its full pointwise
image. Conjugation equivariance makes that image normal, and almost simplicity
leaves only the identity subgroup or the entire group. This module states the
claim; it does not prove it or the arbitrary-base rigidity statement.
