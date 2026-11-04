# Unipotent splitness from split-torus domination

Author: Worker 1333.

`UnipotentSplitTorusDominationStatement.{u}` is a proposition target. For
every field `k : Type u` and every smooth connected affine actual group
scheme `U` over `k`, it asserts that `IsUnipotent U` together with
`HasPointedSplitTorusDomination U` implies
`RelativeRoot.IsSplitUnipotent U`. The statement retains finite fields,
imperfect fields and every characteristic.

The existing domination predicate supplies an actual finite-rank split
ground-field torus `P` and an actual morphism of relative schemes
`p : P.X ⟶ U.X`. Its underlying scheme map is dominant, and it sends
the identity section of `P` to that of `U`. The map need not be a group
homomorphism. Splitness is required over the original ground field,
not over an extension.

The conclusion is the existing finite-series predicate. It supplies a
finite normal series with actual smooth connected closed terms and
represented fppf quotients that are one-dimensional vector groups over
`k`. A zero-length series means the trivial group. The existing
representation-based `IsUnipotent` predicate is unchanged; comparing it
with the structural unipotent groups in the source is part of a proof,
not an added hypothesis.

The provenance is derived from T. A. Springer, *Linear Algebraic Groups*,
second edition (1998), Theorem 14.3.8(i), printed pp.245–246, one-based
PDF pp.259–260. The registered source is
`springer-1998-linear-algebraic-groups`, SHA256
`44d69662b47d85998f4e65baba1dd1454a3a30e065bcd58342c227d59a73aabf`.
The source assumes a connected solvable group and characterizes its
ground-field splitness by a dominant morphism from a product of affine
space and split multiplicative groups. The present target specializes
the source to unipotent groups, which are solvable, and to a purely
multiplicative source. Its pointedness assumption further restricts the
source hypotheses. For a unipotent group, the resulting split structure
is precisely a finite series with additive one-dimensional quotients.
No rationality-only or rational-point-density criterion is asserted.

The source proof first handles commutative elementary factors by
additive-function modules and then assembles split extensions. That
structural argument is not implemented in this file. In particular,
affine-line constancy, torus-action rigidity and finite-separable
extraction of a dominating torus do not themselves prove this target.
The target does not assert separable descent, existence of a torus
quotient or rational conjugacy of maximal tori.
