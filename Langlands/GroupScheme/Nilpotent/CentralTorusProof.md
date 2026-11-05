# A central maximal torus with unipotent quotient: proof

Authors: Worker 1331; underlying published proof by Worker 1487.

`nilpotentCentralTorusStatement.{u}` proves exactly the published proposition
`Langlands.GroupScheme.NilpotentCentralTorusStatement.{u}`. Its proof term is
`nilpotentCentralTorus.{u}`, imported from `Nilpotent.NoTorusUnipotent`.
This module supplies a focused proof entry point for that existing deduction.
It introduces no additional mathematical hypothesis and changes neither the
published statement nor its imports.

For every field `k : Type u` and every smooth connected affine group scheme
`G` over `Spec k` with `IsNilpotentGroupScheme G`, the conclusion gives an
actual commutative group scheme `T`, an inclusion `i : T.toGrp → G`, an
actual affine unipotent group scheme `Q`, and a projection `q : G → Q`.
The inclusion is a central maximal torus. The projection satisfies
`RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q`: it is flat,
scheme-surjective and locally of finite presentation, and its actual
scheme-theoretic kernel represents the all-test range of `i`.

The imported proof first applies
`IsNilpotentGroupScheme.centralTorusQuotient`. Maximal-torus existence over
the original field supplies `T` and `i`; the nilpotent torus-centrality
argument makes `i` central. The actual normal-subgroup quotient theorem
then constructs a smooth connected affine quotient and its fppf projection.
Nilpotence passes to its geometric point group through surjective lifting
over the algebraic closure. The central-maximal-torus quotient theorem
shows that every homomorphism from a base-field torus to this quotient has
trivial all-test range.

The remaining assertion, unipotence of this particular quotient, follows
from `IsNilpotentGroupScheme.isUnipotent_of_no_torus`. It passes to the
algebraic closure, where geometric nilpotence implies solvability. Every
geometric cocharacter is central and therefore factors through the full
scheme-theoretic center. Commutative cocharacter descent and the absence
of base-field torus maps make this factor zero. The algebraically closed
solvable character criterion proves geometric unipotence, and the field
reflection theorem descends it. The center need not be smooth.

The connection to the exact geometric nilpotence predicate is implemented
in the imported proofs. A nilpotence bound for the algebraic-closure point
group gives a uniform all-test lower-central bound for the smooth connected
affine group. This implies nilpotence of every adjoint difference. A
nonzero split-torus weight is incompatible with that nilpotence; thus the
Lie algebra is fixed by the torus. Diagonalizable-action rigidity gives
all-test centrality, which descends from a splitting field for arbitrary
tori. This argument does not assume a structural comparison as an axiom.

These are internal deductions from the published nilpotent, commutative
cocharacter-descent, character and quotient constructions. The source
comparison for the target is recorded in `CentralTorusStatement.md`; this
proof uses the existing Library route described above. It uses neither the
general `NoTorusUnipotentStatement` nor maximal-torus base-change
preservation derived from that statement. The intermediate nilpotent
no-torus criterion is proved by the independent cocharacter argument.
The universe is arbitrary; the field may be finite or imperfect and may
have any characteristic.
