# Central torus semisimple quotients from geometric solvable radicals

This internal derived reduction combines the actual represented radical,
quotient, centre, and field-reflection interfaces. It retains three structural
prerequisites as explicit assumptions and does not assert the unconditional
central-torus theorem by itself.

Over an algebraically closed field,
`HasTrivialSolvableRadical.hasFiniteCenter` constructs the full centre of an
affine group locally of finite type. Every smooth connected closed central
subgroup is commutative because its inclusion is monic; hence it is solvable
and normal. Triviality of the solvable radical kills its full range. The
finite-centre helper then proves that the original centre representative is
finite, including its nilpotents.

`IsGeometricSolvableRadical.isSemisimple_quotient` assumes that `G` is a
smooth connected affine group scheme over an arbitrary field `k`, that
`r : R ⟶ G` is an actual geometric solvable radical, that `Q` is affine,
and that `q : G ⟶ Q` satisfies the full
`RelativeRoot.IsFppfQuotient (SubgroupFunctor.range r) q` predicate.
Under these hypotheses the quotient helper proves that `Q` is connected
reductive over `k` and has trivial solvable radical after base change to
the algebraic closure.
The preceding finite-centre argument applies there, giving semisimplicity
of that base change. The published field-reflection theorem descends
semisimplicity to the original field. The kernel remains the full represented
kernel on all tests throughout the argument.

The final reduction assumes ground-field solvable radical existence, the
algebraically closed normal-solvable-central-torus theorem, and arbitrary
field-extension compatibility of largest central subtori. For every connected
reductive ambient group scheme `G` over an arbitrary field `k`, the existing
geometric radical reduction constructs a geometric solvable radical from
these inputs. Over the algebraic closure its source is a central torus by
the second input. Torus structure and centrality descend to the original
field. Its unchanged underlying group scheme, equipped with commutativity,
is the required actual central torus. Its inclusion is closed, and its
structure morphism is affine and locally of finite type. The quotient
semisimplicity theorem applies to every quotient in the target.

The source field is arbitrary. No perfectness, characteristic, or splitting
hypothesis is introduced. The reduction explains the remaining proof
obligations through its three explicit structural assumptions; it does not
replace their proofs or complete the unconditional host task.
