# Faithful unipotent matrix actions and finite normal subgroups

This internal development supports the common-kernel step of KP Lemma 2.2.11
(printed pp.72–73, PDF pp.103–104, *Bruhat–Tits theory: a new approach*, 2023).

`HasUnipotentPointMatrices` requires nilpotent deviation from identity on
every relative scheme test. The exponent can depend on the test and point.
Restriction preserves it, and the canonical global-sections comparison
transports it to the actual rational matrices.

A matrix that is diagonalizable over a reduced commutative ring and whose
deviation from identity is nilpotent is identity: conjugation transports the
nilpotent power to the diagonal, and reducedness makes every diagonal
deviation zero. Over an algebraically closed field, the actual diagonalization
of a split-torus representation gives this conclusion at every rational
point. The reduced-source, separated-target rational-point equality criterion
then proves the actual representation trivial.

Finite Galois splitting of tori extends the triviality assertion to every
torus over an algebraically closed field. A faithful unipotent matrix action
therefore excludes nontrivial closed tori in its source: its restriction to
each torus is trivial, and faithfulness cancels the representation. For a
smooth connected affine source, the published infinite-field no-torus
unipotence theorem consequently proves unipotence.

`isFinite_of_normal_of_unipotentPointMatrices` applies this to the reduced
identity core of a closed normal subgroup of a smooth affine group with
trivial unipotent radical. The core is smooth, connected and normal. A closed
faithful representation restricts to a faithful representation of the core,
so the preceding theorem makes it unipotent. The ambient radical condition
makes its inclusion trivial. Its topological range is open, so the identity
of the full subgroup is an open singleton. The published finite-type affine
group finiteness criterion then proves the full subgroup scheme finite,
including any nilpotent structure.

The field is algebraically closed and the ambient representation is explicitly
closed and faithful in this finite-subgroup result. Normality and triviality
of the unipotent radical remain explicit hypotheses. This is a supporting
structural argument; it does not yet identify or bound the simple-factor map.
