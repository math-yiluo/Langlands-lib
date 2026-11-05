# Invariant integration for reductive groups in characteristic zero

`CharacteristicZeroReductiveInvariantIntegralStatement.{u}` says that every
connected reductive affine group scheme `H` over every characteristic-zero field
`k : Type u` admits a normalized invariant linear functional on its actual
coordinate algebra `CoordinateIntegration.Coord H`.

The conclusion is `Nonempty (CoordinateIntegration.InvariantIntegral H)`. Its
linear functional has value one at the constant function one. For every
commutative `k`-algebra `A : Type u`, its `A`-linear extension to
`A ⊗[k] Coord H` is invariant under pullback by left translation by every actual
`A`-point of `H`. This includes nonreduced coefficient algebras. The explicit
affineness instance supplies the coordinate presentation; it is also a field of
`IsConnectedReductive H`. There is no algebraic-closure restriction on `k` and no
change of base field in the conclusion.

This is a derived statement, rather than a verbatim theorem from the source.
Milne, *Algebraic Groups*, corrected 2022 reprint, Definition 12.52 and Remark
12.53(a), printed p.248 (PDF p.259), define linear reductivity and extend
semisimplicity to arbitrary rational representations. The Reynolds-operator
paragraph on printed p.249 (PDF p.260) supplies the equivariant projection onto
invariants. Theorem 22.42(a) implies (b), printed pp.478–479 (PDF pp.489–490),
gives linear reductivity for connected reductive groups in characteristic zero.
Applying the Reynolds projection to the regular representation on `k[H]`, whose
invariant functions are the constants, gives the stated functional. Equivariance
in the group-scheme representation and scalar extension give the asserted
all-coefficient-algebra invariance. The Lean statement packages this consequence;
it does not implement that construction or assert a proof of its existence.

The retained original is registered as `milne-2022-algebraic-groups`, source
SHA256 `f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`,
at `/home/taskhub/pilot/literature/J. S. Milne - Algebraic Groups- The Theory of Group Schemes of Finite Type over a Field (2022 corrected reprint).pdf`.
The author's retained 2022-reprint errata were read. Their correction to the
proof of 22.42, printed p.478, specifies that the initial `V_i` are the
eigenspaces for the centre `Z`; it does not change the theorem's conclusion.

The coordinate-integral interface is internal Library support derived from the
actual affine-coordinate presentation and the earlier split-torus averaging
construction. This proposition isolates the substantial reductive-existence
input required by vector-extension defect averaging. It assumes neither a Levi
decomposition nor the characteristic-zero vector-extension splitting statement.
