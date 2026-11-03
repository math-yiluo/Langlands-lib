# Actual Borel existence by prime-kernel height

Worker 135.

This internal construction proves existence of an actual Borel embedding into
any affine group scheme locally of finite type over a field, in arbitrary
characteristic and universe. Here Borel means exactly the published
`IsBorelSubgroup`: maximal among smooth connected solvable closed subgroups
defined over the field. No geometric maximality or conjugacy over a nonclosed
field is asserted. Over an algebraically closed field the result supplies the
existence part of Milne, *Algebraic Groups* (2017), Theorem 17.9, printed pp.353–354.
The construction does not prove the conjugacy part of the task's exact target.

`IsAdmissible` collects the four conditions before maximality. The actual
terminal group scheme gives one such subgroup: its structural morphism is the
identity, its underlying space is the spectrum of a field, and the unit
inclusion is a closed immersion because it is a section with one-point source.
Base change preserves the terminal object, so its geometric point group is
trivial and hence solvable.

For each admissible embedding the actual coordinate kernel in the noetherian
ambient coordinate ring is prime and has finite height, by
`BorelExistenceCoordinates`. The proof chooses the least natural number that
occurs as such a height, and an embedding with that height. Every admissible
overgroup has at least this height; reverse containment of coordinate kernels
and prime-height rigidity then force the factor map to be an actual
isomorphism of group schemes. These are precisely all five fields of the
published `IsBorelSubgroup` structure.

`exists_minimal_height_admissible` retains the global height comparison against
every admissible subgroup, without requiring a containment. The theorem
`exists_isBorelSubgroup_minimal_height` additionally proves maximality.
`BorelData` records the actual subgroup, embedding, Borel proof and global
height comparison; `borelData` chooses such data. A comparison of dimensions
or a proper quotient would require further arguments and is not asserted here.
The construction uses classical choice, without selecting a canonical subgroup. The finite-height argument replaces Milne's maximal
dimension argument; it is derived internal content using published integrality,
ideal-sheaf and commutative algebra results. Milne's official errata were read,
and no correction to Theorem 17.9 was found.
