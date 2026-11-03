# Normal closed subgroups as representation kernels

`Langlands.GroupScheme.MatrixRepresentation.NormalKernelStatement.{u}` states
that every normal closed subgroup of an affine group scheme of finite type
over an arbitrary field is the kernel of a finite-dimensional representation.
This file defines a proposition; it does not prove it.

The field `k : Type u` is unrestricted. The ambient actual group scheme `G`
is locally of finite type and affine over `Spec k`, so is of finite type.
The subgroup is an actual homomorphism `i : H ⟶ G` whose scheme map is a
closed immersion. Its range is normal on every relative scheme test.
There is no smoothness, reducedness, connectedness, perfectness or
characteristic assumption.

The conclusion supplies a natural number `n` and an actual homomorphism
`ρ : G ⟶ GL (Fin n)`. The equality of subgroup functors says that a point
over every scheme over `Spec k` belongs to the kernel of `ρ` exactly when
it factors through `i`. It therefore specifies the scheme-theoretic kernel,
including infinitesimal structure, rather than only field-valued points.
The integer `n` may be zero.

The source is J. S. Milne, *Algebraic Groups* (2017), Corollary 5.19,
printed p.103 (PDF p.119), following Proposition 5.18. The source first
constructs an affine quotient by a normal subgroup and then embeds it in a
general linear group; the resulting kernel assertion is the one recorded
here. Equality of the represented subgroup functors is the chosen Lean
expression of that assertion. The official author errata snapshot registered
as `milne-2017-algebraic-groups-errata-2026-11-02` has no correction to
Proposition 5.18 or Corollary 5.19.
