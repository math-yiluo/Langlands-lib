# Reductive group schemes at field-valued points and under base change

This internal result connects the Library's geometric-fibre definition of
`IsReductive` with the actual pullback at any field-valued point. It uses the
published proofs of connected reductivity under arbitrary field extension and
its reflection, the algebraically closed comparison with pseudo-reductivity,
and the actual pullback composition isomorphism. It makes no additional
structural assumption on the group or the base scheme. All schemes and fields
lie in the arbitrary common universe `u`.

The actual construction `reductiveFieldFiber f` maps the subtype of reductive
group schemes over `S` to the subtype of connected reductive group schemes
over the supplied field. Its underlying group is definitionally the pullback
along the original `f`, as recorded by `reductiveFieldFiber_val`.
Similarly, `reductiveBaseChange b` maps reductive group schemes over `S` to
reductive group schemes over `S'`, retaining the actual pullback along `b`.
`reductiveBaseChange_val` records this definitional identification. These maps
use the existing subtype convention for group schemes with a supplied
reductivity property. The following lemmas establish their property fields.

`IsReductive.isConnectedReductive_residueFiber` proves connected reductivity of
the actual pullback along `S.fromSpecResidueField s`. The given reductivity
predicate supplies pseudo-reductivity of the geometric fibre at `s`. Its base
field is algebraically closed, so the published comparison makes that geometric
fibre connected reductive. The inverse pullback composition isomorphism
identifies it with the algebraic-closure extension of the residue-field fibre.
Reflection under field extension then gives the conclusion.

`IsReductive.isConnectedReductive_baseChange` treats every supplied morphism
`f : Spec k ⟶ S`, not just those presented as a chosen algebra map. Let `s` be
the image of the unique point of `Spec k`. The actual stalk homomorphism of `f`
induces a field map from `κ(s)` to `k`. Mathlib's residue-field factorization
states that its spectrum map followed by `S.fromSpecResidueField s` is exactly
`f`. The preceding theorem gives connected reductivity over `κ(s)`; the
published arbitrary field-extension proof preserves it over `k`. The pullback
composition isomorphism and the factorization equality identify this result
with the pullback along the original `f`.

`IsReductive.isConnectedReductive_algebraMap` specializes the result to the
actual map `Spec.algebraMap R k` for any commutative ring `R`, any field `k`
and any `Algebra R k`.

`IsReductive.baseChange` proves preservation under every scheme morphism
`b : S' ⟶ S`. Smoothness and affineness are preserved by pullback. At a point
of `S'`, apply the field-valued-point theorem to its geometric point composed
with `b`. The pullback composition isomorphism identifies the result with the
geometric fibre of the changed group. Connected reductivity implies
pseudo-reductivity, supplying the exact fibre clause of `IsReductive`.

These results do not prove that generic connected reductivity spreads to an
open subset. They supply the geometric-fibre-to-field-valued-point step needed
after a reductive family has been obtained.
