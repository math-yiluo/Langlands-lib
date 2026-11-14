# A cocharacter presenting a Borel on a specified residue fibre

This internal construction supplies the initial cocharacter for a neighbourhood
argument in the opposite-Borel proof. It derives its conclusions from the
Library's field-level `regularCocharacterBorel` theorem and split-torus
cocharacter extension; it introduces no additional literature assertion.

Let `S` be any scheme, `G` a reductive group scheme over `S`, and `T` a split
commutative torus over `S`. Let `t : T.toGrp → G` be fibrewise maximal, and
let `i : B → G` be a relative Borel subgroup such that the full subgroup-functor
range of `t` is contained in that of `i`. For every specified point `s` of `S`,
`exists_residueBorelCocharacter` supplies a cocharacter `ν` of this original
torus `T` whose composition with `t`, pulled back to `Spec κ(s)`, satisfies:

- Its dynamic parabolic is exactly the subgroup-functor range of `i_s`.
- Its whole dynamic centralizer is exactly the subgroup-functor range of `t_s`.

Both equalities concern every scheme-valued test over `κ(s)`. They use the
actual pullback and the canonical `Dynamic.baseChangeCocharacter` comparison,
so the centralizer equality can be passed directly to a neighbourhood
criterion for that global cocharacter.

The proof first pulls the range containment to the residue fibre using
`SubgroupFunctor.range_baseChangeHom`. Closedness of the Borel fibre makes
its inclusion a monomorphic representative of its range, and `liftOfLE`
factors the torus inclusion through it. Reductivity supplies connected
reductivity of the ambient residue fibre. Splitness and fibrewise maximality
give a split maximal torus there. The third clause of
`regularCocharacterBorel` then supplies a regular fibre cocharacter presenting
the given Borel. The theorem
`centralizer_comp_eq_range_of_isRegular` identifies its full centralizer.

`IsSplitTorus.extendFieldCocharacter` extends this fibre cocharacter to the
same torus `T` over `S`, with exact equality on pullback. The lattice/dynamic
base-change identity and compatibility with composition transfer both
subgroup-functor equalities to the displayed dynamic pullback form.

`RelativeLevi.BorelResidueCocharacterData` stores an actual global cocharacter
and these two fibre certificates. `residueBorelCocharacter` chooses such data
from the existence theorem. The choices may depend on `s`; no compatibility
between choices at different points is asserted.

No reducedness, connectedness, affine-base, characteristic or Noetherian
hypothesis is imposed. Closedness of `t` need not be a separate premise of
this fibre construction, since fibrewise maximality already supplies the
maximal-torus hypothesis on the selected fibre. The conclusions are on the
specified residue fibre; extending the equalities to a neighbourhood,
constructing an opposite Borel and gluing it remain separate steps.
