# Local Borel normalizer conjugacy from geometric lifting

This derived reduction proves part (2) of the split Borel local-conjugacy target
conditional on the published `SplitNormalizerGeometricLocalLiftingStatement`.
It does not prove that lifting statement. Lie-containment spreading is discharged
by the published theorem `relativeParabolicLieContainment`.

For two relative Borel subgroups `i` and `j` of a reductive group scheme over an
arbitrary scheme `S`, containing the same closed fibrewise maximal relative torus
`t : T → G`, the theorem
`IsRelativeBorelSubgroup.exists_fieldPoint_normalizer_conjugacy` produces an
actual point over any supplied algebraically closed field point of `S`. It lies
in the full subgroup-functor normalizer of the torus and conjugates the two
Borel ranges after every refinement of that field point. The proof pulls back
the Borels and torus, uses their published field-point transport and maximality,
and applies the published geometric normalizer-transitivity theorem. Canonical
point equivalences return its normalization and conjugacy to the original base.

`relativeBorel_exists_open_normalizer_conjugacy_of_geometric_lifting` fixes a
point `s` of `S` and assumes local lifting modulo the torus for every normalizer
point over `geometricPoint S s`. The assumed lift consists of an open `V`, a
specified factorization `a` of that geometric point through `V`, and a normalizer
section `nV` such that `(a ≫ nV) * n⁻¹` lies in the actual torus range. The theorem
produces an open `U` containing `s` and a rational point of the actual pullback
`G_U`. That point belongs to the full normalizer of the actual pulled-back torus
and makes the actual conjugated source range equal to the target range over `U`.
`relativeBorelLocalNormalizerConjugacyOfGeometricLifting` chooses both this open
and this rational point with all three properties.

The proof first chooses the geometric normalizer conjugator by the field-point
result. Its assumed lift differs on the left by a torus point, hence by a target
Borel point. The published target-correction helper preserves conjugacy with
that multiplication order. The local-section spreading construction then
shrinks `V` to an open of the original `S`, using the published Lie-containment
proof. The geometric point maps to `s`, so that open contains `s`. The canonical
point and all-test conjugacy equivalences turn the resulting section into the
claimed rational pullback point, normalizer membership and equality of ranges.

`splitBorel_exists_open_normalizer_conjugacy_of_lifting` specializes this
construction to the exact affine split reductive data in
`SplitBorelZariskiLocalConjugacyStatement`: every commutative ring, a closed
coordinate split torus maximal on all residue fibres, its fibrewise root datum,
and root weight spaces free of rank one. The supplied
`SplitNormalizerGeometricLocalLiftingStatement` gives the geometric lifting
premise at each `s`. The coordinate split torus is a relative torus, so the
general theorem yields exactly the target's second conclusion. No connected,
local, Noetherian or reduced base hypothesis is added. The first conclusion of
the target is outside this reduction. This is a composition of published
mathematics and the conditional spreading helpers, with no additional
original-source assertion.
