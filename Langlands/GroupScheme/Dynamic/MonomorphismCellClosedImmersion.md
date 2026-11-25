# Closedness over the dynamic triple cell

This is an internal consequence of the arbitrary-base unipotent monomorphism
theorem, the cartesian triple-cell theorem, and stability of closed immersion
under products. It asserts no separate external-source translation.

Let \(H,G\) be group schemes over any scheme \(S\), with cocharacter
\(\chi:\mathbf G_{m,S}\to H\) and homomorphism \(f:H\to G\).
Supply representatives of the three actual dynamic functors
\(U_H(-\chi),Z_H(\chi),U_H(\chi)\), and of the corresponding three functors
in \(G\) for \(f\chi\). Products are associated as \(U^-\times(Z\times U^+)\).
The actual map between these products is `Dynamic.tripleCellFactor`,
constructed in `MonomorphismCellPreimage` from subgroup restrictions.

`isClosedImmersion_tripleCellFactor` assumes that the structure morphisms of
\(H,G\) are affine, that \(f\) is monic in schemes over \(S\), and that the
induced map on the supplied centralizer representatives is a closed immersion.
It proves that the triple-cell factor is a closed immersion. Each unipotent
restriction is closed by
`isClosedSubgroup_unipotent_of_represented_overBase`, using the actual
commuting inclusion square. The product of these two maps and the supplied
closed centralizer map is closed. This assertion needs no smoothness or
connectedness hypotheses.

If \(G\) is also smooth over \(S\), the target triple-cell multiplication is an
open immersion. The theorem `isImmersion_tripleCellMultiplication_comp`
then proves that multiplication from the source triple product followed by
\(f\) is a locally closed immersion: its commuting square factors it as the
closed triple-cell factor followed by the target open immersion. It does not
assert that \(f\) itself is an immersion.

For the remaining construction and result assume that \(H,G\) are smooth and
affine over \(S\), that \(H\) has geometrically connected fibres, and that \(f\)
is monic. The definition `tripleCellPullbackIso` is the canonical isomorphism
from the source triple product to the scheme pullback of \(f\) along target
triple-cell multiplication. It is obtained from `isPullback_tripleCellFactor`.
The two theorems `tripleCellPullbackIso_hom_fst` and
`tripleCellPullbackIso_hom_snd` identify its projections with source
multiplication and the actual induced triple-cell factor, respectively.

Under the same closed-centralizer premise as above,
`isClosedImmersion_pullback_tripleCellMultiplication` proves that the
canonical projection from this pullback to the target triple product is a
closed immersion. The second projection identity identifies it, up to the
displayed isomorphism, with the closed triple-cell factor. Thus this is
closedness of the actual inverse image of the target open cell, rather than
closedness of an unrelated map with the same source and target.

All constructions and proofs are universe-polymorphic and valid over arbitrary
base schemes. The closedness of the centralizer restriction is an explicit
premise, not a result of this module. The reductive monomorphism
closed-immersion theorem, `ReductiveMonomorphismClosedImmersionStatement`
(which the Library proves only under further hypotheses), still requires
that premise and the global arguments.
