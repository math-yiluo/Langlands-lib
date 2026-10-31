# Inner cuspidal support through an actual induction quotient

Author: Worker 125.

This internal adapter uses the Library's actual normalized refined Jacquet
quotients. It does not prove the cuspidal-induction constituent statement or
the persistence statement.

`flattenedUpperJacquetMap` and `flattenedOppositeJacquetMap` restrict the
existing normalized Jacquet intertwiners along the actual constructed
`flattenedLeviEquiv`. Their underlying linear maps are unchanged. Each
`_mk` formula sends the class of a vector to the class of its image under
the supplied coarse-Levi intertwiner. If that original map is surjective,
the descended map is surjective: choose a representative of a target class
and lift that representative through the original map. This elementary
right-exactness argument needs no smoothness or finite-length hypothesis.

The two `isSubquotient_of_quotient` lemmas compose the resulting surjection
with an actual subquotient, using
`WeylBranchPieces.IsSubquotient.of_surjective_left`. That published lemma
takes the actual inverse image of the invariant subspace and composes its
surjective quotient map. Thus the proof retains actual subquotient data.

`exists_transport_of_quotient_of_constituent` applies this opposite
inheritance to an actual quotient of inner normalized induction. It then
applies the existing proposition
`GLCuspidalInductionJacquetConstituentStatement`, which is an explicit
premise of this conditional adapter and remains separately unproved.
The conclusion retains exactly the permutation in `blockWeyl B`, its
conjugacy witness and its intertwining equivalence supplied by that
constituent statement. The coarse quotient need not be irreducible.
Source, quotient, constituent and field universes are independent.

The fine-twist specialization first uses the published irreducibility and
Levi-cuspidality invariance in `FineTwistRegularityProof` for the parameter
`-v`. Pointwise evaluation of the fine parameter at zero identifies the
task's actual inducing datum with the pullback of this twisted
representation. It then applies the preceding quotient adapter, for
arbitrary real `v`.

The internal mathematical provenance is elementary functoriality and
transitivity of actual subquotients, together with direct application of
the imported Library target. The target remains an explicit premise:
this module supplies neither its proof nor a geometric-lemma filtration.
