# Bounded actions on a spanning set

This internal linear-algebra prerequisite is derived from the published
`Langlands.LinearAlgebra.charpoly_coeff_vle_one_of_bounded_powers` theorem in
`BoundedMatrixPowers` and the span-induction argument already used by
`Langlands.exists_valuative_bound_trace_of_mem_span` in `ValuativeTraceBound`.
It is not a new formulation of a literature theorem.

`Langlands.LinearAlgebra.BoundedSpanningActionStatement.{u,v}` says that, over
a nonarchimedean local field `F : Type u`, a matrix indexed by any finite type
`n : Type v` has integral characteristic coefficients if its action on column
vectors preserves a coordinate-bounded spanning set `S`. Here spanning means
`Submodule.span F S = ⊤`. Coordinate boundedness means that, for each coordinate
`i`, there is a nonzero `b : F` such that `x i ≤ᵥ b` for every `x ∈ S`.
Preservation means `Set.MapsTo A.mulVec S S`; the matrix need not be invertible
or map `S` onto itself. The conclusion is `A.charpoly.coeff d ≤ᵥ 1` for every
natural number `d`. The theorem `boundedSpanningAction` proves this proposition
at the two independent universes.

The implementation first proves
`exists_valuative_bound_linearMap_of_mem_span`. For an arbitrary indexed family
of scalar-valued linear maps, a bound uniform over the family at each point of
`S` extends to each vector in its span. Span induction handles addition by
choosing the larger of two bounds in the total valuative relation; scalar
multiplication multiplies a bound by the scalar, treating the zero scalar
separately. Every chosen bound remains nonzero.

`exists_common_valuative_bound` combines finitely many nonzero bounds.
`exists_valuative_bound_entries_of_mapsTo_spanning` applies the span lemma to
the coordinate forms of an arbitrary family of matrices, each preserving `S`.
Testing at the standard basis vector with coordinate `j` equal to one bounds
the matrix entry in row `i`, column `j`, uniformly over the family. Combining
the finitely many entry bounds gives one nonzero bound for all matrices and
entries. These three lemmas require only a field and a valuative relation;
they make no local-field or topological assumption.

`exists_valuative_bound_powers_of_mapsTo_spanning` shows by induction that all
nonnegative powers preserve `S`, and applies the preceding family result.
Finally, the published bounded-powers theorem converts that common entry
bound into integrality of every characteristic coefficient over the local
field.

This helper supplies only the linear-algebra step toward boundedness of
normalizers. Constructing a suitable bounded spanning set and comparing its
action with an algebraic-group representation remain separate obligations.
