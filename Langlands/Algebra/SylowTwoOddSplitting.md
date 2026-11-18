# Odd-degree splitting from a cube scalar coboundary

This internal derived supporting unit proves three theorems. Throughout,
`L/k` is a finite Galois extension of fields in one universe.

`Langlands.CentralSimple.sylowTwo_fixedField_odd_degree`: for an actual Sylow
two-subgroup `P` of `L ≃ₐ[k] L`, its fixed field has odd degree over `k`. The
proof identifies that degree with the index of the fixing subgroup, identifies
the latter with `P`, and uses that the index of a Sylow two-subgroup is not
divisible by two.

`Langlands.CentralSimple.exists_odd_degree_splitting_of_scalarDefect_cube`:
let `A` be a finite-dimensional `k`-algebra and
`e : L ⊗[k] A ≃ₐ[L] Matrix (Fin n) (Fin n) L` an actual chart with `n ≠ 0`.
If the cube of the chart's actual scalar defect is a coboundary, then some
intermediate field `F` of odd degree over `k` actually splits `A`: there is an
algebra equivalence `F ⊗[k] A ≃ₐ[F] Matrix (Fin n) (Fin n) F`. The proof takes
`F` to be the fixed field of a Sylow two-subgroup `P`. The order of `P` is a
power of two and hence coprime to three, so the fixed-field descent theorem
`split_over_fixedField_of_coprime_scalarDefect_power` from
`FixedFieldScalarDefect` gives the splitting.

`Langlands.CentralSimple.division_degree_six_scalarDefect_cube_not_coboundary`:
let `D` be a finite-dimensional division `k`-algebra with
`Module.finrank k D = 36`. For every actual chart
`e : L ⊗[k] D ≃ₐ[L] Matrix (Fin n) (Fin n) L` with `n ≠ 0`, the cube of its
actual scalar defect is not a coboundary. Otherwise the previous theorem gives
an actual splitting over an odd-degree field, which
`division_degree_six_not_split_over_odd_extension` from
`DivisionSplittingDegree` excludes. No centrality premise on `D` is needed once
the chart is supplied.

The route specializes the Sylow fixed-field argument of Gille and Szamuely,
*Central Simple Algebras and Galois Cohomology* (2006), Lemma 4.5.14 and the
proof of Proposition 4.5.13(2), printed pages 104–105 (PDF pages 118–119 of
the registered source), to the prime two and a class killed by three. The
class is represented here by the cube coboundary of an actual chart's scalar
defect. The implementation uses the actual scalar cochains and matrix
splitting comparisons of the supporting modules; it does not assume the
source's Brauer group or its general index–period theorem.
