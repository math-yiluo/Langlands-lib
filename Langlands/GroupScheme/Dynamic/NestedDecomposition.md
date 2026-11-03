# Nested dynamic decompositions from subgroup inclusions

This internal result works in every universe for a separated group scheme over
an arbitrary base scheme. Every assertion is evaluated on every test scheme,
including nonaffine and nonreduced tests. It uses the existing dynamic subgroup
functors and their actual groups of test points.

`exists_centralizer_mul_unipotent` gives the ordered product `g = m n` for
`g` in `P(χ)`. Take the existing limit `m` and let `n = m⁻¹ g`.
Multiplicativity of limits and uniqueness show that `n` has limit one.

`centralizer_inf_parabolic_decomposition` assumes `Z(χ) ≤ Z(ψ)`. Writing
`H = Z(ψ) ∩ P(χ)` and `V = Z(ψ) ∩ U(χ)`, it proves `V, Z(χ) ≤ H`,
normality of `V` in `H`, the complement assertion ordered as `V, Z(χ)`,
and the literal set product `H = Z(χ) V`. The existing dynamic factorization
of a point of `H` has its centralizer factor in `Z(χ) ≤ Z(ψ)`; taking a
quotient of those two points puts its other factor in `Z(ψ)`. Normality is
inherited from normalization of `U(χ)` by `P(χ)`. The intersection of the
two factors is trivial by uniqueness of the `χ` limit.

`unipotent_eq_centralizer_inf_mul` assumes `P(χ) ≤ P(ψ)` and
`U(ψ) ≤ U(χ)`. Factor a point of `U(χ)` under `ψ`, with its `Z(ψ)` factor
on the left. The second factor lies in `U(ψ) ≤ U(χ)`; multiplication by
its inverse shows that the first factor lies in `U(χ)` as well. This gives
`U(χ) = (Z(ψ) ∩ U(χ)) U(ψ)` as a set equality. The converse uses closure
of the subgroup under multiplication.

`parabolic_eq_centralizer_inf_mul` uses the same calculation in `P(χ)`:
from `P(χ) ≤ P(ψ)` and `U(ψ) ≤ P(χ)`, it proves the all-test product
`P(χ) = (Z(ψ) ∩ P(χ)) U(ψ)`.

`nestedLeviDecomposition_of_inclusions` combines these results into the exact
`SubgroupFunctor.NestedLeviDecomposition` conclusion. It retains all three
inclusions as explicit hypotheses. It establishes neither reverse radical
containment for arbitrary connected reductive groups nor the unconditional
`DynamicNestedParabolicDecompositionStatement`.

`NestedLeviDecompositionFromInclusions` packages this generic implication as
an explicit proposition, universally quantified over separated group schemes
over arbitrary bases. The theorem `nestedLeviDecompositionFromInclusions`
proves that proposition by the preceding assembly.

The provenance is an internal derivation from the published
`Dynamic.LimitMap`, `Dynamic.Decomposition` and `Dynamic.NestedParabolic`
modules. It abstracts the elementary factor calculations already used in
`Rational.StandardLeviIntersectionReduction`; it does not use the standard
cocharacter or parabolic-order statements or claim their proofs.
