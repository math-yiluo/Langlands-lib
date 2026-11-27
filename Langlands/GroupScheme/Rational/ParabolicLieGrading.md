# The tangent grading of a rational parabolic

The module `Langlands.GroupScheme.Rational.ParabolicLieGrading` proves the algebraic form of the
grading of the Lie algebra of a connected reductive group by a parabolic subgroup, over a field
`k` of characteristic zero.

## Main result

- `exists_parabolicLieGrading`: let `G` be connected reductive over `k`, `q : Q → G` a parabolic
  subgroup, `iV : V → Q` its geometric unipotent radical and `l : M → Q` a rational Levi subgroup.
  Then there is `H₀` in the Lie algebra `𝔤 = Additive (lieKernel G k)` such that
  1. the eigenvectors of `ad H₀` with integer eigenvalues span `𝔤` over `k`;
  2. the tangent map of `l ≫ q` is injective;
  3. a vector `Y` lies in the image of the tangent map of `l ≫ q` if and only if `⁅H₀, Y⁆ = 0`;
  4. the image of the tangent map of `iV ≫ q` is the span of the eigenvectors of `ad H₀` with
     eigenvalues `n + 1`, `n` a natural number.

## Proof

By `parabolicDynamic`, `q` represents the dynamic parabolic `P(χ)` of a cocharacter `χ`. The
Library's `IsRationalLeviSubgroup.exists_centralCocharacter_of_dynamicParabolic` provides a
cocharacter `ψ` of `M` whose composite `ψ ≫ l ≫ q` has the same dynamic parabolic and whose
centralizer is the Levi (`centralizer_eq_of_dynamicParabolic`), while
`Dynamic.range_comp_radical_eq_unipotent_of_reductive` identifies the radical with the dynamic
unipotent group `U(ψ ≫ l ≫ q)`. Take `H₀ = dψ'(1)` for `ψ' = ψ ≫ l ≫ q`
(`cocharacterLieVector`). The Library's `dynamicRingLie` describes the tangent spaces of the
dynamic centralizer and unipotent group as the weight-zero part and the sum of the positive weight
spaces. The Library's `Lie.mem_range_targetMapLinear_iff` (module
`Langlands.GroupScheme.Dynamic.RingWeightLift`) turns these into statements about the images of
the tangent maps: if a closed subgroup `j : H → G` represents a subgroup functor `F`, a tangent
vector of `G` lies in the image of the tangent map of `j` exactly when its dual-number point lies
in `F`. With `mem_weightSpace_powerHom_iff` (weight spaces are eigenspaces of `ad H₀`) and
`iSup_weightSpace_powerHom_eq_top` (weight spaces span), these become statements 1, 3 and 4;
statement 2 holds because closed subgroups are monomorphisms, so their tangent maps are
injective.

## Sources

A. Borel, *Linear Algebraic Groups*, 2nd ed., §IV.11 and §V.20 (parabolic subgroups, Levi
decompositions and the description `P(λ)`, `U(λ)`, `Z(λ)` by a cocharacter); the dynamic
description follows B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, §2.1.
