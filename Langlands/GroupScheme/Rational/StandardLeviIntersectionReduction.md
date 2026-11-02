# Nested standard Levi intersections from standard cocharacters and the parabolic order

Worker 778. This module reduces the published `StandardLeviIntersectionStatement` to two
other published statements, `StandardCocharacterStatement` and
`StandardParabolicOrderStatement`. It proves neither of them. Its final theorem takes both as
explicit hypotheses, so it does not prove `StandardLeviIntersectionStatement` without
them. Provenance is internal: the arguments are formal consequences of the dynamic
decomposition `P(χ) = U(χ) ⋊ Z(χ)` in `Langlands.GroupScheme.Dynamic.LimitMap` and
`Langlands.GroupScheme.Dynamic.Decomposition`, applied to standard cocharacters.

## Setting

Throughout, `k` is a field, `G` is a group scheme over `Spec k` whose structure morphism is
affine, `i : T → G` is a homomorphism from a commutative group scheme `T`, and `ν` is a
cocharacter of `T`. No splitness, maximality or reductivity of `G` or `T` is assumed in the
per-test-scheme lemmas. For a set `J` of characters, the published subgroup functors
`P_J = standardParabolic i ν J`, `L_J = standardLevi i ν J` and
`U_J = standardUnipotent i ν J` are the intersections, over all standard cocharacters `ζ`
for `J` (`IsStandardCocharacter i ν J ζ`), of the dynamic parabolic, centralizer and
unipotent subgroup functors of the cocharacter `χ_ζ = ζ ≫ i` of `G`. Write
`P(ζ)`, `Z(ζ)` and `U(ζ)` for these dynamic subgroup functors.

## The predicate

`StandardLeviIntersection.IsRealizingStandardCocharacter i ν J ζ` says that `ζ` is a
standard cocharacter for `J` with `Z(ζ) ≤ L_J` and `U(ζ) ≤ U_J`. Since `L_J` and `U_J` are
intersections over all standard cocharacters, the reverse inclusions `L_J ≤ Z(ζ)` and
`U_J ≤ U(ζ)` hold for every standard `ζ`
(`standardLevi_le_dynamicCentralizer`, `standardUnipotent_le_dynamicUnipotent`). So the
predicate says that `ζ` realizes `L_J = Z(ζ)` and `U_J = U(ζ)`. The predicate says
nothing about `P_J`.

## Lemmas on a test scheme `Q`

- `conj_mem_standardUnipotent`: for any `J`, if `p ∈ P_J(Q)` and `v ∈ U_J(Q)`, then
  `p v p⁻¹ ∈ U_J(Q)`. For each standard `ζ` for `J`, `p ∈ P(ζ)(Q)` and `v ∈ U(ζ)(Q)`, and
  `Dynamic.conj_mem_unipotent` gives `p v p⁻¹ ∈ U(ζ)(Q)`. No standard cocharacter needs to
  exist.
- `eq_one_of_mem_standardLevi_of_mem_standardUnipotent`: if `J` has a standard
  cocharacter `ζ`, a point of `L_J(Q) ∩ U_J(Q)` lies in `Z(ζ)(Q) ∩ U(ζ)(Q)`, so it is `1`
  by `Dynamic.eq_one_of_mem_centralizer_of_mem_unipotent`. The uniqueness of limits that
  this lemma requires is `HasLimit.unique`, which holds because an affine morphism is
  separated.
- `exists_standardUnipotent_mul_standardLevi`: if `ζ` realizes `L_J` and `U_J`, every
  `g ∈ P_J(Q)` is `v l` with `v ∈ U_J(Q)` and `l ∈ L_J(Q)`. Since `g ∈ P(ζ)(Q)`, take
  `l = Dynamic.limit g ∈ Z(ζ)(Q) ≤ L_J(Q)` (`limit_mem_centralizer`) and
  `v = g l⁻¹ ∈ U(ζ)(Q) ≤ U_J(Q)` (`mul_inv_limit_mem_unipotent`).

## The two parts of the target, on a test scheme `Q`

`leviInterParabolic_decomposition` assumes that `ζ` realizes `L_J` and `U_J` and that
`L_J ≤ L_K`. With `H = (L_K ⊓ P_J)(Q)`, `V = (L_K ⊓ U_J)(Q)` and `L = L_J(Q)`, it proves the
four clauses of the first part of the target:

1. `V ≤ H`, because `U_J ≤ P_J` (`standardUnipotent_le_standardParabolic`).
2. `L ≤ H`, because `L_J ≤ L_K` and `L_J ≤ P_J` (`standardLevi_le_standardParabolic`).
3. `V` is normal in `H`. For `h ∈ H` and `v ∈ V`, `h v h⁻¹ ∈ L_K(Q)` because `L_K(Q)` is a
   subgroup, and `h v h⁻¹ ∈ U_J(Q)` by `conj_mem_standardUnipotent` since `h ∈ P_J(Q)`.
4. `V` and `L` are complements in `H`, by `Subgroup.isComplement'_of_disjoint_and_mul_eq_univ`.
   They intersect trivially by `eq_one_of_mem_standardLevi_of_mem_standardUnipotent`. For
   `x ∈ H`, write `x = v l` with `v ∈ U_J(Q)` and `l ∈ L_J(Q)` by
   `exists_standardUnipotent_mul_standardLevi`. Then `l ∈ L_K(Q)`, so `v = x l⁻¹ ∈ L_K(Q)`
   and `v ∈ V`.

`standardUnipotent_eq_leviInter_mul` assumes that `ζ` realizes `L_K` and `U_K` and that
`P_J ≤ P_K` and `U_K ≤ U_J`. It proves the set equality
`U_J(Q) = (L_K(Q) ∩ U_J(Q)) · U_K(Q)`.

- Inclusion `⊆`: let `u ∈ U_J(Q)`. Then `u ∈ P_J(Q) ≤ P_K(Q)`, so
  `exists_standardUnipotent_mul_standardLevi` for `K` gives `u = w l` with `w ∈ U_K(Q)` and
  `l ∈ L_K(Q)`. Since `l⁻¹ ∈ P_K(Q)`, `conj_mem_standardUnipotent` gives
  `l⁻¹ w l ∈ U_K(Q)`. Then `l = u (l⁻¹ w l)⁻¹`, and `U_K ≤ U_J` gives `l ∈ U_J(Q)`. So
  `u = l (l⁻¹ w l)` with `l ∈ L_K(Q) ∩ U_J(Q)` and `l⁻¹ w l ∈ U_K(Q)`.
- Inclusion `⊇`: a product `a b` with `a ∈ U_J(Q)` and `b ∈ U_K(Q) ≤ U_J(Q)` lies in the
  subgroup `U_J(Q)`.

## The reduction theorem

`standardLeviIntersectionStatement_of_standardCocharacter_of_standardParabolicOrder`
proves `StandardLeviIntersectionStatement.{u}` from `StandardCocharacterStatement.{u}` and
`StandardParabolicOrderStatement.{u}`. Fix the data of the target, with
`J ⊆ K ⊆ simpleRelativeRoots i ν`. `StandardCocharacterStatement` gives standard
cocharacters `ζ_J` for `J` and `ζ_K` for `K`, together with `L_J = Z(ζ_J)`,
`U_J = U(ζ_J)`, `L_K = Z(ζ_K)` and `U_K = U(ζ_K)`. So `ζ_J` realizes `L_J` and `U_J`, and
`ζ_K` realizes `L_K` and `U_K`. `StandardParabolicOrderStatement` gives `P_J ≤ P_K` from
`J ⊆ K`, and also `L_J ≤ L_K` and `U_K ≤ U_J`. The first part of the target is
`leviInterParabolic_decomposition` on every test scheme. The second part is
`standardUnipotent_eq_leviInter_mul` at the test scheme `Spec k` over itself, whose points
are the rational points `standardUnipotentPoints` and `standardLeviPoints`.

## Scope

The parabolic equalities `P_J = P(ζ)` from `StandardCocharacterStatement` are not used.
Together, the two premises contain everything this reduction needs from root theory: the
existence of standard cocharacters, the dynamic comparisons, and the inclusions between
standard subgroups for nested index sets. Proving `StandardLeviIntersectionStatement`
outright still requires proofs of both premises.
