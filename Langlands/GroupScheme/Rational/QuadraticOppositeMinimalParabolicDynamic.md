# A cocharacter for a quadratic opposite minimal parabolic and its Levi subgroup

The module `Langlands.GroupScheme.Rational.QuadraticOppositeMinimalParabolicDynamic` proves
`IsQuadraticOppositeMinimalParabolicLevi.exists_dynamicData`, the analogue for minimal
parabolic subgroups of `IsQuadraticOppositeBorelTorus.exists_dynamicData` (module
[`QuadraticOppositeTorusCell`](QuadraticOppositeTorusCell.md)).

## Statement

Let `Q/F` be a field extension, `G` a connected reductive group over `F`, and `t : C ⟶ G`
with `IsQuadraticOppositeMinimalParabolicLevi Q t`. Then there are `σ ∈ Aut(Q/F)` with
`σ ≠ 1` and a cocharacter `χ` of `G_Q` such that

- the dynamic centralizer `Z(χ)` is the subgroup functor `range t_Q` of `C_Q`, and
- Galois transport by `σ` carries the dynamic unipotent subgroup `U(χ)` to `U(-χ)`.

## Proof

The predicate supplies `σ ≠ 1`, a minimal parabolic subgroup `j : P ⟶ G_Q`, a rational Levi
subgroup `l : C_Q ⟶ P` with `l ≫ j = t_Q`, and `range j ⊓ range σ(j) = range t_Q`. One
cocharacter `χ` realizes `P = P(χ)` and `C_Q = Z(χ)`
(`DynamicLeviConjugacy.exists_cocharacter_parabolic_levi`, with `parabolicDynamic` and
`dynamicGeometricUnipotentRadical`). The transported cocharacter `χσ` has
`P(χσ) = σ(P)` and `Z(χσ) = Z(χ)`, since `C_Q` is a base change and is therefore
Galois-invariant. So `P(χ) ∩ P(χσ) = Z(χ)`, and the uniqueness of opposite dynamic parabolics
(`oppositeDynamicParabolicUniqueness`) gives `U(χσ) = U(-χ)`; finally `U(χσ)` is the Galois
transport of `U(χ)`.

## Source

This is the step "`σ(P)` is the parabolic subgroup opposite to `P` with respect to `C`" in the
proof of V. Platonov and A. Rapinchuk, *Algebraic Groups and Number Theory* (1994),
Lemma 6.28' (printed p. 383), modelled on the proof of Lemma 6.28 (printed pp. 369–370);
source ID `platonov-rapinchuk-1994-algebraic-groups-number-theory`.
