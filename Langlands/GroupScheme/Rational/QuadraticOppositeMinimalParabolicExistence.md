# Existence of a quadratic opposite minimal parabolic and its Levi subgroup

The module `Langlands.GroupScheme.Rational.QuadraticOppositeMinimalParabolicExistence` proves
Platonov–Rapinchuk, Lemma 6.17', for the class of minimal parabolic subgroups, in the form of
the predicate `IsQuadraticOppositeMinimalParabolicLevi` of
[`NumberFieldQuadraticOppositeMinimalParabolicLevi`](NumberFieldQuadraticOppositeMinimalParabolicLevi.md).

## Declarations

- `isClosedSubgroup_radicalGaloisHom`, `isParabolicSubgroup_radicalGaloisHom` and
  `isMinimalParabolicSubgroup_radicalGaloisHom`: for a field extension `Q/F`, a group `G` over
  `F` with `G_Q` connected reductive, and `σ ∈ Aut(Q/F)`, the Galois translate
  `radicalGaloisHom j σ` of a closed (resp. parabolic, resp. minimal parabolic) subgroup
  `j : P ⟶ G_Q` is again closed (resp. parabolic, resp. minimal parabolic).
- `exists_quadraticOppositeMinimalParabolicLevi_of_intersection`: for `Q/F` quadratic Galois,
  `σ ≠ 1`, `G` over `F` with affine structure morphism, a minimal parabolic subgroup
  `j : P ⟶ G_Q` and a rational Levi subgroup `l : L ⟶ P` with
  `range j ⊓ range (radicalGaloisHom j σ) = range (l ≫ j)` (all test schemes), there is a
  closed subgroup `t : C ⟶ G` over `F` with `IsQuadraticOppositeMinimalParabolicLevi Q t`.
- `exists_quadraticOppositeMinimalParabolicLevi`: for an infinite field `F`, a quadratic
  Galois extension `Q/F` and a connected reductive group `G` over `F`, there is a closed
  subgroup `t : C ⟶ G` over `F` with `IsQuadraticOppositeMinimalParabolicLevi Q t`.

## Proofs

*Galois translates.* A parabolic subgroup of `G_Q` is the dynamic parabolic `P(χ)` of a
cocharacter (`parabolicDynamic`); its Galois translate is the dynamic parabolic of the
transported cocharacter and is a closed subgroup, hence parabolic. Minimality follows because
Galois transport of subgroup functors is monotone and transport by `σ⁻¹` inverts transport by
`σ`.

*Descent.* As in `exists_quadraticOppositeBorelTorus_of_intersection`, the intersection
`P ∩ σ(P)` is invariant under `Gal(Q/F)` because `σ² = 1`, and
`IsClosedSubgroup.exists_descent_of_galois_range_eq` descends the closed subgroup `l ≫ j` to a
closed subgroup `t : C ⟶ G` over `F` with an isomorphism `e : C_Q ≅ L` and
`t_Q = e ≫ l ≫ j`. The Levi subgroup of the predicate is `e ≫ l`, a rational Levi subgroup
because precomposition with an isomorphism preserves this property.

*Existence.* The proof follows `exists_quadraticOppositeBorelTorus` with a minimal parabolic
subgroup in place of a Borel subgroup. Take a maximal split torus `S` of `G_Q`
(`exists_maximalSplitTorus`) and a generic cocharacter `ν` of `S`
(`IsSplitTorus.exists_genericCocharacter`); `-ν` is generic as well. With `χ = ν`, the dynamic
parabolics `P(χ)` and `P(-χ)` are minimal parabolic (`genericMinimalParabolic`), and the
dynamic centralizer `Z(χ)` is a rational Levi subgroup of `P(χ)`
(`dynamicCentralizerReductive`, `Dynamic.isGeometricUnipotentRadical_of_centralizer`,
`Dynamic.isRationalLeviSubgroup_of_geometricUnipotentRadical`). The Galois translate
`σ(P(χ))` is minimal parabolic, so a rational point `w` conjugates it to `P(-χ)`
(`minimalParabolicConjugacy`). The open cell `U(χ) · P(-χ)` (`oppositeCellStatement`),
translated by `w`, is a nonempty open set, and density of the twisted Galois values
(`galoisTwistedPointDensity_of_isGalois`) gives `g ∈ G(Q)` with
`g⁻¹ σ(g) = q · q' · w`, `q ∈ U(χ)(Q)`, `q' ∈ P(-χ)(Q)`. For `P = g P(χ) g⁻¹`,
`σ(P) = g q P(-χ) (g q)⁻¹`, and since `q ∈ P(χ)`,
`P ∩ σ(P) = g q (P(χ) ∩ P(-χ)) (g q)⁻¹ = g q Z(χ) (g q)⁻¹`
(`Dynamic.parabolic_inf_opposite_eq_centralizer`). This conjugate of `Z(χ)` is the image of
the rational Levi subgroup `Z(χ) ⟶ P(χ)` followed by inner conjugation by `q` in `P(χ)`
(`innerIso_hom_comp`, `innerIso_mul_hom`), and the descent step concludes.

## Source

V. Platonov and A. Rapinchuk, *Algebraic Groups and Number Theory* (Academic Press, 1994),
source ID `platonov-rapinchuk-1994-algebraic-groups-number-theory`, Lemma 6.17' (printed
p. 383), whose proof is said there to be analogous to that of Lemma 6.17 (printed
pp. 329–330) with the open cell of Borel–Tits, §5, in place of the Bruhat cell. The class of
minimal parabolic subgroups is reflexive: `P(χ)` and its opposite `P(-χ)` are both minimal
parabolic, and all minimal parabolic subgroups of `G_Q` are conjugate under `G(Q)`. The
theorem here assumes `G` connected reductive and `F` infinite; perfectness is not needed.
