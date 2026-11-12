# An actual opposite parabolic for a represented parabolic

Author: Worker 70. Module
`Langlands.Representation.Families.InducedTwistsDetectionOpposite`, namespace
`Langlands.Renard.AlgebraicFamily.InducedTwistsDetection`. Internal helper for the
uniform induced-twist detector.

## Statement

`exists_opposite_parabolic`: let `G` be a connected reductive group over a field `k`,
`p : P ⟶ G` an actual parabolic subgroup and `l : M ⟶ P` a rational Levi subgroup. Then
there are group schemes `P̄`, `N̄`, maps `pbar : P̄ ⟶ G`, `mbar : M ⟶ P̄`, `nbar : N̄ ⟶ P̄`
and a cocharacter `χ : 𝔾_m ⟶ G` with the following properties:

- `pbar` is parabolic, `mbar` is a rational Levi subgroup, `nbar` is a geometric unipotent
  radical, and `subgroupMultiplication mbar nbar` is an isomorphism;
- `mbar ≫ pbar = l ≫ p`, and `P(k) ∩ P̄(k) = M(k)` as subgroups of `G(k)`
  (`pointImage p ⊓ pointImage pbar = pointImage (l ≫ p)`);
- the range of `pbar` is the dynamic parabolic `P(χ)`, the range of `l ≫ p` is the
  dynamic centralizer `Z(χ)`, and the range of `nbar ≫ pbar` is the dynamic unipotent
  subgroup `U(χ)`.

These are exactly the opposite-parabolic hypotheses of the published
`LeviSecondAdjointnessStatement`, together with a dynamic description of `P̄` that gives
Iwahori contractions.

## Proof

The proved `parabolicDynamic` and `dynamicGeometricUnipotentRadical` give, through
`DynamicLeviConjugacy.exists_cocharacter_parabolic_levi`, a cocharacter `χ₀` with
`range p = P(χ₀)` and `range (l ≫ p) = Z(χ₀)`. Set `χ = χ₀⁻¹`
(`Dynamic.inverseCocharacter`), so that `Z(χ) = Z(χ₀)`. `P̄` is the affine
representing scheme `Dynamic.Affine.parabolicHom χ`. `mbar` and `nbar` are the
factorizations of `l ≫ p` and `Dynamic.Affine.unipotentHom χ` through it. The following
proved results then apply:
- `dynamicGeometricUnipotentRadical` together with `unipotentFieldExtensionStatement`
  shows that `nbar` is a geometric unipotent radical;
- `Dynamic.isIso_subgroupMultiplication` shows that the multiplication map is an
  isomorphism;
- `Dynamic.Affine.isParabolicSubgroup_parabolicHom_of_parabolicDynamic` shows that `pbar`
  is parabolic.

The intersection of rational points is `Dynamic.parabolic_inf_opposite_eq_centralizer`
evaluated at the identity test scheme.
