# Orbits along the opposite cocharacter

Author: Worker 919.

Module `Langlands.GroupScheme.Dynamic.GmOrbitInversion`, namespace
`Langlands.GroupScheme.GmOrbitInversion`. This is an internal supporting unit for Task 7586,
with no literature source. Inversion of `𝔾ₘ` is written as
`(CommGroupScheme.groupHom (Gm.powerHom S (-1))).hom.hom`. This is the convention of the
Library's `Dynamic.oppositeCocharacter` and `Dynamic.orbit_oppositeCocharacter`.

## Statements

Let `S` be a scheme and `X : Over S`.

- `groupHom_powerHom_neg_one`:
  `(CommGroupScheme.groupHom (Gm.powerHom S (-1))).hom.hom = ι[(Gm S).X]`. The power map
  `t ↦ t⁻¹` is the group-object inverse.
- For `T : CommGroupScheme S`, `comp_groupHom_neg (x : U ⟶ (Gm S).X) (ν : cocharacterLattice T)`:
  `x ≫ (groupHom (-ν)).hom.hom = (x ≫ (groupHom (Gm.powerHom S (-1))).hom.hom) ≫
  (groupHom ν).hom.hom`.
- `gmOrbit_neg (b : SchemeAction T.toGrp X) (ν) (w : Z ⟶ X)`:
  `(b.restrict (groupHom (-ν))).gmOrbit w =
  Z ◁ (groupHom (Gm.powerHom S (-1))).hom.hom ≫ (b.restrict (groupHom ν)).gmOrbit w`.
- `gmOrbit_oppositeCocharacter (b : SchemeAction H X) (χ : (Gm S).toGrp ⟶ H) (w : Z ⟶ X)`,
  for any group scheme `H`:
  `(b.restrict (Dynamic.oppositeCocharacter χ)).gmOrbit w =
  Z ◁ (groupHom (Gm.powerHom S (-1))).hom.hom ≫ (b.restrict χ).gmOrbit w`.

So the `𝔾ₘ`-orbit map along the opposite cocharacter is the orbit map along the cocharacter,
precomposed with inversion on the `𝔾ₘ` factor.

## The implemented proofs

- `groupHom_powerHom_neg_one`: write the morphism as `𝟙 ≫ (groupHom ((-1) • 𝟙)).hom.hom`
  (`Gm.powerHom_apply`). By `Gm.comp_zsmul_id` this is `(𝟙)⁻¹`, which is `ι` by
  `GrpObj.inv_eq_inv`.
- `comp_groupHom_neg`: `-ν = (-1) • ν`. By `comp_groupHom_zsmul` the value at `x` is
  `(x ≫ groupHom ν)⁻¹`. This equals `x⁻¹ ≫ groupHom ν` (`GrpObj.inv_comp`), and
  `x⁻¹ = x ≫ ι` holds by definition.
- `gmOrbit_neg` and `gmOrbit_oppositeCocharacter`: unfold `gmOrbit` and `restrict_act`. Move
  `Z ◁ _` inside with `naturality`, `whiskerLeft_fst` and `whiskerLeft_snd`. Then use
  `comp_groupHom_neg`, respectively the definition
  `oppositeCocharacter χ = groupHom (Gm.powerHom S (-1)) ≫ χ`.
