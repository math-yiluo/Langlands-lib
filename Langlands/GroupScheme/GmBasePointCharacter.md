# Character values of base points of `𝔾_m`

Module `Langlands.GroupScheme.GmBasePointCharacter`, namespace `Langlands.GroupScheme`.

## Contents

- `gmBasePoint c`: for a field `k` and a unit `c : kˣ`, the point of `𝔾_m` over `Spec k` given
  by `c`, defined through the identification `Gm.affinePointsEquiv` of points of `𝔾_m` with
  units.
- `affinePointsEquiv_constantPoint_gmBasePoint`: over a commutative `k`-algebra `A` in the
  universe of `k`, the point `GroupScheme.constantPoint (gmBasePoint c)` obtained by base change
  is the unit `algebraMap k A c` of `A`.
- `characterValue_powerHom_constantPoint_gmBasePoint`: the value of the character `t ↦ t ^ m`
  (`Gm.powerHom _ m`) at this point is `(algebraMap k A c) ^ m`.

## Proof

The first identity is the naturality of `Gm.affinePointsEquiv` along `k → A`
(`Gm.affinePointsEquiv_naturality`). The second combines it with the Library's value of the
power characters, `SplitExistence.ChevalleyData.ChevGroup.characterValue_powerHom`.
