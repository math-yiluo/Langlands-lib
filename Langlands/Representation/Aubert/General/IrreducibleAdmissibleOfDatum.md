# Jacquet's theorem for `G(F)` from Jacquet–Cartan data

Module `Langlands.Representation.Aubert.General.IrreducibleAdmissibleOfDatum`.
Author: Worker 276 (task `173e44ba-079b-4597-a13b-1aab371a4ec9`).

The module proves one conditional theorem. It reduces the published target
[`RationalPointsIrreducibleAdmissibleStatement`](IrreducibleAdmissibleStatement.md)
(Jacquet's theorem, Renard VI.2.2) to the structural proposition
[`RationalPointsJacquetCartanDatumStatement`](JacquetCartanDatumStatement.md).
The structural proposition is a hypothesis of the theorem. It is not proved here.

## Main result

```
theorem Langlands.Aubert.General.rationalPointsIrreducibleAdmissible_of_jacquetCartanDatum
    (h : RationalPointsJacquetCartanDatumStatement.{u}) :
    RationalPointsIrreducibleAdmissibleStatement.{u, uV}
```

If the rational points of every connected reductive group over every
nonarchimedean local field `F : Type u` carry a Jacquet–Cartan datum (for the
pinned point topology), then every irreducible smooth complex representation
of every such `G(F)`, with carrier in any universe `uV`, is admissible. Both
propositions use the same binders and the same pinned topology
`rationalPointTopology F G.X`.

## Proof

Fix `F`, `G` and `hG : IsConnectedReductive G`. The proof installs the same
local instances as the two statements: `IsAffineHom G.X.hom` from
`hG.isAffineHom`, `IsAffine G.X.left` by `isAffine_of_isAffineHom`, and the
topology `rationalPointTopology F G.X`. It then uses:

1. `Smooth G.X.hom` from `hG.smooth`. This gives the finite-type instance that
   the next two lemmas need.
2. `rationalPoint_isTopologicalGroup F G` (published
   `AlgebraicGeometry.PointTopology.RationalPointGroups`): `G(F)` is a
   topological group for the pinned topology.
3. The hypothesis `h F G hG`, which gives a datum
   `𝒟 : JacquetCartanDatum.{u, u} (RationalPoint F G.X)`.
4. `Langlands.BruhatTits.rationalPoint_exists_compactOpenSubgroup F G`
   (published `BruhatTits.Unipotent.RationalPointCompactOpen`): `G(F)` has a
   compact open subgroup, by van Dantzig's theorem for the locally profinite
   group `G(F)`.
5. `Langlands.SmoothRep.isAdmissible_of_jacquetCartanDatum 𝒟 hK₀ A hA`
   (published
   [`Smooth.Admissibility.JacquetCartan`](../../Smooth/Admissibility/JacquetCartan.md)):
   for a topological group with a compact open subgroup and a Jacquet–Cartan
   datum, every irreducible object `A` of `SmoothRep.{0, u, uV} ℂ G(F)` is
   admissible.

Step 5 applied to an arbitrary `A` with `A.IsIrreducible` is exactly the inner
clause of the target.

## Status

Combined with a proof of `RationalPointsJacquetCartanDatumStatement`, this
theorem proves the target. The structural proposition is still open: it needs
the Iwasawa and Cartan decompositions of standard Levi subgroups of `G(F)` and
the contraction of their walls (see
[`JacquetCartanDatumStatement.md`](JacquetCartanDatumStatement.md)).
