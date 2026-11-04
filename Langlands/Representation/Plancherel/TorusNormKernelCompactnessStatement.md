# Compactness of the rational norm kernel of a torus

Author: Worker 723.

This module states one proposition, `TorusNormKernelCompactnessStatement`. It is a
proposition definition only. Nothing is proved here.

## Statement

Fix a nonarchimedean local field `F` of either characteristic. Let `T` be an actual
group scheme over `Spec F` with `IsAffineHom T.X.hom` and
`LocallyOfFiniteType T.X.hom`, and suppose `GroupScheme.IsTorus T`, so that `T` becomes
a split torus after base change to some field extension of `F`. Give the point group
`GroupScheme.rationalPoints T` the canonical topology `rationalPointTopology F T.X`.
The statement says that the existing subgroup
`Langlands.Plancherel.rationalCommonNormKernel T` is a compact subset in that topology.

`rationalCommonNormKernel T` is the intersection of the kernels of
`g ↦ |χ(g)|_F` over all rational characters `χ : T ⟶ Gm` defined over `F`, where
`|·|_F` is the normalized absolute value. In Renard's notation this is `⁰T`.

The two finiteness hypotheses are listed explicitly. The existing affine point topology
needs `IsAffine T.X.left`, and the module derives that from `IsAffineHom T.X.hom` by
`isAffine_of_isAffineHom`, as `SmoothRealStructureStatement` does. Every torus over a
field is affine and of finite type, but deriving that by descent from the split base
change is a separate matter. Keeping both properties as hypotheses makes the statement
weaker, not stronger. Callers with smooth affine groups have them anyway, since
smoothness implies local finite type.

## Source

The registered source is Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026,
`renard-2026-representations-groupes-reductifs-padiques`, SHA-256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

- V.2.3, printed p.105 / PDF p.111: `⁰G` is the intersection of the kernels of
  `|χ|_F` over the rational characters `χ ∈ X*(G)`.
- V.2.5, printed p.107 / PDF p.113, treats tori. It notes that for a split torus `A`,
  `⁰A` is the maximal compact subgroup of `A`.
- V.2.6, Proposition, printed p.108 / PDF p.114, states that `⁰G ∩ Z(G)` is compact
  for every connected reductive `G`. A torus is connected reductive and equals its own
  centre, so that Proposition gives this statement with `G = T`. The proof there
  combines the almost-direct product `T = T_an A`, compactness of the anisotropic
  part, and cocompactness of `T_an A` in `T`.

The statement is derived as the torus case of V.2.6. Renard's proposition is stated for
reductive groups over a fixed local field, and its proof goes through the anisotropic
and split parts. This module asserts only the torus conclusion, for the Library's
`IsTorus` predicate and the Library's actual rational characters and point topology.
It needs no proof of reductivity for tori.

## Role

This is the compactness input for the cocompactness proof of
`CentralDerivedNormKernelCocompactnessStatement` (task `bbd4ee2c`). There, the
quotient `M ⟶ M/𝒟M` by the scheme-theoretic derived subgroup is a torus. It sends the
norm kernel of `M` into the norm kernel of that torus, which this statement makes
compact. The split case is already proved, for commutative group schemes satisfying
`IsSplitTorus`, as `isCompact_commonNormKernel`
(`Representation/Plancherel/SplitTorusCompactKernel`).
The non-split case is the substantive new content.
