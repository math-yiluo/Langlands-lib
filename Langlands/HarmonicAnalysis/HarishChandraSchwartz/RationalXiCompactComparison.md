# Compact comparison of actual spherical functions

The module
`Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiCompactComparison`
specializes the derived compact comparison to the actual rational points of a
connected reductive group and to its actual standard Levi subgroups. The
proposition `RationalXiCompactComparisonStatement.{u}` is proved by
`rationalXiCompactComparison`, at arbitrary universe `u`.

Let `F` be a nonarchimedean local field, `G` a connected reductive affine group of
finite type over `F`, `i : S → G` a maximal split torus, `ν` generic, and `J` a
subset of the simple relative roots. For compact open subgroups `K,L` satisfying
the minimal Iwasawa decompositions of `G(F)` and `M_J(F)`, there are positive real
constants `C_G,C_M`, independent of the point, with

```
Ξ_K(g) ≤ C_G Ξ_L(g),
Ξ_K^{M_J}(m) ≤ C_M Ξ_L^{M_J}(m).
```

Interchanging `K,L` gives the reverse comparisons. The two helper theorems state
these comparisons separately: the ambient theorem only needs the ambient
Iwasawa decompositions, and the Levi theorem only needs the Levi decompositions.
There is no Cartan covering, basis, height, or analytic estimate among their
premises.

This is derived content, used to reconcile the compact subgroup defining the
spherical functions with the structural compact subgroup in Proposition II.4.5.
Its starting constructions are Waldspurger's compact quotient integral (I.1,
printed p.240), induced invariant pairing (I.3, printed p.243) and spherical
coefficient (II.1, printed p.250). It is not a separately numbered claim of that
source.

The implemented proof identifies `rationalMinimalModulus` with the modular
character of the actual minimal parabolic, using the published parabolic
modulus theorem with the empty finite root index. Reductive unimodularity,
closedness of the minimal parabolic and second countability of the rational
points then verify every premise of `exists_xi_le_mul_xi`. For the Levi
comparison, it applies the ambient theorem to `Standard.leviScheme i ν J`.
Published results establish that this scheme is connected reductive and of
finite type with the required maximal split torus and generic cocharacter.
`leviSchemeCompact` carries the compact, open and Iwasawa properties of
`K ∩ M_J(F)` and `L ∩ M_J(F)` to that scheme. Finally,
`rationalXi_leviScheme` transports the two inequalities back along
`leviSchemePointsEquiv`. The two constants may differ.

Source: J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques,
d'après Harish-Chandra* (2003), literature ID `waldspurger-2003-plancherel`,
SHA256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
The intrinsic Levi interpretation agrees with I.1, printed p.240, where the
properties of `M ∩ K` are specified. The source provides the constructions;
the uniform comparison is derived by the imported general comparison theorem.
