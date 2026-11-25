# Actual Cartan-to-Iwasawa weight comparison

This module states
`Langlands.HarishChandraSchwartz.RationalCartanIwasawaWeightComparisonStatement.{u}`.
It does not prove this comparison.

Let `F` be a nonarchimedean local field and `G` a connected reductive affine
group locally of finite type over `F`. Let `i : S → G` be a maximal split torus
and `ν` a generic cocharacter. Let `K0` be any compact subgroup, `F0` any finite
set of points in the torus centralizer, and `K` a compact open subgroup with
`G(F) = P0(F) K` for the minimal standard parabolic `P0` determined by `ν`.
The statement asks for a positive constant `C` such that

```
φK(ϖ^y) ≤ C φK(g)
```

for every cocharacter `y` whose pairings with all simple relative roots are
nonnegative and every `g` in the actual Cartan cell
`⋃_{f∈F0} K0 ϖ^y f K0`. Here `ϖ^y` is the actual uniformizer evaluation
`Aubert.General.uniformizerPowers i (.ofAdd y)` and
`φK = iwasawaWeight hPK (rationalMinimalModulus i ν)`.
The constant is uniform in `y` and every point of these cells; it may depend
on all the preceding field, group, compact and finite data. The statement
assumes neither a Cartan covering nor a simultaneous standard basis.
No representation or Xi estimate is assumed.

This is a derived form of Waldspurger's Lemma II.3.2, printed p.255, adapted
to the Library's actual Cartan cells and arbitrary compact Iwasawa factor.
On `P0(F)` the weight is the square root of the actual minimal-parabolic
modulus. Thus its square is the source's modulus comparison. Waldspurger's
proof uses the determinant eigenline of a representation, its inverse
chamber operator bound and uniform operator bounds on compact factors.
Absorbing the finite centralizer factors into a compact set gives the
version stated here. Arbitrary compact factors, including those in the
Iwasawa decomposition, are bounded in that same argument. These adaptations
are internal derived content rather than a separate numbered assertion in
the source. The proposition is proved as `rationalCartanIwasawaWeightComparison` in
`RationalCartanIwasawaWeightComparisonProof`.

Source: J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques,
d'après Harish-Chandra* (2003), literature ID `waldspurger-2003-plancherel`,
SHA256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
Relevant passages are II.2, printed pp.253–254, and II.3.2 and its proof,
printed p.255.
