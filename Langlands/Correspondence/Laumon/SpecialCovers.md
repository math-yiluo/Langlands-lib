# Special covers of the punctured line

Katz (1986), (1.3.1), p. 74: for a field `K` of characteristic exponent `p`, a finite étale
covering `E → 𝔾_{m,K}` is *special* if it is tame at zero and its geometric monodromy group has a
unique `p`-Sylow subgroup. The class of finite groups with a unique `p`-Sylow subgroup is stable
under subgroups, quotients, finite products and extensions of prime-to-`p` groups by such groups.
Lemma (1.3.2), pp. 74–75, shows that specialness is geometric and is equivalent to the
following: after a prime-to-`p` Kummer pullback `[N]` and a finite constant extension, the
covering extends to `𝔸¹` with `p`-group monodromy. (1.3.3), pp. 75–76, shows that special coverings
form a Galois subcategory, classified by a quotient `π₁(𝔾_{m,K})(special)`. Main Theorem (1.4.1),
p. 76, says that the inverse image functor from special finite étale coverings of
`𝔾_{m,K} = Spec K[T, T⁻¹]` to finite étale coverings of `Spec K((T⁻¹))`, the punctured formal
neighbourhood of `∞`, is an equivalence of categories. Its proof, pp. 77–79, reduces by descent
along `μ_N(K') ⋊ Gal(K'/K)` to Proposition (1.4.2) of
`Langlands.Correspondence.Laumon.ProPCoverComparison`.

In Katz the local end is `∞` and specialness asks for tameness at `0`. Here the end is a
parameter `e : FourierEnd` and specialness asks for tameness at `e.opposite`. At `e = ∞` (or `∞'`)
this is Katz's convention, and at `e = 0` (or `0'`) it is the one of Laumon (2.2.2), p. 156,
whose local trait is at `0` and whose sheaves are tame at `∞`.

## Definitions

- `gmGeometricMonodromyGroup k t E` is the geometric monodromy group of the finite étale cover
  `E` of `𝔾_m` at the geometric point `t` (Katz (1.2.2)): the image of the geometric fundamental
  group `gmGeometricSubgroup k t` of `Langlands.Correspondence.Laumon.TameCovers` in the
  permutations of the fibre of `E` at `t`.
- `specialCover k e`, an `ObjectProperty` of the finite étale covers of `𝔾_m`, holds for `E` when
  `E` is tame at `e.opposite` (`IsTameCoverAt`) and the geometric monodromy group of `E` at
  `gmEndPoint k e` has a unique Sylow `ringChar k`-subgroup (`Subsingleton (Sylow …)`). The
  geometric monodromy groups at two geometric points are conjugate under the transport along a
  path (Katz (1.2.1)–(1.2.2)), so the choice of the point `gmEndPoint k e` does not matter.

## `SpecialCoverEquivalenceStatement`

For a finite field `k` and every end `e`, let `f = puncturedEndToGm k e : η_e → 𝔾_m` be the map of
the punctured henselian end trait (from `Langlands.Correspondence.Laumon.TameCovers`). Then:

1. for special covers `E`, `E'` relative to `e`, pullback along `f`
   (`Scheme.FiniteEtale.pullback f`) is a bijection from the morphisms `E → E'` to the morphisms of
   their pullbacks;
2. every finite étale cover of `η_e` is isomorphic to the pullback of a special cover.

So pullback is an equivalence from special covers onto the finite étale covers of `η_e`.

Katz's theorem uses the completed field `K((T⁻¹))`. Laumon (2.2.2) uses the henselian trait.
Its fraction field in the Library is `endField k`, the separable closure of `k(t)` in
`k((t)) = LaurentSeries k`. In bridge (b2),
`Langlands.Henniart.Laumon.henselianCompletionGalois` proves
`HenselianCompletionGaloisStatement` of `Langlands.Correspondence.Laumon.Completion`.
Restriction from the Galois group of `LaurentSeries k` to that of `endField k` is an
isomorphism of topological groups. Equivalently, base change to the completion is an
equivalence on finite étale algebras, as in
`Langlands.AlgebraicGeometry.PointTopology.henselianFiniteEtaleEquivalence`. The restriction
in the statement followed by base change to `LaurentSeries k` gives Katz's restriction,
using the uniformizer `x` at `0` and `1/x` at `∞`. In (1.4.8), pp. 81–82, Katz applies the
same completion principle to the geometric field `K^sep ⊗_K K((T⁻¹))`, the union of the
fields `K'((T⁻¹))` over finite Galois extensions `K'/K`. Its completion is `K^sep((T⁻¹))`.

The field form of Katz's Kummer pullback test (1.1.2)–(1.1.3), pp. 71–72, agrees with the
wild-inertia test in `IsTameCoverAt`. For the henselian field `H` at the opposite end, with
uniformizer `t`, there is some `N ≥ 1` prime to `p` such that the finite étale restriction
becomes unramified after base change to `H(t^(1/N))`. The field factors after this base change
are composita of the original field factors with `H(t^(1/N))`, using embeddings into a
separable closure of `H`.

Katz proves the theorem for every field. The statement is the case of a finite field, the
setting of the canonical extension here. Laumon (2.2.2) works over a perfect field of
characteristic `p` ((0.1), p. 134).

## Declarations used

The module imports `Langlands.Correspondence.Laumon.TameCovers`, whose declarations
`gmOpen`, `gmGeometricSubgroup`, `gmEndPoint`, `IsTameCoverAt`, `FourierEnd.opposite` and
`puncturedEndToGm` it uses together with `puncturedEnd` and `FourierEnd` of
`Langlands.Correspondence.Laumon.Traits`. From weil-conjectures it uses
`AlgebraicGeometry.Scheme.FiniteEtale`, `AlgebraicGeometry.Scheme.FiniteEtale.fiber` and
`AlgebraicGeometry.Scheme.FiniteEtale.pullback`. Under `#print axioms` each of them depends only
on `propext`, `Classical.choice` and `Quot.sound`, and so does every declaration of this module.
The Library theorem `Langlands.AlgebraicGeometry.PointTopology.henselianFiniteEtaleEquivalence`
and `Langlands.Henniart.Laumon.henselianCompletionGalois` cited above have the same status.
