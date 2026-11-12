# Common maximal split torus centralizers for two rational parabolics: proof

Author: Worker 49.

`Langlands.GroupScheme.parabolicIntersectionCentralizer` proves the published
`Langlands.GroupScheme.ParabolicIntersectionCentralizerStatement.{u}` from
`Langlands.GroupScheme.Rational.ParabolicTorusStatement`, for every universe `u`.
The theorem's type is exactly that proposition. It has no further hypotheses.

The statement's Markdown cites Borel–Tits, *Groupes réductifs* (1965), 4.18,
printed p.92 (source ID `borel-tits-1965-groupes-reductifs`). Take a field
`k : Type u`, a connected reductive group scheme `G` over `Spec k`, and two
actual rational parabolic subgroups `j : P ⟶ G` and `j' : P' ⟶ G`. The theorem
constructs a commutative group scheme `M` over `k` and `s : M.toGrp ⟶ G` with
`IsMaximalSplitTorus s`. It proves `torusCentralizer s ≤ SubgroupFunctor.range j`
and `torusCentralizer s ≤ SubgroupFunctor.range j'`. These are inclusions of
subgroup functors on every scheme over `k`. The field may be finite, imperfect
or of any characteristic. The parabolics need not be minimal.

The implemented route composes published Library results. It is not a
transcription of the printed proof. It uses neither minimal parabolics nor
rational Levi subgroups, and it does not use rational Bruhat decomposition.

## Step 1: a common rational maximal torus

The imported helper `parabolicIntersectionTorus`
(`Langlands.GroupScheme.Absolute.ParabolicIntersectionTorusProof`) proves the
published `ParabolicIntersectionTorusStatement` (Borel–Tits 4.7, first
assertion). It supplies a commutative group scheme `T` over `k`, a homomorphism
`t : T.toGrp ⟶ G` with `IsMaximalTorus t`, and factors `f : T.toGrp ⟶ P`,
`f' : T.toGrp ⟶ P'` with `f ≫ j = t` and `f' ≫ j' = t`. The torus need not be
split over `k`.

## Step 2: cocharacters of `T` over `k` presenting each parabolic

`exists_fixedTorusCocharacter_range_eq_parabolic hG ht hj f hf` proves the
following. If a rational parabolic `j : P ⟶ G` contains a rational maximal
torus `t` through `f ≫ j = t`, then there is a cocharacter
`mu : cocharacterLattice T` over `k` with
`SubgroupFunctor.range j = Dynamic.parabolic (CommGroupScheme.groupHom mu ≫ t)`.

1. `torusFiniteGaloisSplitting` gives a finite Galois extension `K / k` with
   `K : Type u` over which `T` becomes a split torus. Finite dimensionality
   makes the extension algebraic, and Mathlib's `AlgEquiv.fintype` supplies
   the finite automorphism group needed below.
2. Over `K`, the published results give everything needed.
   `IsConnectedReductive.baseChange_of_algebraicExtension` shows that `G_K` is
   connected reductive. `maximalTorusBaseChange` makes `t_K` a maximal torus.
   `parabolicFieldExtensionStatement` makes `j_K` parabolic. The base change of
   `f ≫ j = t` is `f_K ≫ j_K = t_K`.
3. The fixed-torus classification `SplitParabolicCocharacterStatement` holds.
   It is obtained inside the proof as
   `splitParabolicCocharacterStatement_of_absoluteBorelOvergroup borelConjugacy
   absoluteBorelOvergroupCocharacter maximalTorusBaseChange`. Applied over `K`,
   it gives a cocharacter `ν` of `T_K` with
   `range(j_K) = Dynamic.parabolic (ν ≫ t_K)`.
4. The reverse direction of
   `exists_range_eq_parabolic_iff_finiteGaloisBaseChange` descends this to a
   cocharacter of `T` over `k`. That theorem averages `ν` over its Galois orbit.
   Its hypotheses are supplied as follows. `G` is smooth, affine and connected.
   `T` is affine because `t` is a closed immersion into the affine `G`. The
   underlying morphism of `j` is a monomorphism because `j` is a closed
   immersion.

Applying this to `j` and to `j'` with the same torus `t` gives `mu` and `mu'`.

## Step 3: one split torus through both cocharacters

Let `I = ULift Bool` with two distinct elements `i₁, i₂`, and let `D` be the split
torus `splitTorus.commGroupScheme (Spec k) I`. Homomorphisms of commutative group
schemes form an additive group, and composition is bilinear. So
`φ = proj i₁ ≫ mu + proj i₂ ≫ mu' : D ⟶ T` is a homomorphism.
`splitTorus.single_comp_proj` gives `single i₁ ≫ φ = mu` and
`single i₂ ≫ φ = mu'`.

`IsSplitTorus.exists_dominant_factor_isSplitSubtorus` factors
`CommGroupScheme.groupHom φ ≫ t : D.toGrp ⟶ G` as `p ≫ a`, where `a : A.toGrp ⟶ G`
is a split subtorus. `exists_maximalSplitTorus_extension` extends `a` to a
maximal split torus `s : M.toGrp ⟶ G` with `g ≫ s = a`. It needs `G` affine and
locally of finite type, which follows from smoothness.

## Step 4: the centralizer inclusions

For `i = i₁` and `ν = mu`, rewriting with `g ≫ s = a`, `p ≫ a = groupHom φ ≫ t`
and `groupHom (single i₁) ≫ groupHom φ = groupHom mu` gives

```text
groupHom mu ≫ t = (groupHom (single i₁) ≫ p ≫ g) ≫ s.
```

So the cocharacter `mu ≫ t` factors through `s`. The published
`torusCentralizer_le_dynamicCentralizer` gives
`torusCentralizer s ≤ Dynamic.centralizer (groupHom mu ≫ t)`.
`Dynamic.centralizer_le_parabolic` then gives inclusion in
`Dynamic.parabolic (groupHom mu ≫ t)`, which equals `SubgroupFunctor.range j`
by Step 2. The same argument with `i₂` and `mu'` gives the inclusion into
`SubgroupFunctor.range j'`.

## Checks

`lean_check` of the two modules in environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6` reports no errors or warnings. The
theorem depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound`.
