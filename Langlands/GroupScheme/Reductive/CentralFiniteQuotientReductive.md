# Central isogenies preserve connected reductivity

Author: Worker 1546.

This module proves that the target of a central isogeny out of a connected
reductive group over a field is connected reductive. It is derived content:
the statements are chosen for the proof of
`Langlands.GroupScheme.SplitCentralTorusQuotientStatement` and are not items
of the cited literature (see Provenance).

Notation: for points `x, y` of a group scheme on a test scheme `T`, products,
powers and `1` are the Library pointwise group structure. `range f` is the
Library subgroup functor `SubgroupFunctor.range f` of a homomorphism `f`, and
`⊥` is the trivial subgroup functor. `kernel q` is the Library actual
(scheme-theoretic) kernel of `q`.

## Main result

- `Langlands.GroupScheme.isConnectedReductive_of_isCentralIsogeny`: let `k`
  be a field and `q : G ⟶ Q` a homomorphism of group schemes over `Spec k`.
  Assume `IsConnectedReductive G`, that `Q.X.hom` is affine (an instance
  argument), and `IsCentralIsogeny q`. Then `IsConnectedReductive Q`.

The four fields of `IsConnectedReductive Q` are proved as follows.

- Smoothness: `smooth_target_of_surjective_flat_hom`
  (`FppfQuotientTargetSmooth.lean`), since `G` is smooth and `q` is flat,
  surjective and locally of finite presentation.
- Affineness: the hypothesis.
- Connectedness: the underlying map of `q` is continuous and surjective and
  `G.X.left` is connected.
- Trivial geometric unipotent radical: let `b = toAlgebraicClosure k`. The base
  change `q_b` of `q` along `b` is a central isogeny
  (`IsCentralIsogeny.baseChange`), so its kernel is killed by some positive
  power `n` on every test scheme (`IsCentralIsogeny.exists_pow_eq_one_kernel`).
  The base changes of `G` and `Q` are affine, and that of `G` is smooth. The
  geometric core below, applied to `q_b`, gives the result.

## The geometric core

The new declarations in this section are in the namespace
`Langlands.GroupScheme.FiniteCentralQuotient`; the trivial-image lemma is
reused from `Langlands.GroupScheme.CenterQuotient`.

- `id_eq_one_of_isOpen_identityPoint`: let `U` be a group scheme over
  `Spec K` for a field `K`, with `U.X.hom` smooth and `U.X.left` connected.
  If the singleton of the identity point (`IdentityComponent.identityPoint U`)
  is open, then the identity morphism of `U.X` equals the constant
  morphism `1`. Proof: the unit section `η` is a section of the structure
  morphism, hence a closed immersion; its range is the identity point, which is
  then open and closed, hence everything, as `U.X.left` is connected. A smooth
  scheme over a field is reduced, so the surjective closed immersion `η` is an
  isomorphism, and so is the structure morphism. Hence `𝟙 U.X` and `1` agree
  after composition with the structure morphism, so they are equal.
- The imported `CenterQuotient.range_eq_bot_of_id_eq_one`: over any base scheme, if `𝟙 U.X = 1`, then
  `range j = ⊥` for every homomorphism `j : U ⟶ Q`. Every point `y` of `U`
  equals `y ≫ 𝟙 U.X = 1`, so `y ≫ j = 1`. This is the existing lemma from
  `Adjoint/CenterQuotientCore.lean`.
- `hasTrivialUnipotentRadical_of_kernel_pow_eq_one`: let `K` be an
  algebraically closed field and `q : G ⟶ Q` a homomorphism of group schemes
  over `Spec K`. Assume:
  - `G.X.hom` is smooth and affine, and `HasTrivialUnipotentRadical G` holds;
  - `Q.X.hom` is affine;
  - the underlying morphism of `q` is flat and locally of finite presentation;
  - there is `n > 0` with `x ^ n = 1` for every point `x` of `kernel q` on
    every test scheme.

  Then `HasTrivialUnipotentRadical Q` holds. Neither centrality nor
  surjectivity of `q` is used.

### Proof of the core

Let `j : U ⟶ Q` be a smooth connected unipotent closed subgroup with normal
range. We show `range j = ⊥`.

1. **The preimage.** Let `A = q⁻¹(U)` be the Library preimage subgroup
   (`SubgroupPreimage.groupScheme q j`, `Reductive/UnipotentRadicalQuotientReduction.lean`),
   with closed inclusion `ι_A : A ⟶ G` and projection `π : A ⟶ U`. Its range in
   `G` is normal (`SubgroupPreimage.isNormal`), and `A` is affine and locally
   of finite type.
2. **Its reduced identity component.** Let `H` be the reduced identity
   component of `A` (`ReducedSubgroup.identityCore A`), with inclusion
   `ι_H : H ⟶ A`. The composite `ι_H ≫ ι_A` is a closed immersion with normal
   range (`ReducedSubgroup.isNormal_range_identityCoreι_comp`), and `H` is
   smooth and connected.
3. **`H` has no cocharacters.** Let `z : Gm ⟶ H`. Then `z ≫ ι_H ≫ π` is a
   homomorphism from a torus to the unipotent `U`, hence `0`
   (`IsTorus.hom_eq_zero_of_isUnipotent`). By the preimage square, the
   point `z ≫ ι_H ≫ ι_A` of `G` is killed by `q`, so it factors through
   `kernel q`, and its `n`-th power is `1`. The multiplication-by-`n` map
   `m` of `Gm` is flat and surjective
   (`IsSplitTorus.flat_and_surjective_multiplication`), hence an epimorphism,
   and `m ≫ (z ≫ ι_H ≫ ι_A)` is the `n`-th power of `z ≫ ι_H ≫ ι_A`, which
   is `1`. So `z ≫ ι_H ≫ ι_A = 1`, and `z = 0` because `ι_H ≫ ι_A` is a
   monomorphism.
4. **`H` is trivial.** By step 3 and `AbsoluteNoCocharacter.isUnipotent`, `H`
   is unipotent. As a smooth connected unipotent normal closed subgroup of
   `G`, it has trivial range by `HasTrivialUnipotentRadical G`. So
   `ι_H ≫ ι_A = 1`, and hence `ι_H ≫ π = 0`: composed with the monomorphism
   `j`, it equals `ι_H ≫ ι_A ≫ q = 1`.
5. **The identity point of `U` is open.** The range of `ι_H` is open in `A`
   (`ReducedSubgroup.isOpen_range_identityCoreι`,
   `KernelCoreQuotientDimension.lean`). The projection `π` is a base change of
   `q`, so it is flat and locally of finite presentation, hence an open map.
   The image of the range of `ι_H` under `π` is the range of `ι_H ≫ π = 0`,
   which is the identity point of `U` (`range_zero_hom`). So the identity
   point is open.
6. **Conclusion.** By `id_eq_one_of_isOpen_identityPoint`, `𝟙 U.X = 1`, and
   by `CenterQuotient.range_eq_bot_of_id_eq_one`, `range j = ⊥`.

## Provenance

Reductive means a smooth connected affine group whose geometric unipotent
radical is trivial (the Library `IsConnectedReductive`, after J. S. Milne,
*Algebraic Groups*, Cambridge University Press, 2017, source ID
`milne-2017-algebraic-groups`, 6.46). The result of this module is the case
of a central isogeny of the published `CentralQuotientReductiveStatement`
(`Reductive/CentralQuotientReductiveStatement.lean`); its Markdown explains
that Milne does not state that result for an arbitrary central kernel, and
gives a source-level argument. The proof here takes a different, internal
route that uses only that the kernel of `q` has bounded exponent: the
reduced identity component of `q⁻¹(U)` has no cocharacters, so it is a
unipotent normal subgroup of `G` and hence trivial; this component is open
in `q⁻¹(U)` and the projection `q⁻¹(U) ⟶ U` is an open map, so the identity
point of `U` is open, and `U`, being connected and smooth, is trivial.

Checked with `lean_check` in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`
against Library commit `af00455e8e62bad8f10d229e6e3b908795bbf28f`
(diagnostic `6a9e6236-ce59-48ba-8c1e-7be9172bcad7`) and again against Library
commit `0bd5bf67c3464359bc8da3b3100163d6ee3da352` (diagnostic
`d36d4362-ae19-4303-b2e5-46bd5324db90`): 0 errors, 0 warnings,
axioms `propext`, `Classical.choice`, `Quot.sound`.
