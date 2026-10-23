# Additivity of the relative Lie differential

This module proves the published target
`Langlands.CommGroupScheme.LieAdditivityStatement S` for every scheme `S`.
Its closing theorem is

```lean
theorem Langlands.CommGroupScheme.lieAdditivity (S : AlgebraicGeometry.Scheme.{u}) :
    LieAdditivityStatement S
```

So for all commutative group schemes `G`, `H` over `S` and all homomorphisms
`f g : G ⟶ H`, `lieMap (f + g) = lieMap f + lieMap g`. On the left, `+` is the
pointwise group law on homomorphisms. On the right, `+` is addition of
morphisms of `𝒪_S`-modules. The statement pair
`Langlands.AbelianScheme.LieAdditivityStatement` is imported unchanged. No
hypothesis on `S`, `G` or `H` is added: no smoothness, finite presentation,
affineness or flatness. The proof uses no dual numbers or tangent points. It
computes the cotangent map of the group law directly with relative
differentials. Worker 270 wrote the Lean code and this explanation.

The module imports the statement module, which brings in the published Lie
construction `Langlands.AbelianScheme.LieFunctor`, and the helper module
`Langlands.AlgebraicGeometry.RelativeDerivationsPullback`. The helper is
described in
[RelativeDerivationsPullback.md](../AlgebraicGeometry/RelativeDerivationsPullback.md).
Its main result, `RelativeDerivation.app_eq_zero_of_isPullback`, says that a
relative derivation on a fibre product is zero once it kills the sections
pulled back along both projections.

## Objects and notation

- `GroupScheme S` is `Grp (Over S)`. `CommGroupScheme S` bundles a group
  scheme `G` with `IsCommMonObj G.X`. Its morphisms are
  `Additive (G.toGrp ⟶ H.toGrp)`, and `groupHom` forgets the additive
  notation. So `groupHom (f + g)` is by definition the product
  `groupHom f * groupHom g` in the Hom group of `Grp (Over S)`.
- For a group scheme `H` with `IsCommMonObj H.X`, Mathlib makes `H` a
  commutative group object of `Grp (Over S)` (`Monoidal/Cartesian/Grp.lean`).
  This gives the commutative group structure on `G ⟶ H` with
  `1 = toUnit G ≫ η` (`Hom.one_def`) and `f * g = lift f g ≫ μ`
  (`Hom.mul_def`). Here `lift`, `fst`, `snd` and `toUnit` belong to the
  cartesian monoidal structure of `Grp (Over S)`, and `𝟙_ (GroupScheme S)` is
  the trivial group scheme. Mathlib's `MonObj.comp_mul` gives
  `h ≫ (a * b) = (h ≫ a) * (h ≫ b)`.
- Write `c` for the published `GroupScheme.cotangentMap`. For `f : G ⟶ H` it is
  a morphism `H.cotangentAtIdentity ⟶ G.cotangentAtIdentity`. Here
  `cotangentAtIdentity G` is `e_G^* Ω_{G/S}`, the pullback along the identity
  section of the relative differentials. `c f` is the comparison
  `identityPullbackIso f` followed by `e_G^*` applied to
  `relativeDifferentialsMap` of the underlying scheme morphism. The Library
  proves `c (𝟙 G) = 𝟙` (`cotangentMap_id`) and
  `c (f ≫ g) = c g ≫ c f` (`cotangentMap_comp`). The category `S.Modules`
  is preadditive, so `c f + c g` makes sense.
- `GroupScheme.lieMap f` is `Langlands.Scheme.Modules.dualMap (c f)`.
  `CommGroupScheme.lieMap f` is `GroupScheme.lieMap (groupHom f)`.

## Step 1: the trivial homomorphism (namespace `Langlands.GroupScheme`)

- `relativeDerivation_app_eq_zero_of_id`: every relative derivation along
  `𝟙 S` is zero, by the field `app_base`. Each section of `S` is pulled
  back from the base along `𝟙 S`.
- `isZero_cotangentAtIdentity_tensorUnit`: the underlying object of the
  trivial group scheme is `Over.mk (𝟙 S)`. So its relative differentials are
  `relativeDifferentials (𝟙 S)`. This module is zero: its identity agrees
  with `0` by the uniqueness part of the universal property
  (`relativeDifferentials_hom_ext`), since both derivations obtained from
  them vanish by the previous lemma. Pulling back a zero object gives a zero
  object (`Functor.map_isZero`).
- `cotangentMap_one`: `c (1 : G ⟶ H) = 0`. Indeed `1 = toUnit G ≫ η`, so
  `c 1 = c η ≫ c (toUnit G)` by `cotangentMap_comp`. The second factor starts
  at the zero cotangent module of `𝟙_ (GroupScheme S)`, so it is `0`.

## Step 2: the projections of `H ⊗ H` are jointly epimorphic on cotangents

Let `P = H ⊗ H` be the product in `Grp (Over S)`. Its underlying scheme is the
fibre product `H.X.left ×_S H.X.left`, with the scheme projections as the
underlying maps of `fst H H` and `snd H H` (`Grp.fst_hom_hom`,
`Over.fst_left` and the `snd` versions).

- `adjoint_derivation_app_map_eq_zero`: let `p : G ⟶ H` be any homomorphism
  and `γ : G.cotangentAtIdentity ⟶ M` any morphism of `𝒪_S`-modules with
  `c p ≫ γ = 0`. Let `γ'` be its adjoint `Ω_{G/S} ⟶ (e_G)_* M` for the
  adjunction `pullbackPushforwardAdjunction e_G`. Then the derivation
  `d_G ≫ γ'` (`RelativeDerivation.postcomp`) kills every section `p^♯ a`
  pulled back from `H`. Proof: `identityPullbackIso p` is an isomorphism, so
  `c p ≫ γ = 0` says that `e_G^*` of `relativeDifferentialsMap p` followed by
  `γ` is zero. Naturality of the adjunction (`homEquiv_naturality_left`)
  turns this into `relativeDifferentialsMap p ≫ γ' = 0`. Next the
  adjunction for `p` (`homEquiv_naturality_right`) gives a zero morphism.
  Its value on `d_H a` is `γ'` applied to `d_G (p^♯ a)`, by the Library's
  `relativeDifferentialsMap_adjoint_app`.
- `cotangentMap_fst_snd_ext`: for `γ : P.cotangentAtIdentity ⟶ M`,
  `c (fst H H) ≫ γ = 0` and `c (snd H H) ≫ γ = 0` imply `γ = 0`. By the
  previous lemma, the derivation `d_P ≫ γ'` kills the sections pulled back
  along both projections. The square of projections is a pullback
  (`IsPullback.of_hasPullback`). So `app_eq_zero_of_isPullback` shows that
  this derivation is zero, that is, equal to `d_P ≫ 0`. Uniqueness in the
  universal property of `Ω_{P/S}` (`relativeDifferentials_hom_ext`) gives
  `γ' = 0`. Hence `γ = 0`, since `γ` is recovered from `γ'` through the
  counit.

## Step 3: the cotangent map of the group law

The proof never uses `μ[H]` itself. Its source `H ⊗ H` is built from Mathlib's
`Grp.instMonoidalCategory`, while `fst`, `snd` and `lift` use the cartesian
monoidal structure. The two agree definitionally, but checking that inside
sums of morphisms made the kernel time out. The proof uses instead the
product `fst H H * snd H H : H ⊗ H ⟶ H` in the Hom group, whose source is the
cartesian product.

- `lift_comp_fst_mul_snd`: `lift f g ≫ (fst H H * snd H H) = f * g`, by
  `MonObj.comp_mul`, `lift_fst` and `lift_snd`.
- `cotangentMap_lift_fst_add_lift_snd`: write `i₁ = lift (𝟙 H) 1` and
  `i₂ = lift 1 (𝟙 H)`. Then
  `c i₁ ≫ c (fst H H) + c i₂ ≫ c (snd H H) = 𝟙`. By Step 2 it suffices that
  the difference with `𝟙` is killed by `c (fst H H)` and by `c (snd H H)`.
  Composing with `c (fst H H)` and using `cotangentMap_comp` gives
  `c (i₁ ≫ fst) = c (𝟙 H) = 𝟙` and `c (i₂ ≫ fst) = c 1 = 0`
  (`cotangentMap_one`). So the composite is `c (fst H H)`, as for `𝟙`. The
  same holds for `snd`.
- `cotangentMap_fst_mul_snd`: `c (fst H H * snd H H) = c (fst H H) + c (snd H H)`.
  By `lift_comp_fst_mul_snd` and the unit laws `i₁ ≫ (fst * snd) = 𝟙 * 1 = 𝟙`
  and `i₂ ≫ (fst * snd) = 𝟙`. Hence `c (fst * snd) ≫ c iₖ = 𝟙` for both `k`.
  Precompose the identity of the previous lemma with `c (fst * snd)`.
- `cotangentMap_mul`: `c (f * g) = c f + c g` for `f g : G ⟶ H`. Write
  `f * g = lift f g ≫ (fst * snd)` and apply `cotangentMap_comp`, the
  previous lemma, `Preadditive.add_comp` and again `cotangentMap_comp` with
  `lift_fst`, `lift_snd`.

## Step 4: the Lie differential

- `lieMap_one`: `lieMap (1 : G ⟶ H) = 0`, from `cotangentMap_one` and the
  Library's `Langlands.Scheme.Modules.dualMap_zero`.
- `lieMap_mul`: `lieMap (f * g) = lieMap f + lieMap g`, from
  `cotangentMap_mul` and `Langlands.Scheme.Modules.dualMap_add`. The
  module-level additivity of `dualMap` is used only after `cotangentMap_mul`
  has related the group law to a sum of cotangent maps.
- `CommGroupScheme.lieAdditivity S`: for commutative `G`, `H` and
  `f g : G ⟶ H`, the left side `lieMap (f + g)` is by definition
  `GroupScheme.lieMap (groupHom f * groupHom g)`. So the target is
  `lieMap_mul (groupHom f) (groupHom g)`.

## Consequences

Namespace `Langlands.CommGroupScheme`:

- instance `lieFunctor_additive S : (lieFunctor S).Additive`, with `map_add`
  given by `lieAdditivity`;
- `lieMap_add`, `lieMap_zero`, `lieMap_neg` and `lieMap_sub`. They follow from
  the instance through `Functor.map_zero`, `Functor.map_neg` and
  `Functor.map_sub`.

Namespace `Langlands.AbelianScheme`:

- `commHom_add`: `commHom (f + g) = commHom f + commHom g`, by `rfl`, since
  abelian-scheme Hom groups are those of the underlying commutative group
  schemes;
- instance `lieFunctor_additive S : (lieFunctor S).Additive`. `lieMap f` is
  the commutative-group-scheme `lieMap (commHom f)`, so `map_add` is
  `CommGroupScheme.lieAdditivity` after `commHom_add`;
- `lieMap_add`, `lieMap_zero`, `lieMap_neg` and `lieMap_sub`, as above.

The intermediate results `GroupScheme.cotangentMap_one`,
`GroupScheme.cotangentMap_mul`, `GroupScheme.lieMap_one` and
`GroupScheme.lieMap_mul` hold for any group schemes `G`, `H` over `S` with
`IsCommMonObj H.X`. They are also public.

## Provenance and comparison with the literature

The statement is derived from Conrad–Gabber–Prasad, *Pseudo-reductive
Groups*, second edition (2015), registered as
`conrad-gabber-prasad-2015-pseudo-reductive`. Section 2.1, printed page 52
(PDF page 78), defines `Tan_e(G) = Hom_k(Cot_e(G), k)`. It gives a natural
bijection of `Tan_e(G)` with `ker(G(k[ε]) → G(k))`, which "is a
homomorphism". Appendix A.7, Lemma A.7.2 (printed page 530, PDF page 556),
says that right multiplication by `1 + εv` acts on the structure sheaf as
`1 + εD_v` for a left-invariant derivation `D_v`. Composing two such
translations adds the derivations, because `ε² = 0`. This is the computation
used at the start of printed page 532.

The Lean proof follows a different, coordinate-free route without dual
numbers. It computes the differential of the group law on relative
differentials. The source's "homomorphism" claim corresponds to
`cotangentMap_mul`. Its derivation-level content is Step 2: on the fibre
product `H ×_S H`, relative differentials are generated by those pulled back
along the two projections. The proof then dualizes with `dualMap`. Every
comparison is proved for the published objects: `cotangentAtIdentity`,
`cotangentMap`, `Lie` and `lieMap`, for an arbitrary base scheme.
