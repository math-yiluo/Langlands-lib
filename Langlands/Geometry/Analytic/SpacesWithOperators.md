# The fixed-`K`, `K`-linear part of Berkovich's category `𝒜n^op` of analytic spaces with operators

Author: Worker 21.

This module defines the part of Berkovich's category `𝒜n^op` of analytic
spaces with operators that lives over one fixed complete ultrametric field
`K` and uses only `K`-linear maps. Its objects are pairs `X(G)` of a
topological group `G` and a `G`-space `X` in the Library's sense: a Hausdorff
`K`-analytic space with a continuous action of `G` by `K`-linear
automorphisms. A morphism `Y(H) → X(G)` is a continuous homomorphism
`ν : H → G` together with a `K`-linear morphism of analytic spaces `φ : Y → X`
compatible with `ν`. The module also constructs:

- the functor `X(G) ↦ G` to topological groups, with a proof that this
  category is fibred over topological groups (Mathlib's `Functor.IsFibered`);
- the fibre over `G`, which is the category of continuous `K`-linear
  `G`-actions on Hausdorff `K`-analytic spaces (the Library's `GSpace K G`);
- the action of `G` on `X(G)` by conjugation;
- Berkovich's morphisms `a : X(G_d) → X(G)` and `b : X → X(G)` of
  Example 1.1.3.

Everything in the module is proved. The section "Scope" below says what part
of Berkovich's category is not covered.

## Original source

Berkovich, *Étale equivariant sheaves on p-adic analytic spaces* (unfinished
manuscript, 1995–1996), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
§1.1, printed pp.2–3 (PDF page = printed page):

> The category of analytic spaces with operators 𝒜n^op is the category of
> pairs X(G) where G is a topological group and X is a G-space. A morphism
> between such spaces φ : X′(G′) → X(G) is a pair consisting of a continuous
> homomorphism of topological groups ν_φ : G′ → G and a morphism of analytic
> spaces φ : Y → X compatible with the homomorphism ν_φ. For example, a
> G-morphism φ : Y → X between G-spaces gives rise to a morphism
> φ : Y(G) → X(G) for which ν_φ is the identity map on G. If X is a G-space,
> then the action of G on X extends to a natural action of G on X(G) for
> which ν_g(g′) = gg′g⁻¹. The category 𝒜n^op is a fibred category over the
> category of topological groups. The fibre over G will be denoted by G-𝒜n.

> 1.1.3. Example. Let X be a G-space. In what follows we'll use the following
> two morphisms a : X(G_d) → X(G) and b : X → X(G), where G_d denotes the
> group G endowed with the discrete topology and X = X({1}).

In the first sentence about morphisms Berkovich writes `φ : Y → X` for the
underlying morphism of `X′(G′) → X(G)`; `Y` there is `X′`. "Compatible with
`ν_φ`" means `φ(g′y) = ν_φ(g′)φ(y)`, that is `φ ∘ g′ = ν_φ(g′) ∘ φ`.

## Topological groups

The category of topological groups is the Library's
`Langlands.Topology.TopologicalGroup` (module
`Langlands.Topology.Category.TopologicalGroup`): groups in `Type z` with a
topology making them topological groups, and continuous homomorphisms
(Mathlib's `ContinuousMonoidHom`, `G →ₜ* H`). This module adds, in the
namespace `Langlands.Topology.TopologicalGroup`:

- `trivial`, the trivial group `{1}` (`PUnit`);
- `discrete G`, Berkovich's `G_d`: the group of `G` with the discrete
  topology. It is the Library's `Topology.DiscreteOperatorGroup` (module
  `Langlands.Topology.GroupAction.DiscreteOperatorGroup`).
  `fromDiscrete G : G_d ⟶ G` is the identity map, the Library's
  `DiscreteOperatorGroup.toOriginal`;
- `conj g : G ⟶ G`, conjugation `x ↦ g x g⁻¹` (`conj_apply`).

## The category

Let `K` be a complete ultrametric normed field.

- `SpaceWithOperators K`: a structure with fields
  `group : Topology.TopologicalGroup` and `space : GSpace K group.carrier`.
  This is Berkovich's `X(G)` for a `K`-analytic space `X` with a `K`-linear
  action.
- `SpaceWithOperators.Hom Y X`: fields `groupHom : Y.group ⟶ X.group` (`ν`),
  `hom : Y.space.obj.V ⟶ X.space.obj.V` (`φ`, a morphism of the Library's
  category `LocalizedCategory` of `K`-analytic spaces, so `K`-linear) and
  `comm`: for every `h`,
  `Y.ρ h ≫ φ = φ ≫ X.ρ (ν h)`. In diagrammatic order this is
  `φ ∘ h = ν(h) ∘ φ`, Berkovich's compatibility.
- The category instance: identities `(𝟙 G, 𝟙 X)`, composition
  `(ν, φ) ≫ (ν′, φ′) = (ν ≫ ν′, φ ≫ φ′)`. Morphisms are equal when their
  `groupHom` and `hom` agree (`hom_ext`). The `@[simp]` lemmas
  `id_groupHom`, `id_hom`, `comp_groupHom` and `comp_hom` hold by `rfl`.
- `toTopologicalGroup K : SpaceWithOperators K ⥤ Topology.TopologicalGroup`:
  `X(G) ↦ G`, `(ν, φ) ↦ ν`.
- `forget K : SpaceWithOperators K ⥤ LocalizedCategory`: `X(G) ↦ X`,
  `(ν, φ) ↦ φ`.

## The fibre over `G`

- `ofGSpace G : GSpace K G ⥤ SpaceWithOperators K`: `X ↦ X(G)`, and a
  `G`-morphism `φ` goes to `(𝟙 G, φ)`. This is Berkovich's "a G-morphism
  φ : Y → X between G-spaces gives rise to a morphism φ : Y(G) → X(G) for
  which ν_φ is the identity map on G".
- `ofGSpace G` is faithful (instance).
- `exists_ofGSpace_map_eq`: every morphism `X(G) → Y(G)` with group
  homomorphism `𝟙 G` comes from a `G`-morphism. Together with faithfulness,
  this identifies the fibre over `G` with `GSpace K G`, the category of
  continuous `K`-linear `G`-actions on Hausdorff `K`-analytic spaces. This is
  the fixed-`K` part of Berkovich's fibre `G-𝒜n`.
- `ofGSpace_comp_toTopologicalGroup`: `ofGSpace G` followed by
  `toTopologicalGroup` is the constant functor at `G` (by `rfl`).

## Fibred over topological groups

For `X(G)` and a continuous homomorphism `ν : H → G`:

- `resObj X ν` is `X(H)`: the `G`-space `X` restricted to an `H`-space along
  `ν` (Library `GSpace.res`).
- `resLift X ν : X(H) ⟶ X(G)` is the morphism `(ν, 𝟙 X)`.
- `isHomLift_iff`: a morphism `f` lies over `ν` for `toTopologicalGroup`
  (Mathlib's `Functor.IsHomLift`) exactly when `f.groupHom = ν`.
- `isStronglyCartesian_resLift`: `resLift X ν` is strongly cartesian over `ν`
  (Mathlib's `Functor.IsStronglyCartesian`). Given `f : Y(L) ⟶ X(G)` over
  `μ ≫ ν`, the unique morphism `Y(L) ⟶ X(H)` over `μ` through which `f`
  factors is `(μ, f.hom)`.
- The instance `(toTopologicalGroup K).IsFibered` follows from Mathlib's
  `Functor.IsFibered.of_exists_isStronglyCartesian`. This is Berkovich's
  sentence "The category 𝒜n^op is a fibred category over the category of
  topological groups", for the fixed-`K`, `K`-linear part.

## The action of `G` on `X(G)`

- `conjugation X g : X ⟶ X` for `g ∈ G` is the pair
  `(Topology.TopologicalGroup.conj g, X.ρ g)`: `ν_g(g′) = g g′ g⁻¹` and the
  action of `g` on `X`. Compatibility is `ρ(g′) ≫ ρ(g) = ρ(g) ≫ ρ(g g′ g⁻¹)`, both sides being
  `ρ(g g′)`.
- `conjugation_one`, `conjugation_mul`
  (`conjugation X (g * g′) = conjugation X g′ ≫ conjugation X g`), and
  `conjugationAction X : G →* End X`. In Mathlib's `End X`, multiplication is
  composition in the opposite order (`f * f′ = f′ ≫ f`). So this is a left
  action of `G` on `X(G)`: Berkovich's "natural action of G on X(G)".

## Example 1.1.3

- `discreteLift X : X(G_d) ⟶ X(G)` is Berkovich's `a`: `resLift` along
  `Topology.TopologicalGroup.fromDiscrete`. `X(G_d)` is `X` with the same
  action, regarded as a `G_d`-space.
- `underlying X` is `X({1})`, the space `X` with the trivial group, and
  `underlyingLift X : X({1}) ⟶ X(G)` is Berkovich's `b`: `resLift` along the
  trivial homomorphism `{1} → G`.

## Scope

Berkovich's conventions in §1.1 (printed p.1) are broader than this module:

> a (non-Archimedean) analytic space is a pair (k, X), where k is a
> non-Archimedean field and X is a k-analytic space, and a morphism
> (K, Y) → (k, X) is a pair consisting of an isometric embedding k ↪ K and a
> morphism of K-analytic spaces Y → X ⊗̂_k K

and, for the automorphism group `G(X)`: "(If X is k-analytic, then such an
automorphism induces an isometric automorphism of the field k.)" Example
1.1.1(i) (printed p.2) uses this generality: the Galois group `Gal(k^s/k)` acts
on `X ⊗̂_k \widehat{k^a}` through its action on the field.

This module fixes the field `K`. All analytic spaces are `K`-analytic, all
morphisms `φ` are `K`-linear, and all actions are by `K`-linear automorphisms.
The last restriction is inherited from the Library's `GSpace`
(module `ContinuousAnalyticAction`, "Provenance of choice 4"): its
automorphism group is Berkovich's group `G_K(X)` of `K`-automorphisms. Not
covered here, and left as remaining work:

- morphisms that change the ground field (`k ↪ K` with `Y → X ⊗̂_k K`); the
  Library's `LocalizedCategory` has no ground-field extension `X ⊗̂_k K` of
  analytic spaces yet;
- actions by semilinear automorphisms, which act on the ground field, such as
  the Galois actions of Example 1.1.1(i).

The constructions and proofs here are the fixed-`K` specialization of
Berkovich's. In particular, the category is fibred over topological groups and
its fibre over `G` is `GSpace K G`, not Berkovich's full `G-𝒜n`.

## Choices

- Universes: groups in `Type z`; spaces in `LocalizedCategory.{u, v, w}`, the
  universes of `GSpace`. The sites `Qét(X(G))` and `Ét(X(G))` of the Library
  use `w = v`.
- The fibration is stated with Mathlib's strongly cartesian morphisms. The
  chosen cartesian lift of `ν` at `X(G)` is the restriction `X(H)`, with the
  identity of `X` as underlying morphism.
- Berkovich next says that a morphism `X′(G′) → X(G)` induces morphisms of the
  quasi-étale and étale sites, through fibre products `X′ ×_X U`. Those are
  not formalized here; fibre products over a base are not available in the
  Library's `LocalizedCategory` in general. For morphisms `resLift X ν` the
  induced functor of sites is the Library's
  `EquivariantQuasiEtaleSite.res ν` (resp. `EquivariantEtaleSite.res ν`).
