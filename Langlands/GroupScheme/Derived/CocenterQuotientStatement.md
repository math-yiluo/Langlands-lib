# The cocenter quotient of a connected reductive group

Authors: Worker 1532 (draft), Worker 1388.

`Langlands.GroupScheme.CocenterQuotientExistenceStatement.{u}` is a
proposition definition (`def … : Prop`). It is a statement only, not a
theorem: this module proves nothing about it. It asserts that the quotient
`M / M_der` of a connected reductive group by its derived subgroup exists
as an affine commutative group scheme and is a torus. It also asserts that
every maximal torus of `M` maps onto this quotient on cocharacters over
every field that splits that torus.

## The proposition

For every universe `u`, every field `k : Type u`, all group schemes
`M D : GroupScheme (Spec (CommRingCat.of k))` and every group-scheme
homomorphism `d : D ⟶ M` such that

1. `IsConnectedReductive M`, and
2. `IsDerivedSubgroup d`,

there exist a commutative group scheme
`D' : CommGroupScheme (Spec (CommRingCat.of k))` and a group-scheme
homomorphism `q : M ⟶ D'.toGrp` such that the following four conjuncts hold:

- `IsAffine D'.X.left`: the underlying scheme of `D'` is affine;
- `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range d) q`: `q` is an
  fppf quotient map with kernel the subgroup `d`;
- `IsTorus D'.toGrp`: `D'` is a torus;
- for every commutative group scheme
  `T : CommGroupScheme (Spec (CommRingCat.of k))`, every homomorphism
  `t : T.toGrp ⟶ M` with `IsMaximalTorus t`, and every field `E : Type u`
  with `[Algebra k E]` such that
  `IsSplitTorus (GaloisPointComparison.baseChanged k E T.toGrp)`, both
  - `IsSplitTorus (GaloisPointComparison.baseChanged k E D'.toGrp)`, and
  - the map `cocharacterLattice T_E → cocharacterLattice D'_E` given by
    `ν ↦ ν ≫ (CommGroupScheme.baseChange (GaloisPointComparison.baseMap k E)).map (Additive.ofMul (t ≫ q))`
    is surjective. Here `T_E` and `D'_E` are the images of `T` and `D'`
    under `CommGroupScheme.baseChange (GaloisPointComparison.baseMap k E)`.

Those are all the quantified objects, hypotheses and conjuncts. The universe
`u` is arbitrary. The field `k` has no perfectness, separability or
characteristic hypothesis. The groups `M` and `D` are arbitrary group schemes
over `Spec k`; only the two hypotheses above constrain them. The field `E`
can be any field with a `k`-algebra structure in the same universe. It need
not be algebraic, finite or separable over `k`. The first three conjuncts do
not depend on any maximal torus. The cocharacter conjunct is conditional:
it concerns every maximal torus `t` and every field `E` over which `T` is
split.

## The Library predicates used

- `IsConnectedReductive M` (module `Langlands.GroupScheme.Reductive.Basic`)
  is a structure with four fields. The structure morphism of `M` is smooth
  and affine, the underlying space of `M` is connected, and the base change
  of `M` to `AlgebraicClosure k` has trivial unipotent radical
  (`HasTrivialUnipotentRadical`: every smooth, connected, unipotent, normal
  closed subgroup is trivial).
- `IsDerivedSubgroup d` (module `Langlands.GroupScheme.Derived.Basic`) says
  two things. First, `d` is a closed subgroup (`IsClosedSubgroup d`: its
  underlying morphism of schemes is a closed immersion). Second,
  `SubgroupFunctor.range d = derivedSubgroup M`. The functor
  `derivedSubgroup M` is defined on each test scheme as the intersection of
  the ranges of all closed subgroups of `M` whose range contains every
  commutator `x y x⁻¹ y⁻¹` of points.
- `RelativeRoot.IsFppfQuotient N q` (module
  `Langlands.GroupScheme.Rational.RootSubgroupStructureStatement`) says that
  the underlying morphism of schemes of `q` is flat, surjective and locally
  of finite presentation. It also says that the range of the kernel
  inclusion `kernelι q` equals `N` on every test scheme. With
  `N = SubgroupFunctor.range d` this makes `D'` the fppf quotient
  `M / M_der`.
- `IsTorus G` (module `Langlands.GroupScheme.Torus.Lattice`) says that for
  some field `K : Type u` with `[Algebra k K]` the base change of `G` to
  `Spec K` is a split torus.
- `IsMaximalTorus t` (module `Langlands.GroupScheme.Torus.Maximal`) says
  three things. First, `T.toGrp` is a torus (`IsTorus`). Second, `t` is a
  closed subgroup. Third, whenever `t = f ≫ i'` for a closed subgroup
  `i' : T'.toGrp ⟶ M` with `T'` a torus, the factor `f` is an isomorphism.
  In other words, `t` lies in no strictly larger closed `k`-torus of `M`.
- `IsSplitTorus G` (module `Langlands.GroupScheme.Torus.Split`) says that
  `G` is isomorphic, as a group scheme over its base, to the split torus
  `splitTorus S I` for some finite index type `I : Type u`.
- `cocharacterLattice T` (module `Langlands.GroupScheme.Torus.Lattice`) is
  the type `Gm S ⟶ T` of homomorphisms of commutative group schemes from
  the multiplicative group, that is, the cocharacter group `X_*(T)`.
- `GaloisPointComparison.baseMap k E` (module
  `Langlands.GroupScheme.GaloisPointRational`) is the morphism
  `Spec E ⟶ Spec k` induced by `algebraMap k E`. `baseChanged k E G` is the
  base change of `G` along it. `CommGroupScheme.baseChange` (module
  `Langlands.AbelianScheme.GroupScheme`) is the base-change functor on
  commutative group schemes. Its object `T_E` has underlying group scheme
  `baseChanged k E T.toGrp`, so the splitting hypothesis on `T` and the
  splitting conclusion on `D'` refer to the same base changes as the
  cocharacter lattices.
- `Additive.ofMul (t ≫ q) : T ⟶ D'` is the composite `T → M → D'` viewed as
  a morphism of commutative group schemes. In the Library, such a morphism
  is a group-scheme homomorphism wrapped in `Additive`.

## Relation to other Library results and to consumers

The Library theorem `normalSubgroupQuotientExistence` (module
`Langlands.GroupScheme.NormalQuotientExistenceProof`) gives a quotient by a
closed normal subgroup of an affine, locally finite type group only as a
`GroupScheme`. It records that the structure morphism of the quotient is
affine and locally of finite type, and the fppf-quotient property. It gives
no commutative structure, no torus property and no cocharacter comparison,
so it does not give this proposition. `DerivedSubgroupStructureStatement` (module
`Langlands.GroupScheme.Derived.StructureStatement`) concerns
representability, base change, smoothness and connectedness of the derived
subgroup. It does not state this proposition either.

The cocharacter conjunct has the same form as hypothesis 3 of
`Langlands.Geometry.Building.TorusIwahoriSurjectivityStatement`
(KP Lemma 2.5.20(1), task `89233dc7-3f93-44d1-b189-8686082149ba`), with
`f := Additive.ofMul (t ≫ q)`. That statement quantifies over an
intermediate field `L` of the unramified closure; as a type, `L` is a field
with an algebra structure over the base field, so `E := L` is an admissible
choice here. The conjunct `IsAffine D'.X.left` supplies that statement's
instance for `T₃ := D'`.
This proposition does not assert `IsAffine T.X.left`. A consumer has to
supply it separately; mathematically it holds because `t` is a closed
immersion into the affine `M`.

## Source and derived formulation

Tasho Kaletha and Gopal Prasad, *Bruhat–Tits Theory: A New Approach*,
Cambridge University Press, 2023, registered as
`kaletha-prasad-2023-bruhat-tits-new-approach` (KP). Printed page = PDF
page − 31.

- §2.6(a), printed p. 93 / PDF p. 124, fixes the notation: `G_der` is the
  derived subgroup of a connected reductive group `G` over any field. The
  same paragraph states that for a maximal torus `T ⊂ G` the intersection
  `T ∩ G_der` is a maximal torus `T_der` of `G_der`.
- The proof of Lemma 2.6.27, printed p. 105 / PDF p. 136, takes a
  maximally split maximal `K`-torus `T` of the minimal Levi subgroup `M_0`.
  It sets `T_sc = T ∩ M_0,der`, forms the torus `D = T / T_sc`, and uses the
  image of an element of `M_0(K)^1` in `D(K)`. This implicitly uses a map
  `M_0 → D` identifying `D` with `M_0 / M_0,der`. The proof then applies
  Lemma 2.5.20 to `T → D` to lift that image to an element of `T(K)^0`.

The section 2.6 entries of the authors' corrections
(`kaletha-prasad-2024-corrections`, version of 1 November 2024) concern
§2.6(d), the text before Definition 2.6.20 and Definition 2.6.23. None
concerns §2.6(a) or Lemma 2.6.27.

This proposition is a derived formulation and not a numbered result of KP.
It packages the quotient `M → M / M_der` and the facts that the cited proof
uses for `D`: affineness, being a torus, splitting over a field that splits
`T`, and surjectivity on cocharacters, which hypothesis 3 of Lemma 2.5.20(1)
needs. It is stated for an arbitrary connected reductive group over an
arbitrary field, not only for `M_0` over `K`.

The following standard argument is the reason the proposition holds. It is
recorded as provenance only; nothing here proves it. The maximal torus `T`
contains the central torus of `M`, so `M = T · M_der`. By KP §2.6(a),
`T ∩ M_der` is a maximal torus of `M_der`. Hence
`M / M_der ≅ T / (T ∩ M_der)` is a torus. Over a field `E` splitting `T`
there is an exact sequence of split tori

`1 → T ∩ M_der → T → M / M_der → 1`

whose kernel `T ∩ M_der` is connected. So `X_*(T ∩ M_der)` is saturated in
`X_*(T)`, and the induced map `X_*(T_E) → X_*((M / M_der)_E)` is
surjective.

The surjectivity on cocharacters is stronger than `q` being an fppf
quotient. For example, the `n`-th power map of `G_m` is an fppf quotient
(by `μ_n`) but acts on cocharacters as multiplication by `n`, which is not
surjective for `n ≥ 2`. So a proof of the cocharacter conjunct must use that
the kernel `T ∩ M_der` of `T → M / M_der` is connected for the actual
derived subgroup. An isogeny argument alone does not suffice.

A proof of this proposition is a separate `lean.proof@1` obligation.
