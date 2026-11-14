# Statement: the simple factors of a connected reductive group over a field

Worker 75.

`Langlands.GroupScheme.ReductiveSimpleFactorDecompositionStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports:

- [`Reductive.AlmostSimple`](AlmostSimple.md), which brings in `IsConnectedReductive`
  from [`Reductive.Basic`](Basic.md) and `IsSemisimple` from
  [`Reductive.Semisimple`](Semisimple.md);
- [`SimplyConnected.AlmostSimpleProductFactors`](../SimplyConnected/AlmostSimpleProductFactors.md),
  which provides `piFactorInclusionHom A i : A i ⟶ pi A`, the homomorphism inserting the
  `i`-th factor into the finite product `pi A` (identity in all other coordinates);
- [`Rational.SplitTorusFactorization`](../Rational/SplitTorusFactorization.md), which
  provides `prodHom a b hab : A ⊗ B ⟶ M`, the homomorphism `(x, y) ↦ a(x) * b(y)` of two
  homomorphisms `a : A ⟶ M` and `b : B ⟶ M` whose values commute on every test scheme
  (`hab`), and `IsCentral.commute_values`, which supplies `hab` when `a` is central;
- [`CentralIsogeny.Basic`](../CentralIsogeny/Basic.md), which provides
  `IsCentralIsogeny` (the underlying morphism is finite, flat, surjective and locally of
  finite presentation, and the scheme-theoretic kernel is central);
- [`Derived.Basic`](../Derived/Basic.md), which provides `IsDerivedSubgroup d`: `d` is a
  closed subgroup whose range is the derived subgroup functor `derivedSubgroup G`;
- [`Torus.Lattice`](../Torus/Lattice.md), which provides the field-level `IsTorus`: the
  group becomes a split torus after base change to some field extension.

Through these imports it also uses `pi A`, the categorical finite product of a family of
group schemes from [`Products`](../Products.md); `IsClosedSubgroup` (the underlying
morphism of schemes is a closed immersion); `IsCentral` from
[`Rational.Characters`](../Rational/Characters.md) (every point of the source maps into
the centre of the target, on every test scheme); and `SubgroupFunctor.range` and
`SubgroupFunctor.IsNormal` from [`SubgroupFunctor`](../SubgroupFunctor.md). For a
homomorphism `n : K ⟶ H`, `(SubgroupFunctor.range n).carrier T` is the set of points
`y ≫ n.hom.hom` with `y : T ⟶ K.X`, for every test scheme `T`; `IsNormal` means that
these sets are normal subgroups of `H(T)` for every `T`; `≤`, `⊥` and equality of
subgroup functors are taken on every test scheme. All group schemes are over `Spec k`
and in universe `u`.

It states Conrad's Exercise 5.5.2, the reductive case of the decomposition theorem.

## Three local predicates

For field group schemes `H` and `K` and a homomorphism `n : K ⟶ H`:

- `IsNormalSubgroup n` means `IsClosedSubgroup n`, `Smooth K.X.hom`,
  `ConnectedSpace K.X.left` and `(SubgroupFunctor.range n).IsNormal`. So `n` presents
  `K` as a smooth connected closed normal subgroup of `H`, Conrad's "normal smooth
  connected `k`-subgroup".
- `IsMinimalNormalSubgroup n` means `IsNormalSubgroup n`, `SubgroupFunctor.range n ≠ ⊥`,
  and for every `K'` and `n' : K' ⟶ H` with `IsNormalSubgroup n'`,
  `SubgroupFunctor.range n' ≠ ⊥` and `range n' ≤ range n`, we have `range n' = range n`.
  These are the minimal nontrivial normal smooth connected `k`-subgroups of `H`.
- `IsMinimalNoncentralNormalSubgroup n` means `IsNormalSubgroup n`, `¬ IsCentral n`,
  and for every `K'` and `n' : K' ⟶ H` with `IsNormalSubgroup n'`, `¬ IsCentral n'` and
  `range n' ≤ range n`, we have `range n' = range n`. These are the minimal elements
  among the non-central normal smooth connected `k`-subgroups of `H`.

All three are local `let`s with the ambient group `H` implicit. `IsMinimalNormalSubgroup`
is used for `H = D`, and `IsMinimalNoncentralNormalSubgroup` for `H = G`.

## Statement

Let `k : Type u` be a field and `G` a group scheme over `Spec k` with
`IsConnectedReductive G`. Let:

- `z : Z ⟶ G` be a homomorphism with `hz : IsCentral z`, `IsClosedSubgroup z` and
  `IsTorus Z`, such that every `z' : Z' ⟶ G` with `IsClosedSubgroup z'`, `IsCentral z'`
  and `IsTorus Z'` has `range z' ≤ range z`. So `z` presents the maximal central
  `k`-torus of `G`.
- `d : D ⟶ G` satisfy `IsDerivedSubgroup d`. So `d` presents the derived group
  `D(G)`.
- `I : Type u` with `Finite I`, and `a i : A i ⟶ D` for `i : I`, such that every `a i`
  satisfies `IsMinimalNormalSubgroup` (in `D`), `i ↦ SubgroupFunctor.range (a i)` is
  injective, and every `n : K ⟶ D` with `IsMinimalNormalSubgroup n` has
  `range n = range (a i)` for some `i`. So the `a i` list the `k`-simple factors of `D`,
  each once.

Then:

1. **The factors are the minimal non-central normal subgroups of `G`.** Every
   composite `a i ≫ d` satisfies `IsMinimalNoncentralNormalSubgroup` (in `G`); and every
   `n : K ⟶ G` with `IsMinimalNoncentralNormalSubgroup n` has
   `range n = range (a i ≫ d)` for some `i`.
2. **The multiplication map is a central isogeny.** There is a homomorphism
   `p : pi A ⟶ G` with `piFactorInclusionHom A i ≫ p = a i ≫ d` for every `i`, such that
   `IsCentralIsogeny (prodHom z p (hz.commute_values p))`. Here
   `prodHom z p _ : Z ⊗ pi A ⟶ G` is `(x, y) ↦ z(x) * p(y)`.
3. **Normal semisimple subgroups of `D` are normal in `G`.** For every `n : K ⟶ D` with
   `IsNormalSubgroup n` (in `D`) and `IsSemisimple K`, the range of `n ≫ d` is normal in
   `G`: `(SubgroupFunctor.range (n ≫ d)).IsNormal`.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I, Panoramas
et Synthèses 42–43, SMF, 2014. It is registered as `conrad-2014-reductive-group-schemes`,
file `Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are
the printed page numbers.

- Exercise 5.5.2, p.182: "This exercise generalizes Theorem 5.1.19 to the reductive
  case. Let G be a connected reductive group over a field k, Z its maximal central
  k-torus, and G′ = D(G) its semisimple derived group. Let {G′_i} be the k-simple factors
  of G′. Prove that they are precisely the minimal nontrivial normal smooth connected
  non-central k-subgroups of G, and that the multiplication homomorphism
  Z × ∏ G′_i → G is a central isogeny. (Keep in mind that if k is finite then G(k) is not
  Zariski-dense in G, so in general an argument is needed to prove that the G′_i are
  normal in G.) Also prove that the normal connected semisimple k-subgroups of G′ are
  necessarily normal in G (the converse being obvious)."
- Theorem 5.1.19, p.150, which defines the `k`-simple factors of a semisimple group as
  its minimal nontrivial normal smooth connected `k`-subgroups and shows that they form a
  finite set.

Conrad leaves the exercise to the reader; the notes contain no proof of it.

## Derivation from the source

- **The maximal central torus.** Conrad's `Z` is given as data, with the property that
  defines it: a closed central `k`-torus containing every closed central `k`-torus,
  compared through ranges. The same encoding is used in the Library's
  `ReductiveDerivedCentralIsogenyStatement` over a general base. Existence is not
  asserted here; the statement applies to every such `z`.
- **The derived group.** `G′ = D(G)` is any closed subgroup `d` whose range is the
  derived subgroup functor. Conrad's adjective "semisimple" describes `D(G)`; it is not a
  hypothesis.
- **The `k`-simple factors of `G′`.** By Theorem 5.1.19 these are the minimal
  nontrivial normal smooth connected `k`-subgroups of `G′`, and they are finite in
  number. The statement takes them as a hypothesis family `a`: each `a i` is minimal,
  distinct indices give distinct subgroups, and every minimal subgroup occurs. Finiteness
  of the index type is assumed (`Finite I`); by Theorem 5.1.19 every such list is
  finite. For trivial `D` the family is empty, `pi A` is the trivial group, and
  clause 2 says that `Z ⊗ pi A ⟶ G`, `(x, 1) ↦ z(x)`, is a central isogeny.
- **"Minimal nontrivial normal smooth connected non-central `k`-subgroups of `G`".**
  The statement reads this as the minimal elements among the non-central normal smooth
  connected `k`-subgroups (`IsMinimalNoncentralNormalSubgroup`). A non-central subgroup
  is nontrivial, so "nontrivial" needs no separate condition. "Non-central" is
  `¬ IsCentral n`: some point of `K` does not map into the centre of `G`. The `G′_i`
  are subgroups of `G` through `d`, so the first half of clause 1 is about the
  composites `a i ≫ d`. "Precisely" is the two halves of clause 1, with subgroups of
  `G` compared through their ranges.
- **The multiplication homomorphism.** The factors pairwise commute (Theorem 5.1.19),
  so multiplication `∏ G′_i → G` is the homomorphism restricting to `a i ≫ d` on the
  `i`-th factor. Clause 2 asserts such a `p`. `Z` is central, so `z` and `p` have
  commuting values, and `prodHom z p _` is the multiplication `Z × ∏ G′_i → G`. Clause 2
  asserts that it is a central isogeny.
- **Normality.** "Normal connected semisimple `k`-subgroups of `G′`" are the `n` with
  `IsNormalSubgroup n` in `D` (closed, smooth, connected, normal) and
  `IsSemisimple K`. Clause 3 states that their images in `G` are normal. Conrad's
  parenthetical "converse" (a subgroup of `G′` that is normal in `G` is normal in `G′`)
  is omitted.

## Scope

The proposition does not state:

- the existence of the maximal central torus, of the derived group, or of the
  `k`-simple factors of `D(G)`; these are hypotheses;
- that `D(G)` is semisimple;
- the converse in clause 3.

Theorem 5.1.19 itself (the semisimple case) is a separate statement,
`SimpleFactorDecompositionStatement`, which this module neither imports nor uses.

## Relation to the Library

- `ReductiveCentralDerivedProductStatement` in
  [`Reductive.CentralDerivedProductStatement`](CentralDerivedProductStatement.md)
  states, over a field, that a central torus `Z` and the derived group `D` exist with
  `Z × D → G` an epimorphism.
- `ReductiveDerivedCentralIsogenyStatement` in
  [`Reductive.DerivedCentralIsogenyStatement`](DerivedCentralIsogenyStatement.md)
  states, over any base, that the maximal central torus exists and that `Z × D → G` is a
  central isogeny for a normal semisimple closed subgroup `D` with torus cokernel
  (Conrad, Corollary 5.3.3).

This statement refines the second over a field by replacing `D` with the product of its
`k`-simple factors. This module proves none of these relations.
