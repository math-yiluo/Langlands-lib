# Statement: the largest subtorus of a group of multiplicative type

Worker 75.

`Langlands.GroupScheme.MultiplicativeTypeLargestSubtorusStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports:

- [`Torus.MultiplicativeType`](MultiplicativeType.md), for the field-level predicate
  `IsMultiplicativeType`. Through its imports it also gives the field-level torus predicate
  `IsTorus` ([`Torus.Lattice`](Lattice.md)), the closed-subgroup predicate
  `IsClosedSubgroup` ([`Reductive.Basic`](../Reductive/Basic.md)), the subgroup functors
  `SubgroupFunctor.range` and `SubgroupFunctor.IsNormal`
  ([`SubgroupFunctor`](../SubgroupFunctor.md)), the base-change functor
  `GroupScheme.baseChange`, and Mathlib's `Smooth` and `QuasiCompact`;
- [`Rational.RootSubgroupStructureStatement`](../Rational/RootSubgroupStructureStatement.md),
  for the fppf quotient predicate `RelativeRoot.IsFppfQuotient`;
- Mathlib's `Mathlib.AlgebraicGeometry.Morphisms.Finite`, for `IsFinite`.

`GroupScheme S` is `Grp (Over S)`. A morphism `f : G ⟶ H` in it is a homomorphism of group
schemes over `S`. Its underlying morphism of `S`-schemes is `f.hom.hom : G.X ⟶ H.X`, and
its underlying morphism of schemes is `f.hom.hom.left`.

## Lean statement

```lean
def MultiplicativeTypeLargestSubtorusStatement : Prop :=
  let IsLargestSubtorus :
      ∀ {K : Type u} [Field K] {G T : GroupScheme (Spec (CommRingCat.of K))}, (T ⟶ G) → Prop :=
    fun {K} _ {G T} t => IsTorus T ∧ IsClosedSubgroup t ∧
      ∀ (T' : GroupScheme (Spec (CommRingCat.of K))) (t' : T' ⟶ G),
        IsTorus T' → IsClosedSubgroup t' → ∃ f : T' ⟶ T, f ≫ t = t'
  ∀ (k : Type u) [Field k] (H : GroupScheme (Spec (CommRingCat.of k))),
    IsMultiplicativeType H →
      (∃ (T : GroupScheme (Spec (CommRingCat.of k))) (t : T ⟶ H), IsLargestSubtorus t) ∧
      (∀ (T : GroupScheme (Spec (CommRingCat.of k))) (t : T ⟶ H),
        IsTorus T → IsClosedSubgroup t →
        (∃ (Q : GroupScheme (Spec (CommRingCat.of k))) (q : H ⟶ Q),
          IsFinite Q.X.hom ∧ RelativeRoot.IsFppfQuotient (SubgroupFunctor.range t) q) →
        IsLargestSubtorus t) ∧
      (∀ (K : Type u) [Field K] [Algebra k K]
        (T : GroupScheme (Spec (CommRingCat.of k))) (t : T ⟶ H),
        IsLargestSubtorus t →
        IsLargestSubtorus
          ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map t)) ∧
      (∀ (G : GroupScheme (Spec (CommRingCat.of k))) (h : H ⟶ G),
        Smooth G.X.hom → QuasiCompact G.X.hom →
        IsClosedSubgroup h → (SubgroupFunctor.range h).IsNormal →
        ∀ (T : GroupScheme (Spec (CommRingCat.of k))) (t : T ⟶ H),
          IsLargestSubtorus t → (SubgroupFunctor.range (t ≫ h)).IsNormal)
```

## Objects and predicates used

- `IsMultiplicativeType H` (field level): there are a field `K : Type u`, an algebra
  `k → K`, a finitely generated abelian group `Λ : Type u` and an isomorphism of group
  schemes over `Spec K` from `H_K` onto the diagonalizable group `D_K(Λ)`. This is Milne's
  Definition 12.17. Such an `H` is commutative, affine and of finite type over `k`.
- `IsTorus T` (field level): for some field extension `K` of `k`, the base change `T_K` is
  a split torus, that is, isomorphic to a finite product of copies of `𝔾_m` over `K`. This
  is Milne's Definition 12.14.
- `IsClosedSubgroup t` for a homomorphism `t : T ⟶ G`: the underlying morphism of schemes
  `t.hom.hom.left` is a closed immersion. So `t` identifies `T` with a closed subgroup
  scheme of `G`.
- **Largest subtorus.** The local predicate `IsLargestSubtorus t`, for a homomorphism
  `t : T ⟶ G` of group schemes over a field `K`, says three things: `T` is a torus, `t` is
  a closed subgroup, and every closed subgroup `t' : T' ⟶ G` with `T'` a torus factors as
  `t' = f ≫ t` for some homomorphism `f : T' ⟶ T`. Because `t` is a monomorphism, the
  factorization says that the subtorus `T'` is contained in the subtorus `T`. The binder
  over the field `K` is implicit, so the same predicate is used over `k` in parts 1, 2 and
  4 and over `K` in part 3.
- `SubgroupFunctor.range f` for `f : T ⟶ G`: the subgroup functor of `G` whose `T₀`-points
  are the `T₀`-points of `G` that factor through `f`.
- `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range t) q` for `q : H ⟶ Q`: the morphism
  `q.hom.hom.left` is flat, surjective and locally of finite presentation, and the subgroup
  functor of points of the scheme-theoretic kernel of `q` is exactly
  `SubgroupFunctor.range t`.
- `IsFinite Q.X.hom` (Mathlib): the structure morphism of `Q` is finite, that is, `Q` is
  affine with a coordinate ring finite-dimensional over `k`.
- `(SubgroupFunctor.range f).IsNormal`: for every test scheme `T₀` over `k`, every point
  `g : T₀ ⟶ G.X` and every point `x` in `range f` over `T₀`, the conjugate `g * x * g⁻¹`
  lies in `range f` over `T₀`.
- `GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))`: the published
  base-change functor along `Spec K → Spec k`. On a homomorphism `t : T ⟶ H` it gives
  `t_K : T_K ⟶ H_K`.

## Statement and quantifiers

For every field `k : Type u` and every group scheme `H` over `Spec k` of multiplicative
type, the following four assertions hold.

1. **Existence.** There are a group scheme `T` over `Spec k` and a homomorphism
   `t : T ⟶ H` that is a largest subtorus of `H`.
2. **Characterization by a finite quotient.** Let `t : T ⟶ H` be a closed subgroup with `T`
   a torus. Suppose there are a group scheme `Q` over `Spec k`, finite over `k`, and a
   homomorphism `q : H ⟶ Q` that is an fppf quotient map with kernel `range t`. Then `t` is
   a largest subtorus of `H`.
3. **Base change.** Let `K` be a field with a `k`-algebra structure, and let `t : T ⟶ H` be
   a largest subtorus of `H`. Then `t_K : T_K ⟶ H_K` is a largest subtorus of `H_K`.
4. **Normality.** Let `G` be a group scheme over `Spec k` whose structure morphism is
   smooth and quasi-compact, and let `h : H ⟶ G` be a closed subgroup whose range is a
   normal subgroup functor of `G`. If `t : T ⟶ H` is a largest subtorus of `H`, then the
   range of `t ≫ h` is a normal subgroup functor of `G`.

All group schemes are in universe `u`, and the field `K` of part 3 is in universe `u`.

## Source

James S. Milne, *Algebraic Groups: The theory of group schemes of finite type over a field*
(Cambridge University Press, 2017), source ID `milne-2017-algebraic-groups`, file
`Milne--Algebraic groups, the theory of group schemes of finite type over a field
(book)--2017.pdf`. Page numbers are printed page numbers; the PDF page is the printed page
plus 16.

- Notation 12.29, p.241: "Let H be an algebraic group of multiplicative type over k. Then
  H = D(M) with M = X*(H). We define H_t ≝ D(M/M_tors). It is the largest subtorus of H.
  It is also the unique subtorus T of H such that H/T is finite, which shows that its
  formation commutes with extension of the base field. Note that H_t = (H°)_red. If H is a
  normal algebraic subgroup of a smooth algebraic group G, then H_t is normal in G (by
  1.52 and 1.87)."
- Proposition 1.52, p.21: "The identity component G° of an algebraic group G is a
  characteristic subgroup of G (hence a normal subgroup)."
- Corollary 1.87, p.32: "Let H be a normal algebraic subgroup of a smooth algebraic group
  G. If H_red is an algebraic subgroup of G, then it is normal in G."
- Definition 1.1, p.6, with the opening of Chapter 1: an algebraic group over `k` is a group
  object in the category of schemes of finite type over `k`. Definition 1.3, p.7: an
  algebraic subgroup of `G` is an algebraic group `H` that is a `k`-subscheme of `G` such
  that the inclusion is a homomorphism. Proposition 1.41, p.18: "Algebraic subgroups of
  algebraic groups are closed (in the Zariski topology)."
- 2.14, p.44: "An algebraic group G over k is finite if it is finite as a scheme over k."
- Definition 5.5, p.99: a homomorphism of algebraic groups is a quotient map if it is
  faithfully flat. Theorem 5.14, p.102, gives for a normal algebraic subgroup `N` of `G`
  the quotient map `G → G/N` with kernel `N`.
- Definition 12.14, p.236 (tori) and Definition 12.17, p.236 (multiplicative type).

The official errata snapshot of 2026-11-02 (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`) lists corrections only to 12.41 and 12.57
in Chapter 12. It has no correction to Notation 12.29.

## Derivation from the source

- **Subtorus.** A subtorus of `H` is an algebraic subgroup of `H` that is a torus. By
  Proposition 1.41 algebraic subgroups are closed, so a subtorus is given by a closed
  subgroup `t : T ⟶ H` with `IsTorus T`.
- **"It is the largest subtorus of H."** Every subtorus of `H` is contained in `H_t`. This
  is the factorization clause of `IsLargestSubtorus`. Part 1 asserts that such a subtorus
  exists. The statement does not construct `H_t` as `D(M/M_tors)`; it asserts the
  properties that Milne states for it.
- **"The unique subtorus T of H such that H/T is finite."** For a subtorus `T` of the
  commutative group `H`, the quotient `H/T` is given by a quotient map `q : H → Q` with
  kernel `T`, and "`H/T` finite" means that `Q` is finite over `k` (2.14). The statement
  encodes the quotient map as `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range t) q`:
  `q` is flat, surjective and locally of finite presentation, and its kernel has the same
  points as `T`. Over a field such a `q` is a quotient map in Milne's sense. Part 2 says
  that every such `T` is a largest subtorus. Since `H_t` has this property, every such `T`
  then has the same points as `H_t`. This is the uniqueness. The finiteness of `H/H_t`
  itself is the Library theorem described under Related Library results.
- **"Its formation commutes with extension of the base field."** For a field `K`
  containing `k`, `(H_t)_K` is the largest subtorus of `H_K`. This is part 3, with the
  extension given by an algebra `k → K`.
- **Normality.** "A smooth algebraic group `G`" is a group scheme of finite type over `k`
  whose structure morphism is smooth. `Smooth G.X.hom` gives local finite presentation,
  and `QuasiCompact G.X.hom` gives quasi-compactness. "H is a normal algebraic subgroup of
  G" is a closed subgroup `h : H ⟶ G` whose range is normal: for every `k`-scheme `T₀`, the
  points of `H` over `T₀` form a normal subgroup of `G(T₀)`. The conclusion "`H_t` is
  normal in `G`" is normality of the range of the composite `t ≫ h : T ⟶ G`, the subgroup
  `H_t` viewed inside `G`.

## Scope

- The identity `H_t = (H°)_red` of Notation 12.29 is not stated; the Library has no
  identity component or reduced subgroup in this form.
- The description `H_t = D(M/M_tors)` through the character group is not stated.
- Part 2 is formulated with an assumed fppf quotient by `T`. It does not assert that the
  quotient `H/T` exists; for the largest subtorus this is the Library theorem below.

## Related Library results

- [`Torus.MultiplicativeTypeStructure`](MultiplicativeTypeStructure.md) proves
  `IsMultiplicativeType.exists_torus_finiteQuotient`: every group of multiplicative type
  over a field has a closed subtorus `j : T ⟶ H` and a finite fppf quotient `H ⟶ Q` with
  kernel `range j`. This is exactly the hypothesis of part 2, so parts 1 and 2 together
  identify that subtorus as the largest one.
- [`Torus.Maximal`](Maximal.md) defines `IsMaximalTorus`, the maximality condition for a
  closed subtorus of a general group (no strictly larger closed subtorus). "Largest" in
  this statement is the stronger condition that every subtorus is contained in it.
- [`Rational.LargestCentralSubtorusBaseChangeStatement`](../Rational/LargestCentralSubtorusBaseChangeStatement.md)
  states that the largest central subtorus of a connected reductive group commutes with
  extension of the base field. It cites Notation 12.29.
