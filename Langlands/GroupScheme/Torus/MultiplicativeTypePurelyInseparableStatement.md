# Statement: purely inseparable extensions do not change groups of multiplicative type

Worker 75.

`Langlands.GroupScheme.MultiplicativeTypePurelyInseparableStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports:

- [`Torus.MultiplicativeType`](MultiplicativeType.md), for the field-level predicate
  `IsMultiplicativeType` and, through its imports, the diagonalizable groups
  `Diagonalizable.groupScheme` and the base-change functor `GroupScheme.baseChange`;
- Mathlib's `Mathlib.FieldTheory.PurelyInseparable.Basic`, for `IsPurelyInseparable`.

`GroupScheme S` is `Grp (Over S)`, and a morphism `f : G ⟶ H` in it is a homomorphism of
group schemes over `S`.

## Lean statement

```lean
def MultiplicativeTypePurelyInseparableStatement : Prop :=
  ∀ (k k' : Type u) [Field k] [Field k'] [Algebra k k'], IsPurelyInseparable k k' →
    (∀ (H : GroupScheme (Spec (CommRingCat.of k)))
        (Λ : Type u) [AddCommGroup Λ] [AddGroup.FG Λ],
        Nonempty (((GroupScheme.baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap k k')))).obj H) ≅
            (Diagonalizable.groupScheme (CommRingCat.of k') Λ).toGrp) →
        ∃ (Λ' : Type u) (_ : AddCommGroup Λ') (_ : AddGroup.FG Λ'),
          Nonempty (H ≅ (Diagonalizable.groupScheme (CommRingCat.of k) Λ').toGrp)) ∧
    (∀ G H : GroupScheme (Spec (CommRingCat.of k)),
        IsMultiplicativeType G → IsMultiplicativeType H →
        Function.Bijective (fun f : G ⟶ H =>
          (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).map f))
```

## Predicates and constructions used

- `IsPurelyInseparable k k'` (Mathlib): `k'` is integral over `k`, and every element of
  `k'` that is separable over `k` lies in the image of `k`. So `k'/k` is a purely
  inseparable algebraic extension; it need not be finite.
- `GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))`: the
  published base-change functor along `Spec k' → Spec k` (module
  `Langlands.AbelianScheme.GroupScheme`), the scheme pullback with its induced group law.
  On objects it sends `H` to `H_{k'}`; on morphisms it sends a homomorphism `f : G ⟶ H`
  to its base change `f_{k'} : G_{k'} ⟶ H_{k'}`. It is the same functor used in
  `IsMultiplicativeType`.
- `Diagonalizable.groupScheme (CommRingCat.of K) Λ`: the diagonalizable group
  `D_K(Λ) = Spec K[Λ]` over `K`, an object of `CommGroupScheme`; `.toGrp` is its
  underlying group scheme.
- `IsMultiplicativeType G` (field level): there are a field `K : Type u`, an algebra
  `k → K`, a finitely generated abelian group `Λ : Type u` and an isomorphism of group
  schemes over `Spec K` from `G_K` onto `D_K(Λ)`. This is Milne's Definition 12.17 for
  algebraic groups, as documented in [`Torus.MultiplicativeType`](MultiplicativeType.md).

## Statement and quantifiers

The proposition quantifies over fields `k` and `k'` in the universe `u` with an algebra
`k → k'` such that `k'` is purely inseparable over `k`. Its conclusion is the conjunction
of two parts.

1. For every group scheme `H` over `Spec k` and every finitely generated abelian group
   `Λ : Type u`, if the base change `H_{k'}` is isomorphic as a group scheme over
   `Spec k'` to `D_{k'}(Λ)`, then `H` is isomorphic as a group scheme over `Spec k` to
   `D_k(Λ')` for some finitely generated abelian group `Λ' : Type u`.
2. For all group schemes `G` and `H` over `Spec k` of multiplicative type, the map
   `f ↦ f_{k'}` from homomorphisms `G ⟶ H` to homomorphisms `G_{k'} ⟶ H_{k'}` is
   bijective.

In part 1 no hypothesis is placed on `H` other than the splitting over `k'`. That
hypothesis already makes `H` of multiplicative type, with `K = k'` in
`IsMultiplicativeType`. The conclusion of part 1 does not assert that `Λ'` is isomorphic
to `Λ`.

## Source

James S. Milne, *Algebraic Groups: The theory of group schemes of finite type over a field*
(Cambridge University Press, 2017), source ID `milne-2017-algebraic-groups`, file
`Milne--Algebraic groups, the theory of group schemes of finite type over a field
(book)--2017.pdf`. Page numbers are printed page numbers; the PDF page is the printed page
plus 16.

- Corollary 12.20, p.238: "If a group of multiplicative type splits over a purely
  inseparable extension of k, then it is already split over k." This is part 1. Milne's
  proof: "This is a consequence of Exercise 11-1 when the group is finite, and the general
  case follows."
- Corollary 12.25, p.240: "Let G and H be groups of multiplicative type over a field k, and
  let k′ be a purely inseparable extension of k. Then Hom(G, H) ≃ Hom(G_{k′}, H_{k′})."
  This is part 2. Milne's proof treats the split case through
  `Hom(G, H) ≃ Hom(X(H), X(G))`, which does not change with the base field, and reduces
  the general case to it by Galois invariants over a finite Galois extension `K` of `k`
  splitting `G` and `H`: `Hom(G, H) ≃ Hom(G_K, H_K)^Γ ≃ Hom(G_{Kk′}, H_{Kk′})^Γ ≃
  Hom(G_{k′}, H_{k′})`, where `Γ = Gal(K/k) = Gal(Kk′/k′)`. This is explanation only.
- Definition 12.17, p.236: "An algebraic group over k is of multiplicative type if it
  becomes diagonalizable over some field containing k." The proof of Corollary 12.19,
  p.238, uses "splits over `k_s`" for "becomes diagonalizable over `k_s`"; so "split" for
  a group of multiplicative type means diagonalizable.

The official errata snapshot of 2026-11-02 (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`) lists no correction to Corollaries 12.20
and 12.25.

## Derivation from the source

- **Purely inseparable extension.** Milne's `k'` is any purely inseparable extension of
  `k`, not necessarily finite. This is Mathlib's `IsPurelyInseparable k k'`, which
  includes algebraicity.
- **Split, diagonalizable.** A group of multiplicative type splits over `k'` when it
  becomes diagonalizable over `k'`, that is, `H_{k'} ≅ D_{k'}(M)` for an abelian group
  `M`. Milne's groups are algebraic groups (of finite type), so `M` is finitely generated.
  The statement takes `M = Λ` finitely generated in the hypothesis and `M = Λ'` finitely
  generated in the conclusion, as in the Library's predicate `IsMultiplicativeType`.
- **Group of multiplicative type in part 1.** In Milne the group is of multiplicative type
  by assumption. Here this follows from the splitting hypothesis, so it is not repeated.
- **Hom.** `Hom(G, H)` is the set of homomorphisms of algebraic groups. The isomorphism
  `Hom(G, H) ≃ Hom(G_{k'}, H_{k'})` is the map given by extension of the base field, as
  in Milne's proof, where each step is a base-change map. The statement asserts that this
  map, `f ↦ (GroupScheme.baseChange _).map f`, is bijective.
- **Universes.** The fields `k`, `k'` and the character groups all live in the universe
  `u`, as in `IsMultiplicativeType`.

## Related Library results

- The module [`Torus.CocharacterPurelyInseparableDescent`](CocharacterPurelyInseparableDescent.md)
  constructs an equivalence of multiplicative points with coefficients extended through a
  purely inseparable field extension, for affine commutative group schemes locally of
  finite type. It is internal infrastructure about cocharacters, not a statement about
  homomorphisms between groups of multiplicative type.
- [`Torus.MultiplicativeTypeGaloisFullFaithfulnessStatement`](MultiplicativeTypeGaloisFullFaithfulnessStatement.md)
  states the finite Galois full faithfulness behind Milne's Theorem 12.23. It cites the
  proof of Corollary 12.25 but does not state the corollary.
