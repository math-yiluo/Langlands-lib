# Statement: the torsion subgroups of a group of multiplicative type are dense

Worker 75.

`Langlands.GroupScheme.MultiplicativeTypeTorsionDensityStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports only
[`Torus.MultiplicativeType`](MultiplicativeType.md). That module gives the field-level
predicate `IsMultiplicativeType`. Through its imports it also gives the group schemes
`GroupScheme S`, the base-change functor `GroupScheme.baseChange` and the Mathlib morphism
properties `IsClosedImmersion`, `Smooth`, `LocallyOfFiniteType` and `QuasiCompact`.

`GroupScheme S` is `Grp (Over S)`. A morphism `f : G ⟶ H` in it is a homomorphism of group
schemes over `S`. Its underlying morphism of `S`-schemes is `f.hom.hom : G.X ⟶ H.X`. The
scoped notation of `CategoryTheory.MonObj` is open. So for every `S`-scheme `T` the set of
morphisms `T ⟶ G.X` (the group `G(T)` of `T`-points of `G`) has the group structure
induced by the group law of `G`. In this group, `1` is the unit and `x ^ n` is the `n`-th
power.

## Lean statement

```lean
def MultiplicativeTypeTorsionDensityStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsMultiplicativeType G →
      (∀ (Z : Scheme.{u}) (z : Z ⟶ G.X.left), IsClosedImmersion z →
        (∀ n : ℕ, 0 < n → ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X),
          x ^ n = 1 → ∃ y : T.left ⟶ Z, y ≫ z = x.left) →
        IsIso z) ∧
      (Smooth G.X.hom →
        ∀ (Z : Scheme.{u}) (z : Z ⟶ G.X.left), IsClosedImmersion z →
          (∀ n : ℕ, (n : k) ≠ 0 → ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X),
            x ^ n = 1 → ∃ y : T.left ⟶ Z, y ≫ z = x.left) →
          IsIso z) ∧
      (∀ H : GroupScheme (Spec (CommRingCat.of k)),
        LocallyOfFiniteType H.X.hom → QuasiCompact H.X.hom →
        ∀ f₁ f₂ : G ⟶ H,
          (∀ n : ℕ, 0 < n → ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X),
            x ^ n = 1 → x ≫ f₁.hom.hom = x ≫ f₂.hom.hom) →
          f₁ = f₂)
```

## Objects and predicates used

- `IsMultiplicativeType G` (field level, module
  [`Torus.MultiplicativeType`](MultiplicativeType.md)): there are a field `K : Type u`, an
  algebra `k → K`, a finitely generated abelian group `Λ : Type u` and an isomorphism of
  group schemes over `Spec K` from `G_K` onto the diagonalizable group `D_K(Λ)`. This is
  Milne's Definition 12.17 for algebraic groups. Such a `G` is commutative and of finite
  type over `k`.
- **Torsion subgroups.** Milne writes `G_n` for the kernel of multiplication by `n` on a
  commutative algebraic group `G`. Its `T`-points are the points `x ∈ G(T)` with
  `x ^ n = 1`. The statement does not construct `G_n` as a scheme; it uses this
  description of its points.
- **Closed subschemes.** A closed subscheme of the scheme `G.X.left` is given by a scheme
  `Z` and a closed immersion `z : Z ⟶ G.X.left` (Mathlib's `IsClosedImmersion`).
  `IsIso z` says that `z` is an isomorphism of schemes, that is, the closed subscheme is
  all of `G`.
- **Containment.** A closed subscheme `z : Z ⟶ G.X.left` contains `G_n` when the closed
  immersion `G_n → G` factors through `z`. By the Yoneda lemma this holds exactly when
  every point of `G_n` factors through `z`: for every `k`-scheme `T` and every
  `x : T ⟶ G.X` with `x ^ n = 1` there is a morphism of schemes `y : T.left ⟶ Z` with
  `y ≫ z = x.left`. (Take `T = G_n` and `x` its inclusion for one direction.) This is the
  hypothesis of parts 1 and 2.
- `Smooth G.X.hom`: the structure morphism `G → Spec k` is smooth (Mathlib's `Smooth`).
- `LocallyOfFiniteType H.X.hom` and `QuasiCompact H.X.hom`: together, `H` is of finite type
  over `k`, so `H` is an algebraic group in Milne's sense.

## Statement and quantifiers

For every field `k : Type u` and every group scheme `G` over `Spec k` of multiplicative
type, the following three assertions hold.

1. **(Theorem 12.33.)** Let `z : Z ⟶ G.X.left` be a closed immersion. Suppose that for
   every `n > 0`, every `k`-scheme `T` and every `x : T ⟶ G.X` with `x ^ n = 1`, the
   morphism `x.left` factors through `z`. Then `z` is an isomorphism.
2. **(Theorem 12.32.)** Suppose that `G` is smooth over `k`. Let `z : Z ⟶ G.X.left` be a
   closed immersion. Suppose that the factorization of part 1 holds for every natural
   number `n` with `(n : k) ≠ 0`. Then `z` is an isomorphism.
3. **(Corollary 12.34.)** Let `H` be a group scheme over `Spec k` of finite type, and let
   `f₁, f₂ : G ⟶ H` be homomorphisms. Suppose that for every `n > 0`, every `k`-scheme `T`
   and every `x : T ⟶ G.X` with `x ^ n = 1` one has `x ≫ f₁.hom.hom = x ≫ f₂.hom.hom`. Then
   `f₁ = f₂`.

All schemes, including `Z` and the test schemes `T`, are in universe `u`.

## Source

James S. Milne, *Algebraic Groups: The theory of group schemes of finite type over a field*
(Cambridge University Press, 2017), source ID `milne-2017-algebraic-groups`, file
`Milne--Algebraic groups, the theory of group schemes of finite type over a field
(book)--2017.pdf`. Page numbers are printed page numbers; the PDF page is the printed page
plus 16.

- Section 12.i, p.242: "For a commutative algebraic group G and integer n ≥ 1, we let G_n
  denote the kernel of multiplication by n on G." The section continues: "The density
  theorems say that the family of subschemes G_n is schematically dense in an algebraic
  group G of multiplicative type. When G is smooth, it suffices to take the G_n with n
  prime to the characteristic."
- Theorem 12.32 (smooth case), p.242: "Let G be a smooth algebraic group of multiplicative
  type. The only closed subscheme of G containing every G_n with n prime to the
  characteristic of k is G itself." This is part 2.
- Theorem 12.33, p.243: "Let G be an algebraic group of multiplicative type over k. The
  only closed subscheme of G containing every G_n is G itself." This is part 1.
- Corollary 12.34, p.243: "Let G be an algebraic group of multiplicative type. If two
  homomorphisms from G to an algebraic group H coincide on G_n for all n ≥ 1, then they
  are equal." This is part 3. Milne's proof: "The difference kernel is a closed subscheme
  of G (as H is separated 1.22)." Here Proposition 1.22, p.12, says "Algebraic groups are
  separated (as algebraic schemes)."
- Chapter 1, p.6: "an algebraic k-scheme is a scheme of finite type over k", and
  Definition 1.1, p.6: an algebraic group over `k` is a group object in the category of
  algebraic schemes over `k`.
- Definition 12.17, p.236: "An algebraic group over k is of multiplicative type if it
  becomes diagonalizable over some field containing k."

The official errata snapshot of 2026-11-02 (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`) lists corrections only to 12.41 and 12.57
in Chapter 12. It has no correction to 12.32, 12.33 or 12.34.

Milne proves 12.32 and 12.33 after reducing to an algebraically closed field. He writes
`G` as a product of copies of `𝔾_m` with a finite group and checks that an element of
`O(G)` vanishing on every `G_n` is zero. Corollary 12.34 then follows: the difference
kernel of `f₁` and `f₂` is a closed subscheme of `G` containing every `G_n`. This is
explanation only.

## Derivation from the source

- **Algebraic group of multiplicative type.** Milne's `G` is an algebraic group of
  multiplicative type over `k`. Here `G` is a group scheme over `Spec k` with
  `IsMultiplicativeType G`. This predicate implies that `G` is of finite type over `k`.
- **"Containing every `G_n`".** `G_n ⊆ Z` as closed subschemes of `G` means that the
  inclusion `G_n → G` factors through `Z`. As explained above, this is the factorization
  of every point of `G_n` through `z`. Milne's `n` ranges over the integers `n ≥ 1` in
  12.33 and 12.34; this is `0 < n` for `n : ℕ`.
- **"n prime to the characteristic of k" (12.32).** This is encoded as `(n : k) ≠ 0`.
  When `k` has characteristic `p > 0`, this says that `p` does not divide `n`. When `k`
  has characteristic `0`, it says `n ≥ 1`, so every `G_n` with `n ≥ 1` is used. This
  matches Milne's sentence "When G is smooth, it suffices to take the G_n with n prime to
  the characteristic", which speaks of a restriction only in positive characteristic. A
  literal reading of "prime to 0" would allow only `n = 1`, and the theorem would then be
  false for `G = 𝔾_m`. `n = 0` is excluded since `(0 : k) = 0`.
- **"The only closed subscheme ... is G itself".** For a closed subscheme
  `z : Z ⟶ G.X.left` this means that `z` is an isomorphism, `IsIso z`.
- **Smooth.** Milne's "smooth algebraic group" is an algebraic group whose structure
  morphism to `Spec k` is smooth, Mathlib's `Smooth G.X.hom`.
- **Algebraic group H (12.34).** An algebraic group is a group scheme of finite type over
  `k`. Finite type is `LocallyOfFiniteType H.X.hom` together with `QuasiCompact H.X.hom`.
  Separatedness of `H` is a consequence (Milne 1.22), so it is not assumed.
- **Homomorphisms coinciding on `G_n`.** `f₁` and `f₂` coincide on `G_n` when their
  restrictions `G_n → G → H` are equal, that is, when `x ≫ f₁.hom.hom = x ≫ f₂.hom.hom`
  for every `T`-point `x` of `G` with `x ^ n = 1`. The conclusion is equality of
  homomorphisms, `f₁ = f₂` in `GroupScheme (Spec k)`.

## Scope

- Part 2 is a strengthening of part 1 only for smooth `G` in positive characteristic. Both
  are stated because they are separate theorems in the source.
- The statement does not assert schematic density in the sense of EGA IV 11.10 (which also
  concerns open subschemes). It states exactly Milne's formulation through closed
  subschemes of `G`.

## Related Library results

- [`Torus.MultiplicativeType`](MultiplicativeType.md) defines the predicate
  `IsMultiplicativeType` used here.
