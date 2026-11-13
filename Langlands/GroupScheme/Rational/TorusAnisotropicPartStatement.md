# The anisotropic part of a torus (Renard V.2.2, Remark 2, recalled): statement

Module `Langlands.GroupScheme.Rational.TorusAnisotropicPartStatement`. Namespace
`Langlands.GroupScheme`. Universe parameter `u` (the base field).
The module contains one **statement**, the `Prop`-valued definition
`TorusAnisotropicPartStatement`. It proves nothing.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`. V.2.2 Remark 2 recalls three facts about a torus `T`
over `F`:

- `T` has a unique maximal split subtorus `A`. The Library has this as
  `IsLargestSplitSubtorus` and the proved `exists_largestSplitSubtorus`
  ([TorusSplitPart](TorusSplitPart.md)).
- `T` has a unique maximal anisotropic subtorus `T_an`.
- `T` is the almost direct product of `A` and `T_an`.

The Chapter V item ledger records the last two as recalled assertions not stated in the
Library. V.2.5 uses them again ("T est le produit presque direct `T = T_an A`").

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read V.2.2, Remarks, printed p.105 / PDF p.111, and V.2.5, printed p.107 /
PDF p.113:

> — 2. Un tore `T` défini sur `F` est dit anisotrope si `X^*(T) = {0}` et déployé si
> `X^*(T) = X^*(𝐓)`. Tout tore `T` défini sur `F` admet un unique sous-tore déployé maximal `A`,
> et un unique sous-tore anisotrope maximal `T_an` et `T` est le produit presque direct de `A` et
> `T_an` (ceci veut dire qu'ils engendrent `T` et que leur intersection est finie).

Here `X^*(T)` denotes the characters defined over `F`.

## Published objects used

- `IsTorus` ([Torus/Lattice](../Torus/Lattice.md)): a group scheme over `k` that becomes a split
  torus after base change to some field extension.
- `IsAnisotropic` ([SplitTorus](SplitTorus.md)): split rank zero, so there is no nontrivial
  split torus inside. For a torus this is `X^*(T)_k = 0`, Renard's definition.
- `IsClosedSubgroup`: a homomorphism that is a closed immersion.
- `IsLargestSplitSubtorus a` ([TorusSplitPart](TorusSplitPart.md)): `a : A ⟶ T` is a closed
  split subtorus through which every homomorphism from a split torus factors uniquely.
- `subgroupMultiplication a b : A × T_an ⟶ T` ([LeviSubgroup](LeviSubgroup.md)): the
  multiplication morphism `(x, y) ↦ a(x) b(y)`. Its underlying morphism of schemes is
  `(subgroupMultiplication a b).left`.

## The statement

**`TorusAnisotropicPartStatement`.** For every field `k` and every torus `T` over `k`, there is
a closed subgroup `b : T_an ⟶ T` with the following properties:

1. `T_an` is an anisotropic torus;
2. every closed anisotropic subtorus `c : C ⟶ T` factors as `c = f ≫ b`;
3. for every largest split subtorus `a : A ⟶ T`, the multiplication morphism
   `A × T_an → T` is surjective and finite.

## Formalization choices

- **Uniqueness of `T_an`.** By 2, two maximal anisotropic subtori factor through each other.
  Closed immersions are monomorphisms, so they are isomorphic over `T`. The statement asserts
  existence with the universal property 2.
- **Almost direct product.** Renard explains the term: "they generate `T` and their intersection
  is finite". Generation is surjectivity of `A × T_an → T`. The kernel of this homomorphism
  is `{(x, x⁻¹)}` with `x` in `A ∩ T_an`. So finiteness of the intersection is finiteness of the
  surjective homomorphism, which is a torsor under its kernel. The statement asserts
  surjectivity and finiteness of the morphism of schemes.
- **Base field.** The statement is over an arbitrary field, like the published torus
  statements. Renard's `F` is a nonarchimedean local field.

## Why the statement is true

Let `Γ` be the Galois group of a finite Galois splitting field, so `X^*(T)` is a `Γ`-lattice and
`X^*(T)^Γ` is the group of characters defined over `k`. Rationally,
`X^*(T) ⊗ ℚ = (X^*(T) ⊗ ℚ)^Γ ⊕ I`, where `I` is the kernel of averaging over `Γ`.

Let `T_an` be the largest subtorus of the intersection of the kernels of the characters of `T`
defined over `k`. Restriction `X^*(T) → X^*(T_an)` is onto and `Γ`-equivariant, so every
character of `T_an` defined over `k` is, up to a positive multiple, the restriction of a
character of `T` defined over `k`. Hence it is trivial, and `T_an` is anisotropic. An
anisotropic subtorus `C` has no nontrivial characters over `k`, so every character of `T`
defined over `k` is trivial on `C`, and `C ⊆ T_an`.

Restriction identifies `X^*(A) ⊗ ℚ` with the invariant summand and `X^*(T_an) ⊗ ℚ` with `I`.
Hence `dim A + dim T_an = dim T` and `A ∩ T_an` is finite. The multiplication homomorphism
`A × T_an → T` therefore has finite kernel and image of full dimension. So it is surjective, and
finite as a torsor under its kernel. These are standard facts on tori over a field (the source
refers to [6], [7] and [42] for algebraic groups).

## Remaining obligations

The proof is a separate obligation.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.GroupScheme.Rational.TorusSplitPart` | `IsLargestSplitSubtorus`; through its imports `IsTorus`, `IsClosedSubgroup` |
| `Langlands.GroupScheme.Rational.SplitTorus` | `IsAnisotropic` |
| `Langlands.GroupScheme.Rational.LeviSubgroup` | `subgroupMultiplication` |
