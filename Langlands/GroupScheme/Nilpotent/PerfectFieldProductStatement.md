# Statement: connected nilpotent group varieties over a perfect field

Worker 75.

`Langlands.GroupScheme.NilpotentPerfectFieldProductStatement.{u} : Prop` is a statement-only,
`Prop`-valued definition. This module does not prove it, and it adds no other definitions,
theorems or axioms. It imports:

- [`Nilpotent.Basic`](Basic.md), for the predicate `IsNilpotentGroupScheme` and, through its
  imports, the group-scheme vocabulary over a field, the monoidal product of group schemes and
  the predicates `IsUnipotent` and `IsTorus`.
- Mathlib's `Mathlib.FieldTheory.Perfect`, for `PerfectField`.

## Lean statement

```lean
def NilpotentPerfectFieldProductStatement : Prop :=
  ∀ (k : Type u) [Field k] [PerfectField k] (G : GroupScheme (Spec (CommRingCat.of k))),
    Smooth G.X.hom → IsAffineHom G.X.hom → ConnectedSpace G.X.left →
      (IsNilpotentGroupScheme G ↔
        ∃ (U T : GroupScheme (Spec (CommRingCat.of k))),
          Smooth U.X.hom ∧ IsAffineHom U.X.hom ∧ ConnectedSpace U.X.left ∧ IsUnipotent U ∧
            IsTorus T ∧ Nonempty (G ≅ U ⊗ T))
```

The namespace `CategoryTheory.MonoidalCategory` is open, so `U ⊗ T` is the monoidal product.

## Objects and predicates used

- **Group schemes.** `GroupScheme S` is `Grp (Over S)`. For `G : GroupScheme S`, `G.X` is its
  scheme over `S`, an object of `Over S`; `G.X.left` is the underlying scheme and `G.X.hom` its
  structure morphism to `S`.
- `Smooth G.X.hom`, `IsAffineHom G.X.hom`: Mathlib's smooth and affine morphisms of schemes.
  `ConnectedSpace G.X.left`: the underlying topological space is connected (and so nonempty).
- `PerfectField k`: Mathlib's perfect fields (every irreducible polynomial is separable).
- `IsNilpotentGroupScheme G` (module [`Nilpotent.Basic`](Basic.md)): the abstract group of
  points of the base change of `G` to `AlgebraicClosure k` with values in
  `Spec (AlgebraicClosure k)` is nilpotent. That module explains why, for smooth connected
  affine `G`, this agrees with Milne's nilpotence (Proposition 16.49).
- `IsUnipotent U` (module [`Reductive.Basic`](../Reductive/Basic.md)): every nonzero
  finite-dimensional matrix representation of `U` over `k` has a nonzero fixed vector (Milne
  6.45).
- `IsTorus T` (module [`Torus.Lattice`](../Torus/Lattice.md)): for some field extension `K` of
  `k`, the base change of `T` to `K` is a split torus (Milne Definition 12.14).
- `U ⊗ T`: the product of `U` and `T` in `Grp (Over (Spec k))`, given by the cartesian
  monoidal structure. Its underlying scheme is the fibre product of `U.X` and `T.X` over
  `Spec k`, and its group law is componentwise (module [`Products`](../Products.md) describes
  its points).
- `G ≅ U ⊗ T`: an isomorphism in `GroupScheme (Spec k)`, that is, an isomorphism of group
  schemes over `k`.

## Statement and quantifiers

For every perfect field `k : Type u` and every group scheme `G` over `Spec k` that is smooth,
affine and connected, the following are equivalent:

1. `G` is nilpotent (`IsNilpotentGroupScheme G`);
2. there are group schemes `U` and `T` over `Spec k`, with `U` smooth, affine, connected and
   unipotent and `T` a torus, such that `G` is isomorphic to `U ⊗ T` as a group scheme.

The trivial group is included, with `U` and `T` both trivial.

## Source

James S. Milne, *Algebraic Groups: The theory of group schemes of finite type over a field*
(Cambridge University Press, 2017), source ID `milne-2017-algebraic-groups`, file
`Milne--Algebraic groups, the theory of group schemes of finite type over a field
(book)--2017.pdf`. Page numbers are printed page numbers; the PDF page is the printed page
plus 16.

- Corollary 16.48, p.341: "The connected nilpotent group varieties over a perfect field k are
  exactly those of the form U × T with U a connected unipotent group variety and T a torus."
- Chapter 16 opening, p.324: "Recall that all algebraic groups are affine over a base field
  k."
- Definition 6.34, p.133: an algebraic group is nilpotent if it admits a central subnormal
  series.
- p.13, after Proposition 1.26: "Therefore 'group variety' = 'smooth algebraic group'."
- Definition 12.14, p.236: "An algebraic group over k is a torus if it becomes isomorphic to a
  finite product of copies of Gm over some field containing k."
- Proposition 14.21, p.284: "every unipotent algebraic group is nilpotent".

The official errata snapshot of 2026-11-02 (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`) lists Chapter 16 corrections only on
pp.324 (the last sentence of the first paragraph: "diagonalizable" should be
"trigonalizable"), 330 and 349. None concerns Corollary 16.48 or the affine convention. Its
Chapter 6, 12 and 14 entries (pp.129, 136, 244, 249, 273) do not concern 6.34, 12.14 or 14.21.

Milne's proof: a group of this form is nilpotent by 14.21; conversely, a smooth connected
nilpotent `G` becomes trigonalizable over a finite extension of `k` (16.30), which is separable
when `k` is perfect, so `G = U × D` with `U` unipotent and `D` of multiplicative type (Theorem
16.47(b)), and `U` and `D` are smooth and connected because `G` is. This is explanation only;
the statement does not depend on that route.

## Derivation from the source

- **Connected nilpotent group variety.** An algebraic group in Milne is a group scheme of
  finite type over `k` (Definition 1.1, p.6), and in Chapter 16 algebraic groups are affine
  (the convention above). A connected group variety there is a smooth, affine, connected group
  scheme over `k`. The statement assumes `Smooth G.X.hom`, `IsAffineHom G.X.hom` and
  `ConnectedSpace G.X.left` for `G`, and the same three conditions for `U`. Smoothness gives
  local finite presentation and affineness gives quasi-compactness, so these group schemes are
  of finite type.
- **Nilpotence.** Milne's nilpotence (6.34) is expressed through the Library's
  `IsNilpotentGroupScheme`, which is designed for smooth groups; the module
  [`Nilpotent.Basic`](Basic.md) records the comparison through Milne 16.49.
- **Unipotent and torus.** Milne's unipotent groups are the Library's `IsUnipotent` (6.45), and
  his tori are the Library's `IsTorus` (12.14). Milne's tori are smooth, affine and connected;
  this is a consequence and is not assumed separately.
- **"Exactly those of the form U × T".** Milne's sentence says that a group scheme is a
  connected nilpotent group variety if and only if it is isomorphic to such a product. The
  statement records this as an equivalence for smooth, affine, connected `G`. Nothing is lost:
  a product `U ⊗ T` of two smooth, affine, connected group schemes over a field is again
  smooth, affine and connected (a connected group scheme over a field is geometrically
  connected), so every group scheme isomorphic to such a product satisfies the three
  hypotheses on `G`. The product is the direct product of algebraic groups, so the
  isomorphism `G ≅ U ⊗ T` is one of group schemes.

## Scope

- Theorem 16.47 (the subgroup `Z(G)_s` and the decomposition over a separable trigonalizing
  extension) is not stated here. Only the existence of a decomposition is asserted; the
  uniqueness of the factors (`U = G_u`, `T = Z(G)_s`) is not part of the statement.
- Corollary 16.57 (connected nilpotent group varieties over a perfect field are unirational) is
  not stated here.

## Related Library results

- [`Nilpotent.CentralTorusStatement`](CentralTorusStatement.md) states, over any field, that a
  smooth connected affine nilpotent group has a central maximal torus with an affine unipotent
  fppf quotient (Milne 16.47(a),(c)).
- [`Cartan.StructureStatement`](../Cartan/StructureStatement.md) states that a Cartan subgroup
  of a smooth connected affine group over a field is smooth, connected and nilpotent (Milne
  17.44); with the present statement, Cartan subgroups over a perfect field are products of a
  connected unipotent group and a torus, as in Milne's proof of Theorem 17.93(a).
- `IsTorus.tensor` (module [`Torus.Products`](../Torus/Products.md)) proves that a product of two
  tori is a torus, and `SubgroupProductOrbit.isUnipotent_tensor` (module
  [`Rational.SubgroupProductGeometry`](../Rational/SubgroupProductGeometry.md)) that a product of
  two affine unipotent groups is unipotent.
