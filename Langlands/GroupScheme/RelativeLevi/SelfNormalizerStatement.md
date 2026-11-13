# Statement: Levi subgroups are their own normalizers

Worker 75.

`Langlands.GroupScheme.RelativeLeviSelfNormalizerStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports [`RelativeLevi.Basic`](Basic.md) (for
`IsRelativeParabolicSubgroup` and `IsRelativeLeviSubgroup`) and
[`Rational.TorusNormalizer`](../Rational/TorusNormalizer.md) (for
`SubgroupFunctor.normalizer`).

## Statement and quantifiers

The proposition quantifies over:

- every scheme `S : Scheme.{u}`;
- group schemes `G P L : GroupScheme S`;
- homomorphisms `i : P ⟶ G` and `l : L ⟶ P`.

It has three hypotheses:

1. `IsReductive G` ([`Reductive.Basic`](../Reductive/Basic.md)): `G` is smooth and affine
   over `S` with connected reductive geometric fibres.
2. `IsRelativeParabolicSubgroup i` ([`RelativeLevi.Basic`](Basic.md)).
3. `IsRelativeLeviSubgroup l` ([`RelativeLevi.Basic`](Basic.md)): `l` is a smooth closed
   subgroup of `P` and, for some unipotent radical `r : U ⟶ P`, multiplication
   `L ×_S U ⟶ P` is an isomorphism.

The conclusion is the equality of subgroup functors of `P`

```lean
(SubgroupFunctor.range l).normalizer = SubgroupFunctor.range l
```

- `SubgroupFunctor.range l` assigns to each test `T : Over S` the subgroup of points
  `T ⟶ P.X` of the form `y ≫ l.hom.hom` with `y : T ⟶ L.X`.
- `SubgroupFunctor.normalizer F`
  ([`Rational.TorusNormalizer`](../Rational/TorusNormalizer.md)) assigns to `T` the points
  `g : T ⟶ P.X` such that, for every test `V`, every morphism `a : V ⟶ T` and every
  `x ∈ F(V)`, both `(a ≫ g) * x * (a ≫ g)⁻¹` and `(a ≫ g)⁻¹ * x * (a ≫ g)` belong to `F(V)`.

So a point of `P` over any `S`-scheme normalizes `L` exactly when it is a point of `L`.
The tests are arbitrary schemes over `S`; this is the scheme-theoretic equality
`N_P(L) = L`.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I, Panoramas
et Synthèses 42–43, SMF, 2014; registered as `conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are the
one-based PDF pages, which agree with the printed page numbers of this file.

- Corollary 5.4.6, p.178, second assertion: "In particular, any Levi S-subgroup L of P is
  its own schematic normalizer in P."
- Definition 5.4.2, p.174 (Levi subgroups of a parabolic subgroup of a reductive group
  scheme).

## Derivation from the source

The proposition is the second assertion of Corollary 5.4.6. "Schematic normalizer in `P`"
is the functor on `S`-schemes `S'` of points `g ∈ P(S')` with `g L_{S'} g⁻¹ = L_{S'}`; on
points this is the condition in `SubgroupFunctor.normalizer`, where the requirement for
both `g` and `g⁻¹` and for every refinement `a : V ⟶ T` expresses equality of the
conjugate subgroup with `L` after every base change. "Is its own normalizer" is the
equality with `SubgroupFunctor.range l`. Parabolic and Levi subgroups are those of
[`RelativeLevi.Basic`](Basic.md), whose Markdown explains the correspondence with
Definitions 5.2.1 and 5.4.2.

## Scope

All objects are in universe `u`. The base `S` is an arbitrary scheme. No maximal torus,
cocharacter or splitting is assumed. The case `P = G`, `L = G` is included.

## Relation to the Library

- The published `RelativeParabolicSelfNormalizerStatement`
  ([`RelativeParabolicNormalizerStatement`](../RelativeParabolicNormalizerStatement.md))
  is the analogous assertion `N_G(P) = P` for parabolic subgroups, over an affine base.
- The source's proof of Corollary 5.4.6 (p.178) notes that the uniqueness of the
  conjugating point, the uniqueness part of `RelativeLeviConjugacyStatement`
  ([`ConjugacyStatement`](ConjugacyStatement.md)), "expresses the property that
  N_P(L) = L (since L ⋉ U = P)".

This module proves none of these relations.
