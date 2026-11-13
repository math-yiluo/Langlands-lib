# Statement: Levi subgroups are conjugate under a unique point of the unipotent radical

Worker 75.

`Langlands.GroupScheme.RelativeLeviConjugacyStatement.{u} : Prop` is a statement-only,
`Prop`-valued definition. This module does not prove it, and it adds no other definitions,
theorems or axioms. It imports [`RelativeLevi.Basic`](Basic.md) (for the three relative
predicates) and [`InnerAutomorphism`](../InnerAutomorphism.md) (for
`GroupScheme.innerIso`).

## Statement and quantifiers

The proposition quantifies over:

- every scheme `S : Scheme.{u}`;
- group schemes `G P U L L' : GroupScheme S`;
- homomorphisms `i : P ⟶ G`, `r : U ⟶ P`, `l : L ⟶ P` and `l' : L' ⟶ P`.

It has five hypotheses:

1. `IsReductive G` ([`Reductive.Basic`](../Reductive/Basic.md)): `G` is smooth and affine
   over `S` with connected reductive geometric fibres.
2. `IsRelativeParabolicSubgroup i`: `i` makes `P` a parabolic subgroup of `G`.
3. `IsRelativeUnipotentRadical r`: `r` is a unipotent radical of `P` (smooth, closed,
   normal, with the unipotent radicals as geometric fibres).
4. `IsRelativeLeviSubgroup l`.
5. `IsRelativeLeviSubgroup l'`.

All three predicates are from [`RelativeLevi.Basic`](Basic.md).

The conclusion is

```lean
∃! u : Over.mk (𝟙 S) ⟶ U.X,
  SubgroupFunctor.range l' =
    SubgroupFunctor.range (l ≫ (P.innerIso (u ≫ r.hom.hom)).hom)
```

- `u` ranges over the global points `U(S)`: morphisms over `S` from `S` itself to `U`.
- `u ≫ r.hom.hom` is the corresponding point of `P(S)`, and `P.innerIso g` is the inner
  automorphism of `P` given on every test scheme `T` by `x ↦ g_T · x · g_T⁻¹`, where `g_T`
  is the pullback of `g` to `T` (`comp_innerIso_hom` in
  [`InnerAutomorphism`](../InnerAutomorphism.md)).
- So `SubgroupFunctor.range (l ≫ (P.innerIso (u ≫ r.hom.hom)).hom)` is the conjugate
  subgroup `u L u⁻¹` of `P`, on every test scheme.

Thus there is exactly one `u ∈ U(S)` such that `L' = u L u⁻¹` as subgroups of `P`.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I, Panoramas
et Synthèses 42–43, SMF, 2014; registered as `conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are the
one-based PDF pages, which agree with the printed page numbers of this file.

- Corollary 5.4.6, p.178, first assertion: "The functor Lev(P) of Levi subgroups of P,
  equipped with its natural R_u(P)-action via conjugation in G, is represented by an
  R_u(P)-torsor."
- Proof of Corollary 5.4.6, p.178: "Since U := R_u(P) is S-affine and Levi subgroups exist
  étale-locally on S ..., it suffices to show that the sheaf Lev(P) is a U-torsor sheaf.
  Using general S, it suffices to show that if L, L′ ⊂ P are Levi S-subgroups then
  L′ = uLu⁻¹ for a unique u ∈ U(S)."
- Definition 5.4.2, p.174 (Levi subgroups and the functor `Lev(P)`).

## Derivation from the source

The torsor assertion of Corollary 5.4.6 has two parts: `Lev(P)` is an `R_u(P)`-torsor
sheaf, and this sheaf is representable. The source reduces the first part, over all bases
at once, to exactly the Lean proposition: for any `S` and any two Levi subgroups `L, L'`
of `P` there is a unique `u ∈ U(S)` with `L' = uLu⁻¹`. Applied over every `S`-scheme
`S'`, that is the statement that `U` acts simply transitively on `Lev(P)(S')` whenever
the latter is nonempty; together with the étale-local existence of Levi subgroups it is
the torsor property. The Lean proposition states the "for all `S`" form directly, with:

- `R_u(P)` replaced by any `r` satisfying `IsRelativeUnipotentRadical`, which is the
  unique such subgroup by Corollary 5.2.5;
- "`L′ = uLu⁻¹`" expressed as equality of images in `P` on every test scheme, since the
  Levi subgroups are given as abstract group schemes with closed immersions into `P`;
- conjugation "in `G`" computed inside `P`, which is the same since `u ∈ U(S) ⊂ P(S)`.

The Lean proposition does not state representability of `Lev(P)` by a scheme, nor the
étale-local existence of Levi subgroups, nor the second assertion of Corollary 5.4.6
(self-normalization, which is `RelativeLeviSelfNormalizerStatement` in
[`SelfNormalizerStatement`](SelfNormalizerStatement.md)).

## Scope

All objects are in universe `u`. The base `S` is an arbitrary scheme. Nothing is assumed
about existence of a global Levi subgroup beyond the two given ones; if `P` has no Levi
subgroup over `S`, the proposition is vacuous for that `P`.

## Relation to the Library

- Over a field, the published `RationalLeviConjugacyStatement`
  ([`Rational.RationalLeviConjugacyStatement`](../Rational/RationalLeviConjugacyStatement.md))
  states the same uniqueness of a conjugating rational point of the unipotent radical,
  with the conjugacy written through an isomorphism `L ≅ L'` of group schemes rather than
  an equality of images.

This module proves none of these relations.
