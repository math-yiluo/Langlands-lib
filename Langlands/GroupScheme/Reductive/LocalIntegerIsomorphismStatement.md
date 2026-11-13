# Statement: generic isomorphisms of reductive groups over local integers

Worker 75.

`Langlands.GroupScheme.ReductiveLocalIntegerIsomorphismStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports:

- [`Adjoint.InnerAction`](../Adjoint/InnerAction.md), for `IsAdjointQuotient.innerAction`;
  `IsAdjointQuotient` of [`Adjoint.Quotient`](../Adjoint/Quotient.md), `AutomorphicAction`
  of [`AutomorphicAction`](../AutomorphicAction.md) and `rationalPoints` of
  [`Rational.Characters`](../Rational/Characters.md) come transitively;
- [`Reductive.Basic`](Basic.md), for `IsReductive`; the base-change functor
  `GroupScheme.baseChange` of [`AbelianScheme.GroupScheme`](../../AbelianScheme/GroupScheme.md)
  comes transitively;
- Mathlib's `Mathlib.NumberTheory.LocalField.Basic`, for `IsNonarchimedeanLocalField`.

`GroupScheme S` is `Grp (Over S)`, and a morphism `H ⟶ G` in it is a homomorphism of
group schemes over `S`.

## Predicates and constructions used

- `IsNonarchimedeanLocalField F`, for a field `F` with a valuative relation and a
  topology: Mathlib's class of nonarchimedean local fields. Its fields are those whose
  topology is the valuation topology, that are locally compact, and whose valuation is
  nontrivial. Mathlib derives from this that the valuation ring `𝒪[F]` is a discrete
  valuation ring with finite residue field. `𝒪[F]` is the ring of integers of `F`.
- `Spec.algebraMap ↥𝒪[F] F : Spec F ⟶ Spec 𝒪[F]` is the morphism induced by the inclusion
  of the integers into `F`. For a group scheme `G` over `𝒪[F]`,
  `(GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] F)).obj G` is its generic fibre `G_F`,
  the pullback of `G` to `Spec F` with its induced group law, and
  `(GroupScheme.baseChange _).map Φ.hom` is the base change `Φ_F` of a homomorphism `Φ`.
- `IsReductive G`: the structure morphism of `G` is smooth and affine, and every geometric
  fibre of `G` is a connected reductive group over an algebraically closed field. This is
  Conrad's reductive group scheme (Definition 3.1.1).
- `IsAdjointQuotient q`, for `q : G_F ⟶ A` over the field `F`: `G_F` is connected reductive,
  `A` is adjoint (semisimple with trivial centre), the underlying morphism of `q` is flat,
  surjective and locally of finite presentation, its scheme kernel is the full
  scheme-theoretic centre of `G_F`, and `q` has the universal properties of the quotient
  of `G_F` by its centre, among group schemes and among schemes. Thus `A` is the adjoint
  central quotient `(G_F)^ad = G_F/Z_{G_F}`. The published theorem
  `adjointQuotientExistence` gives such a `q` for every connected reductive group over a
  field.
- `hq.innerAction : AutomorphicAction A G_F` is the action of `A` on `G_F` obtained by
  descending conjugation of `G_F` on itself along `q`. On every test scheme `T` over `F`,
  `hq.innerAction.act (q ∘ h) g = h g h⁻¹` for `h, g ∈ G_F(T)`
  (`IsAdjointQuotient.innerAction_act_lift`); it also acts by points of `A` that do not
  lift to `G_F`. `act y g` is the action of `y ∈ A(T)` on `g ∈ G_F(T)`.
- `rationalPoints A` is the group `A(F)` of sections `Over.mk (𝟙 (Spec F)) ⟶ A.X`. For a
  test scheme `T : Over (Spec F)`, the composite of the structure morphism
  `Over.homMk T.hom : T ⟶ Over.mk (𝟙 (Spec F))` with `x ∈ A(F)` is the restriction of `x`
  to `A(T)`.

## Statement and quantifiers

The proposition quantifies over every field `F : Type u` with `[ValuativeRel F]`,
`[TopologicalSpace F]` and `[IsNonarchimedeanLocalField F]`, and every
`G G' : GroupScheme (Spec 𝒪[F])` with `IsReductive G` and `IsReductive G'`; then over every
isomorphism `f : G_F ≅ G'_F` of group schemes over `F`, every `A : GroupScheme (Spec F)`,
every `q : G_F ⟶ A` and every `hq : IsAdjointQuotient q`. It asserts that there are

- a point `x : rationalPoints A`, and
- an isomorphism `Φ : G ≅ G'` of group schemes over `𝒪[F]`,

such that for every `T : Over (Spec F)` and every `g : T ⟶ G_F.X`,

```
g ≫ Φ_F = hq.innerAction.act (x|_T) g ≫ f,
```

that is, `Φ_F(g) = f(x · g)`. Taking `T = G_F.X` and `g` the identity, this says that the
underlying morphism of `Φ_F` is the composite of the action of `x` on `G_F` with `f`.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I,
Panoramas et Synthèses 42–43, SMF, 2014. It is registered as
`conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are
the one-based PDF pages, which agree with the printed page numbers.

- Setting, p.259: "Let K be a non-archimedean local field, and R its ring of integers.
  Let G be a reductive group scheme over S = Spec R." and "G^ad := G/Z_G is the adjoint
  central quotient of G".
- p.261, before the theorem: "Let G and G′ be reductive R-groups. For an isomorphism
  f : G_K ≃ G′_K between their generic fibers ... what is the obstruction to extending f
  to an R-group isomorphism G ≃ G′? ... it is more natural to permit the ambiguity of the
  action of G^ad(K) on the source."
- Theorem 7.2.16, p.261: "By composing f with the action of a suitable element of
  G^ad(K), it extends to an R-group isomorphism G ≃ G′. Equivalently, the natural map
  Isom(G, G′) → Isom(G_K, G′_K)/G^ad(K) is surjective. In particular, G and G′ are
  abstractly isomorphic."

## Derivation from the source

- **`K` and `R`.** Conrad's non-archimedean local field `K` is `F` with Mathlib's
  `IsNonarchimedeanLocalField`, and `R = 𝒪[F]`. No restriction on the characteristic is
  made, as in the source.
- **`G^ad(K)` and its action.** Conrad's `G^ad = G/Z_G` is formed over `R`; its group of
  `K`-points is the group of `K`-points of its generic fibre. Formation of the centre and
  of the central quotient commutes with the flat base change `R → K`, so
  `(G^ad)_K = G_K/Z_{G_K}`, and the natural action of `G^ad` on `G` (induced by
  conjugation) base changes to the natural action of `G_K/Z_{G_K}` on `G_K`. The statement
  works directly over `F`: `A` with `q` is the adjoint central quotient of `G_F` and
  `hq.innerAction` is its natural action. Any two adjoint quotients of `G_F` are
  isomorphic compatibly with `q` (`IsAdjointQuotient.quotientIso`), so quantifying over
  every `q` loses nothing.
- **"Composing f with the action of a suitable element ... extends to an R-group
  isomorphism".** The action of `x ∈ G^ad(K)` is an automorphism of `G_K`; composing `f`
  with it gives `f ∘ x : G_K ≃ G'_K`, and "extends to an R-group isomorphism" means that
  `f ∘ x = Φ_K` for an isomorphism `Φ : G ≃ G'` of `R`-groups. The equality of morphisms
  `G_K → G'_K` is stated on the points over every test scheme `T`, where the automorphism
  given by `x` acts as `g ↦ x|_T · g`; by Yoneda this is the equality of morphisms.
- **The two further sentences.** The reformulation "Isom(G, G′) → Isom(G_K, G′_K)/G^ad(K)
  is surjective" says the same thing: every `f` lies in the `G^ad(K)`-orbit of some `Φ_K`.
  "In particular, G and G′ are abstractly isomorphic" follows by forgetting `x`, given an
  isomorphism `f` and an adjoint quotient `q`, which exists by `adjointQuotientExistence`.
  Neither is stated separately.

## Scope

All objects are in universe `u`. The local field `F` is arbitrary, of characteristic zero
or positive characteristic. `G` and `G'` are arbitrary reductive group schemes over
`𝒪[F]`; no splitting or quasi-splitting is assumed, and no compatibility between `G` and
`G'` other than the generic isomorphism `f`.

## Not stated

The statement does not assert that the adjoint quotient `A` exists, or that `G_F` is
connected reductive; without such `q` the statement holds vacuously, and the published
`adjointQuotientExistence` supplies `q` once `G_F` is connected reductive. It does not
state Conrad's Proposition 7.2.14 (split case: the conjugacy classes of the subgroups
`G(R)`), the uniqueness of `x` or `Φ` (they are not unique), the triviality of
`H¹(R_ét, G^ad)`, or the representability of `Aut_{G/R}` used in the proof.
