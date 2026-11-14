# Statement: automorphisms of a pinned split reductive group over a connected affine base

Author: Worker 75.

This module contains one `Prop`-valued statement,
`Langlands.GroupScheme.AffinePinnedAutomorphismGroupStatement.{u}`. The Lean file only
defines the proposition. It contains no proof of it and adds no other declarations or
axioms. It imports [`Reductive.FibrewiseRootDatum`](FibrewiseRootDatum.md) (for
`IsFibrewiseRootDatumOf`, `splitTorus`, `splitTorus.pointsEquiv` and
`splitTorus.exponentWeightSpace`), [`Reductive.Basic`](Basic.md) (for `IsReductive` and
`IsClosedSubgroup`), [`Torus.FieldPointMaximality`](../Torus/FieldPointMaximality.md) (for
`IsFibrewiseMaximalTorus`), [`Lie.KernelTargetMaps`](../Lie/KernelTargetMaps.md) (for
`Lie.targetMapLinear`), [`AutomorphicActionPointIso`](../AutomorphicActionPointIso.md)
(for `AutomorphicAction.basePointIso`), [`Rational.Characters`](../Rational/Characters.md)
(for the centre `center G`),
[`Rational.RootSubgroupStructureStatement`](../Rational/RootSubgroupStructureStatement.md)
(for `RelativeRoot.IsFppfQuotient`) and Mathlib's `LinearAlgebra/RootSystem/Base` (for
`RootPairing.Base`).

## Binders and hypotheses

All objects are in universe `u`. The proposition quantifies over:

- every commutative ring `R : Type u` such that `Spec R` is a connected topological
  space. In Mathlib a connected space is non-empty, so `R` is not the zero ring. `R` need
  not be local or Noetherian;
- a group scheme `G : GroupScheme (Spec R)` with `hG : IsReductive G`: `G` is smooth and
  affine over `Spec R`, and its geometric fibres are connected reductive groups. The
  instance `IsAffineHom G.X.hom` is taken from `hG.isAffineHom` by `haveI`;
- a finite type `I`, a homomorphism `i : splitTorus (Spec R) I ⟶ G` from the coordinate
  split torus `𝔾_m^I`, a type `J` and a Mathlib root datum
  `P : RootDatum J (I → ℤ) (I → ℤ)` on the coordinate character and cocharacter
  lattices.

The four hypotheses on `(G, i, P)` are those of
[`Reductive.AffinePinnedIsomorphismTheoremStatement`](AffinePinnedIsomorphismTheoremStatement.md)
and [`Reductive.AffineSplitIsomorphismTheoremStatement`](AffineSplitIsomorphismTheoremStatement.md).
They say that `(G, i, P)` is split in the sense of Conrad's Definition 5.1.1:

1. `IsClosedSubgroup i`: the underlying morphism of `i` is a closed immersion;
2. `IsFibrewiseMaximalTorus i`: on the residue fibre over every point of `Spec R`, the
   torus is maximal;
3. `IsFibrewiseRootDatumOf I G i P`: `J` is finite, `P` is reduced, and over every field
   `k` with a ring map `R → k`, the realization of `P` is the root datum of the base
   change of `i` to `k`. Here `m : I → ℤ` is the character `t ↦ ∏ⱼ tⱼ ^ mⱼ`;
4. for every `α : J`, the root space `splitTorus.exponentWeightSpace I G i (P.root α)` is
   free of rank one over `R`.

The remaining binders are the pinning and the adjoint quotient:

- `b : P.Base`, a base of the root pairing `P` in Mathlib's sense. Its simple roots are
  `P.root a` for `a ∈ b.support`;
- `X : ∀ a : b.support, R ≃ₗ[R] splitTorus.exponentWeightSpace I G i (P.root a)`,
  trivializations of the simple root spaces. The pinning vector of `a` is `(X a 1).val`,
  an element of the Lie algebra `lieKernel G R`. Together `(i, P, b, X)` is Conrad's
  pinned split group `(G, T, M, {X_a}_{a ∈ ∆})`, with the same conventions as
  [`Reductive.AffinePinnedIsomorphismTheoremStatement`](AffinePinnedIsomorphismTheoremStatement.md);
- a group scheme `Gad` over `Spec R` and a homomorphism `p : G ⟶ Gad` with
  `RelativeRoot.IsFppfQuotient (center G) p`: the underlying morphism of `p` is flat,
  surjective and locally of finite presentation, and the kernel of `p` has exactly the
  points of `center G`. `center G` is the subgroup functor of points that commute with
  every point of `G` after every base change, that is, the functor of points of the
  scheme-theoretic centre `Z_G`. So `Gad` is `G/Z_G`;
- an action `c : AutomorphicAction Gad G` of `Gad` on `G` by group automorphisms with
  `c.restrict p = AutomorphicAction.conjugation (𝟙 G)`: restricted along `p`, it is
  conjugation `g · x = g x g⁻¹`. This is Conrad's natural action of `G/Z_G` on `G`. As
  explained in [`Reductive.ConnectedActionInnerStatement`](ConnectedActionInnerStatement.md),
  `p × 𝟙 : G × G → Gad × G` is an epimorphism, so at most one such `c` exists.

## The two local predicates

For `θ : RootPairing.Aut P` (Mathlib: an automorphism of the root pairing, with a weight
bijection `θ.weightMap`, a root-index bijection `θ.indexEquiv` and a coweight bijection
`θ.coweightMap`, which Mathlib stores contravariantly, as the transpose of the weight
map), the product in `RootPairing.Aut P` satisfies

- `(θ₁ * θ₂).weightMap = θ₁.weightMap ∘ₗ θ₂.weightMap` (Mathlib `weightMap_mul`);
- `(θ₁ * θ₂).indexEquiv = θ₂.indexEquiv.trans θ₁.indexEquiv`, that is, first `θ₂`, then
  `θ₁` (`indexEquiv_mul`);
- `(θ₁ * θ₂).coweightMap = θ₂.coweightMap ∘ₗ θ₁.coweightMap`, in the opposite order
  (`coweightMap_mul`). Forward transport of cocharacters is the inverse of the stored
  coweight map, and that inverse composes as "first `θ₂`, then `θ₁`".

The statement uses only `θ.weightMap` and `θ.indexEquiv`.

Definitions:

- `Based θ` is `∀ j, j ∈ b.support ↔ θ.indexEquiv j ∈ b.support`: `θ` permutes the simple
  roots. The based automorphisms are Conrad's `Aut(R(G, T, M), ∆)`.

For `σ : Aut G` (automorphisms of `G` as a group scheme over `Spec R`) and `θ`,
`Pinned σ θ` says that `θ` is based (witness `hθ`), and

- there is an automorphism `τ` of the split torus `𝔾_m^I` with `i ≫ σ.hom = τ.hom ≫ i`,
  such that for every test scheme `U` over `Spec R`, every point `x : U ⟶ 𝔾_m^I` and
  every `m : I → ℤ`,
  `∏ⱼ (pointsEquiv I U (x ≫ τ))ⱼ ^ (θ.weightMap m)ⱼ = ∏ⱼ (pointsEquiv I U x)ⱼ ^ mⱼ`.
  By Yoneda this says `χ_{θ m} ∘ τ = χ_m`, that is, `χ_m ∘ τ⁻¹ = χ_{θ m}`: transport of
  characters along `σ` acts on the character lattice by `θ.weightMap`. Since
  `θ.weightMap (P.root j) = P.root (θ.indexEquiv j)`, `σ` carries the root `a` to the root
  `θ.indexEquiv a`;
- for every simple root `a`,
  `Lie.targetMapLinear σ.hom R (X a 1).val = (X ⟨θ.indexEquiv a, _⟩ 1).val`: the Lie
  algebra map of `σ` sends the pinning vector of `a` to the pinning vector of
  `θ.indexEquiv a`.

So `Pinned σ θ` says that `σ` preserves the torus and the pinning and induces `θ`. With
this convention, if `Pinned σ₁ θ₁` and `Pinned σ₂ θ₂` then `Pinned (σ₁ * σ₂) (θ₁ * θ₂)`,
using `τ₁ ∘ τ₂` for the torus. (In `Aut G`, `σ₁ * σ₂` is `σ₂ ≪≫ σ₁`, first `σ₂`.)

## Conclusion

There exist group homomorphisms

- `inn : (Over.mk (𝟙 (Spec R)) ⟶ Gad.X) →* Aut G`, from the group `Gad(S)` of sections
  of `Gad` over `S = Spec R`, and
- `π : Aut G →* RootPairing.Aut P`,

such that

1. `inn x = c.basePointIso x` for every `x ∈ Gad(S)`: `basePointIso x`
   ([`AutomorphicActionPointIso`](../AutomorphicActionPointIso.md)) is the automorphism of
   `G` by which the section `x` acts. So the action of `Gad(S)` is a group homomorphism to
   `Aut G`;
2. `inn` is injective;
3. `π.ker = inn.range`;
4. the image of `π` consists of the based automorphisms: `θ ∈ π.range ↔ Based θ`;
5. for every based `θ` there is exactly one `σ : Aut G` with `Pinned σ θ`;
6. `Pinned σ θ → π σ = θ` for all `σ` and `θ`.

By clauses 5 and 6, `θ ↦ σ_θ` (the unique pinned `σ`) is a section of `π` over the based
automorphisms. It is a homomorphism by the multiplicativity of `Pinned` and the
uniqueness in clause 5. Together the clauses say that
`1 → Gad(S) → Aut G → Aut(R(G, T, M), ∆) → 1` is exact and split by the pinning, so
`Aut G ≃ Gad(S) ⋊ Aut(R(G, T, M), ∆)`.

`π` is unique. If `π'` also satisfies clauses 3, 5 and 6, then for `σ : Aut G` the element
`π σ` is based by clause 4. Write `σ = (σ * σ_{π σ}⁻¹) * σ_{π σ}`. The first factor lies
in `ker π = inn.range = ker π'`, so `π' σ = π' σ_{π σ} = π σ`.

## Source and provenance

The statement is derived from a published result; the Lean form is not verbatim. Source:
Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I, Panoramas
et Synthèses 42–43, SMF, 2014, registered as `conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Printed page = PDF
page.

- Theorem 7.1.9, p.245: "Let G be a reductive group over a non-empty scheme S." Part (3),
  p.246: "For pinned split reductive (G, T, M, {X_a}_{a∈∆}) over S, Out_{G/S} is
  identified with the constant S-group associated to Aut(R(G, T, M), ∆). Moreover, the
  pinning defines a semi-direct product splitting of S-groups
  Aut_{G/S} ≃ (G/Z_G) ⋊ Aut(R(G, T, M), ∆)_S."
- Part (1), p.245: `Aut_{G/S}` is represented by a separated smooth `S`-group fitting
  into "a short exact sequence 1 → G/Z_G → Aut_{G/S} → Out_{G/S} → 1".
- Proof, p.246: "we have the inclusion of group sheaves
  (G/Z_G) ⋊ Aut(R(G, T, M), ∆)_S ⊂ Aut_{G/S} for the fppf topology on the category of
  S-schemes. Hence, to prove that this is an equality on S′-points for S-schemes S′ it
  suffices to work Zariski-locally on S′. … The arguments leading up to the proof of
  (7.1.3) were written to apply verbatim at the level of S′-points over any local
  S-scheme S′, upon noting that Proposition 6.2.11(2) is applicable to any local scheme."
- (7.1.3), p.243, over a field: "the choice of pinning defines an injective homomorphism
  Θ ↪ Aut(G) with image equal to the automorphism group of (G, T, B, {X_a}_{a∈∆}) …
  We have just constructed an isomorphism of groups
  (G/Z_G)(k) ⋊ Aut(R(G, T), ∆) ≃ Aut(G)."
- p.242: "The action of G on itself by conjugation factors through an action of G/Z_G on
  G. This identifies the adjoint quotient G/Z_G with a subfunctor of the automorphism
  functor Aut_{G/k}".

## Derivation from the source

The proposition is the statement of Theorem 7.1.9(3) on `S`-points, for a connected
affine base `S = Spec R`.

- *`S`-points.* `Aut_{G/S}(S)` is `Aut G`, the group of automorphisms of `G` as an
  `S`-group. The underlying sheaf of a semidirect product of group sheaves is the
  product, so the `S`-points of `(G/Z_G) ⋊ Γ_S` form the semidirect product
  `(G/Z_G)(S) ⋊ Γ_S(S)`. For the constant `S`-group `Γ_S` of a group `Γ`, `Γ_S(S)` is the
  group of locally constant maps `|S| → Γ`. Since `S` is connected, this is `Γ`. So
  part (3) gives a group isomorphism `Gad(S) ⋊ Aut(R(G, T, M), ∆) ≃ Aut G`.
- *The factors.* The subgroup `G/Z_G ⊂ Aut_{G/S}` is the natural action of `G/Z_G`
  (p.242 over a field; part (1) in general). On `S`-points it is `x ↦ c.basePointIso x`,
  with `c` the action characterized by `c.restrict p = conjugation`. Clauses 1–2 say that
  this map is an injective homomorphism. The splitting "defined by the pinning" sends
  `θ` to the automorphism of the pinned group inducing `θ`; it is the `S`-version of the
  map `Θ ↪ Aut(G)` of p.243, and over `S` this automorphism exists and is unique by the
  Isomorphism Theorem 6.1.17 (p.197). This is clause 5.
- *The projection.* `π` is the projection of the semidirect product onto
  `Aut(R(G, T, M), ∆)`, viewed inside `RootPairing.Aut P`. Its kernel is the normal factor
  (clause 3), its image is the based automorphisms (clause 4), and it is the identity on
  the section (clause 6).
- *Direction of `θ`.* Conrad's functor (6.1.2) to based root data is contravariant on
  characters. The statement fixes the covariant convention: `σ` induces `θ` when
  transport of characters along `σ` is `θ.weightMap`. With it, `θ ↦ σ_θ` is a
  homomorphism for Mathlib's product on `RootPairing.Aut P`. Pulling back characters
  instead would give an anti-homomorphism. An anti-homomorphism that is a section of a
  homomorphism `π` forces the group of based automorphisms to be commutative. The
  abstract group `Aut(R(G, T, M), ∆)` and the semidirect product decomposition do not
  depend on this choice.
- *Relation to the pinned Isomorphism Theorem.* `Pinned σ θ` holds exactly when `σ`,
  viewed as an isomorphism `G ≅ G`, satisfies the conclusion of
  [`Reductive.AffinePinnedIsomorphismTheoremStatement`](AffinePinnedIsomorphismTheoremStatement.md)
  for `H = G`, `i' = i`, `Q = P`, `Y = X` and `f = θ⁻¹`. Its character identity is
  `χ_m ∘ τ = χ_{θ⁻¹ m}`, and its pinning identity sends `X_{θ⁻¹ a'}` to `X_{a'}`. So
  clause 5 is that theorem for automorphisms. This module does not prove the
  implication.
- *Non-empty base.* Conrad assumes `S ≠ ∅`. Here `ConnectedSpace (Spec R)` includes
  non-emptiness.
- *Affine base.* `splitTorus.exponentWeightSpace` is defined only over an affine base, so
  pinnings, and hence this statement, are stated only for `S = Spec R`. This is a
  specialization of Conrad's statement.

## Scope and not stated

- The statement is about `S`-points for connected affine `S`. It does not state
  Theorem 7.1.9 as an isomorphism of group sheaves or on `S′`-points for `S`-schemes `S′`,
  the representability of `Aut_{G/S}`, the exact sequence of `S`-groups
  `1 → G/Z_G → Aut_{G/S} → Out_{G/S} → 1`, or parts (1)–(2) on `Out_{G/S}`. For
  disconnected `S`, the `S`-points of `Aut(R(G, T, M), ∆)_S` are locally constant maps,
  not elements of `Aut(R(G, T, M), ∆)`; that case is not covered.
- It does not describe `π σ` for a given `σ` beyond clause 6, for example as the action
  of `σ` on the based root datum of Remark 7.1.2. Uniqueness of `π` is shown above.
- No semisimplicity is assumed. If `P` has no roots, `G` is a split torus, `Gad(S)` is
  trivial, and the statement says that `Aut G ≅ Aut P`, the automorphisms of the lattice
  `ℤ^I` compatible with the (empty) root datum.
- Non-split groups are not treated.

## Role in the Library

This is a statement for the program of reductive group schemes over a base. A separate
proof task will prove it. The intended route follows Conrad p.246: reduce to `S′`-points
over local `S`-schemes, conjugate `(σ(T), σ(B))` back to `(T, B)` over local rings
(Proposition 6.2.11(2)), correct the pinning by a point of `(T/Z_G)(S′)` (the
unit-correction argument in the proof of Corollary 6.1.15), and apply the pinned Isomorphism Theorem
([`Reductive.AffinePinnedIsomorphismTheoremStatement`](AffinePinnedIsomorphismTheoremStatement.md)).
The field form, Conrad's Proposition 7.1.6, is submitted separately as a statement
candidate (planned module `Reductive.PinnedAutomorphismGroupStatement`); it is not part
of this candidate and is not imported. This module proves no relation between these
statements.
