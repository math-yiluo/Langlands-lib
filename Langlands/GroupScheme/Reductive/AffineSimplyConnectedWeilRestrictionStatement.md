# Statement: simply connected semisimple group schemes as Weil restrictions

Worker 75.

`Langlands.GroupScheme.AffineSimplyConnectedWeilRestrictionStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports
[`Reductive.AlmostSimple`](AlmostSimple.md) (for `IsAlmostSimple` and, through it,
`IsReductive`, `geometricFiber` and `IsSemisimple` from [`Reductive.Basic`](Basic.md)),
[`SimplyConnected.Basic`](../SimplyConnected/Basic.md) (for `IsSimplyConnected`) and
[`AffineWeilRestriction`](../AffineWeilRestriction.md) (for the actual Weil restriction
`AffineWeil.groupScheme`).

It states Conrad's Proposition 6.4.4 over an affine base `Spec A`: a fibrewise
nontrivial semisimple group scheme with simply connected fibres is the Weil restriction,
along a finite étale cover, of a semisimple group scheme with simply connected and
absolutely simple fibres; and this description is unique up to isomorphism.

## Statement and quantifiers

The proposition quantifies over every commutative ring `A : Type u` and every group
scheme `G : GroupScheme (Spec A)`. It has three hypotheses:

1. `IsReductive G` ([`Reductive.Basic`](Basic.md)): `G` is smooth and affine over
   `Spec A`, and each geometric fibre `geometricFiber G s` (the base change along
   `Spec κ(s)^alg → Spec A`, with `κ(s)^alg` the Mathlib `AlgebraicClosure` of the residue
   field) satisfies the field predicate `IsPseudoReductive`, that is, it is a connected
   reductive group over an algebraically closed field.
2. For every point `s` of `Spec A`, `IsSimplyConnected (geometricFiber G s)`
   ([`SimplyConnected.Basic`](../SimplyConnected/Basic.md)): the geometric fibre is
   semisimple (`IsSemisimple`), and every central isogeny onto it from a semisimple group
   is an isomorphism.
3. For every point `s` of `Spec A`, there are a scheme `T` over `Spec κ(s)^alg` and a point
   `x : T ⟶ (geometricFiber G s).X` with `x ≠ 1`. Here `1` is the unit of the group of
   `T`-points (Mathlib's `MonObj` structure, notation opened by `open scoped
   CategoryTheory.MonObj`), namely `T → Spec κ(s)^alg` followed by the unit section.
   This says exactly that the geometric fibre is not the trivial group: if it were trivial
   every point would be `1`, and if it is not trivial the identity point
   (`T = (geometricFiber G s).X`, `x = 𝟙`) differs from `1`.

The conclusion is a conjunction of an existence clause and a uniqueness clause.

### Existence

There are

- a commutative ring `B : Type u` with an `A`-algebra structure, such that `B` is a finite
  `A`-module (`Module.Finite A B`), a projective `A`-module (`Module.Projective A B`) and
  étale over `A` (`Algebra.Etale A B`), and `Spec B → Spec A` is surjective
  (`Surjective (Spec.map (CommRingCat.ofHom (algebraMap A B)))`);
- a group scheme `G' : GroupScheme (Spec B)` with instance witnesses `IsAffine G'.X.left`
  and `LocallyOfFiniteType G'.X.hom`, such that `IsReductive G'` and, for every point `s'`
  of `Spec B`, `IsSimplyConnected (geometricFiber G' s')` and
  `IsAlmostSimple (geometricFiber G' s')` ([`Reductive.AlmostSimple`](AlmostSimple.md));
- an isomorphism `G ≅ AffineWeil.groupScheme A B G'` of group schemes over `Spec A`,
  enclosed in `Nonempty`.

`AffineWeil.groupScheme A B G'` is the Library's Weil restriction `R_{B/A}(G')`: its
points over an `A`-algebra `T` are the points of `G'` over `B ⊗_A T`, with the group law
of `G'` ([`AffineWeilRestriction`](../AffineWeilRestriction.md)). Its construction needs
`Module.Finite A B`, `Module.Projective A B`, `IsAffine G'.X.left` and
`LocallyOfFiniteType G'.X.hom`; this is why those witnesses appear in the existential.

### Uniqueness

For all commutative rings `B B'' : Type u` that are finite, projective and étale
`A`-algebras, and all group schemes `G'` over `Spec B` and `G''` over `Spec B''` with
affine total spaces and locally of finite type structure morphisms, if

- `IsReductive G'` and `IsReductive G''`,
- every geometric fibre of `G'` and every geometric fibre of `G''` is simply connected
  and almost simple, and
- `G ≅ AffineWeil.groupScheme A B G'` and `G ≅ AffineWeil.groupScheme A B'' G''`,

then there are an `A`-algebra isomorphism `α : B'' ≃ₐ[A] B` and an isomorphism of group
schemes over `Spec B` from the base change of `G''` along
`Spec α : Spec B ⟶ Spec B''` (`GroupScheme.baseChange`) to `G'`. Surjectivity of
`Spec B → Spec A` and of `Spec B'' → Spec A` is not assumed here.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I, Panoramas
et Synthèses 42–43, SMF, 2014. It is registered as `conrad-2014-reductive-group-schemes`,
file `Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are
the printed page numbers, which agree with the one-based PDF page numbers.

- Proposition 6.4.4, p.232: "Let G → S be a fiberwise nontrivial semisimple group with
  simply connected fibers over a non-empty scheme S. There is a finite étale cover
  S′ → S and a semisimple group G′ → S′ with simply connected and absolutely simple fibers
  such that G is S-isomorphic to the Weil restriction R_{S′/S}(G′). The pair (S′/S, G′) is
  uniquely determined up to unique S-isomorphism in the following sense: if (S′′/S, G′′)
  is another such pair then every S-group isomorphism R_{S′/S}(G′) ≃ R_{S′′/S}(G′′) arises
  from a unique pair (α, f) consisting of an S-isomorphism α : S′ ≃ S′′ and group
  isomorphism f : G′ ≃ G′′ over α."
- The proof, pp.232–233, reduces étale-locally to the split case, decomposes the simply
  connected root datum into irreducible factors, and uses the Existence and Isomorphism
  Theorems for existence; for uniqueness it reduces to a strictly henselian local base and
  uses conjugacy of maximal tori (Theorem 3.2.6) and the decomposition theorem over a field
  (Theorem 5.1.19).
- Definition 3.1.1, p.81: a reductive (resp. semisimple) `S`-group is a smooth `S`-affine
  `S`-group whose geometric fibres are connected reductive (resp. connected semisimple).
- Exercise 6.5.2 context, p.235: "A semisimple group over a non-empty scheme S is simply
  connected when its geometric fibers are simply connected."
- p.149: "A connected semisimple group H over a field k is k-simple if H ≠ 1 and H has no
  nontrivial normal smooth connected proper k-subgroup, and absolutely simple if H_K is
  K-simple for some (equivalently, any) algebraically closed extension field K/k."

## Derivation from the source

The proposition specializes Proposition 6.4.4 to affine bases and weakens its uniqueness
clause. Its terms translate as follows.

- **Semisimple with simply connected fibres.** Conrad's semisimple `S`-group is a
  reductive `S`-group whose geometric fibres are semisimple (Definition 3.1.1). The
  Library's `IsSimplyConnected` contains `IsSemisimple` as a field, so hypotheses 1 and 2
  together say that `G` is semisimple with simply connected geometric fibres. Over an
  algebraically closed field, Conrad's simple connectedness (the root datum is simply
  connected, Definition 1.3.11, p.29) and the Library's (every central isogeny from a
  semisimple group is an isomorphism) are the classical equivalent definitions; Conrad
  records the equivalence in the text before Exercise 6.5.2, p.235, as a consequence of
  the Existence and Isomorphism Theorems. The same reading applies to `G'`.
- **Fibrewise nontrivial.** Conrad's fibres `G_s ≠ 1` are nontrivial exactly when the
  geometric fibres are; hypothesis 3 is nontriviality of the geometric fibres, as explained
  above.
- **Absolutely simple fibres.** A fibre `G'_{s'}` is absolutely simple when its base change
  to an algebraic closure is simple in the sense quoted from p.149. Over the algebraically
  closed field `κ(s')^alg` the Library's `IsAlmostSimple` says: semisimple, not
  commutative, and every smooth connected normal closed subgroup is trivial or everything.
  For a connected semisimple group, non-commutativity is equivalent to `H ≠ 1`, since a
  commutative connected semisimple group is trivial. So `IsAlmostSimple` of the geometric
  fibre is absolute simplicity of the fibre. (`IsAlmostSimple` follows Milne's
  Definition 19.7 with its official p.399 correction, as recorded in
  [`Reductive.AlmostSimple`](AlmostSimple.md).)
- **Finite étale cover.** For `S = Spec A`, a finite étale `S′ → S` is `Spec B` for a finite
  étale `A`-algebra `B`: `Module.Finite A B` and `Algebra.Etale A B`. A cover is in
  addition surjective. A finite étale algebra is finitely presented and flat, hence
  projective, so `Module.Projective A B` adds no condition; it is required by
  `AffineWeil.groupScheme`.
- **Witnesses for the Weil restriction.** A reductive `G'` over the affine scheme `Spec B`
  has an affine structure morphism, so `G'.X.left` is affine; and it is smooth, hence
  locally of finite type. So the witnesses `IsAffine G'.X.left` and
  `LocallyOfFiniteType G'.X.hom` add no condition beyond `IsReductive G'`. In the
  uniqueness clause they are instance arguments for the same reason.
- **Weil restriction.** `AffineWeil.groupScheme A B G'` represents `T ↦ G'(B ⊗_A T)`, which
  is Conrad's `R_{S′/S}(G′)`.
- **Uniqueness.** Conrad asserts that every isomorphism `R_{S′/S}(G′) ≃ R_{S′′/S}(G′′)`
  arises from a unique pair `(α, f)`. The present clause asserts less: when both Weil
  restrictions are isomorphic to `G`, there is some pair `(α, f)` with `α` an
  `S`-isomorphism `Spec B ≅ Spec B''` (an `A`-algebra isomorphism `B'' ≃ B`) and `f` an
  isomorphism from `G'` onto `G''` over `α`, written as an isomorphism between `G'` and the
  base change of `G''` along `Spec α`. It does not assert that a given isomorphism of Weil
  restrictions comes from `(α, f)`, nor that the pair is unique. The source's uniqueness
  quantifies over pairs as in its existence clause, with `S′ → S` a cover; this clause drops
  that surjectivity, a weakening of its hypotheses. Nothing is lost, since under the
  remaining hypotheses surjectivity follows from hypothesis 3: over a point `s`, the
  geometric fibre of `R_{B/A}(G')` is a product of geometric fibres of `G'` indexed by the
  geometric points of `Spec B` over `s`, which is trivial when there are none.
- **Affine base.** `AffineWeil.groupScheme` is constructed only over an affine base
  `Spec A`, so the statement is restricted to affine bases. The general-base statement is
  not a formal consequence of this one: the pairs found over the members of an affine open
  cover are glued in the source by the full uniqueness clause, which is not stated here. So
  this proposition is a specialization of the source's statement, not a reformulation of
  it.
- **Empty base.** Non-emptiness of `S` is not assumed. For `A = 0` the proposition holds
  trivially: hypotheses 2 and 3 are vacuous, `B = 0` gives the existence clause (every
  scheme over the empty scheme is empty, so all group schemes over `Spec 0` are
  isomorphic), and in the uniqueness clause `B = B'' = 0`.

## Scope

All rings are in universe `u`. The proposition does not state:

- the full uniqueness of Proposition 6.4.4 (every isomorphism of Weil restrictions arises
  from a unique pair `(α, f)`), or the resulting canonicity of `(B, G')`;
- the statement over a non-affine base scheme;
- Remark 6.4.5 (the adjoint analogue) or Example 6.4.6 (the field case).

## Relation to the Library

- [`SimplyConnected.AlmostSimpleWeilRestrictionStatement`](../SimplyConnected/AlmostSimpleWeilRestrictionStatement.md)
  (Worker 1783; Borel–Tits 6.21(ii), Milne Theorem 24.3) records the field case for an
  almost simple `G` over a field `k`: `G ≅ R_{K/k}(G')` for a finite separable field
  extension `K` and an absolutely almost simple simply connected `G'`, with no uniqueness.
  Over a field `k = A`, the present existence clause has a finite étale `k`-algebra `B`, a
  product of finite separable fields, and covers semisimple simply connected `G` that need
  not be almost simple over `k` (Conrad, Example 6.4.6). This module proves no relation
  between the two propositions.
- The Library's split-group statements over a general base, for example
  [`Reductive.AffineSplitIsomorphismTheoremStatement`](AffineSplitIsomorphismTheoremStatement.md)
  (the Isomorphism Theorem over an affine base) and
  [`Reductive.EtaleLocalSplitStatement`](EtaleLocalSplitStatement.md) (étale-local
  splitting), record ingredients of the source's proof. This module does not use them.
