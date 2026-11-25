# Statement: normal idempotent endomorphisms of a Weil restriction of almost simple groups

`Langlands.GroupScheme.WeilFactorIdempotentRigidityStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports
[`Reductive.AlmostSimple`](AlmostSimple.md) (for `IsAlmostSimple` and, through it,
`IsReductive` and `geometricFiber` from [`Reductive.Basic`](Basic.md)) and
[`AffineWeilRestriction`](../AffineWeilRestriction.md) (for the Weil restriction
`AffineWeil.groupScheme` and its point description `AffineWeil.pointsEquiv`).

It is a derived statement, written as the geometric input of the uniqueness clause of
[`Reductive.AffineSimplyConnectedWeilRestrictionStatement`](AffineSimplyConnectedWeilRestrictionStatement.md)
(Conrad, *Reductive group schemes*, Proposition 6.4.4). Informally: if `G'` has almost
simple geometric fibres, then the only normal idempotent endomorphisms of
`H = R_{B/A}(G')`, over any base change `T` of `A`, are the projections onto the
"sub-products" `R_{(B ⊗ T) e / T}`, one for each idempotent `e` of `B ⊗_A T`.

## Statement and quantifiers

The proposition quantifies over

- commutative rings `A B : Type u` with an `A`-algebra structure on `B` such that `B` is a
  finite (`Module.Finite A B`), projective (`Module.Projective A B`) and étale
  (`Algebra.Etale A B`) `A`-algebra;
- a group scheme `G' : GroupScheme (Spec B)` with instance witnesses
  `IsAffine G'.X.left` and `LocallyOfFiniteType G'.X.hom` (needed to form
  `AffineWeil.groupScheme A B G'`, written `H` below);

and assumes

1. `IsReductive G'` ([`Reductive.Basic`](Basic.md));
2. for every point `s'` of `Spec B`, `IsAlmostSimple (geometricFiber G' s')`
   ([`Reductive.AlmostSimple`](AlmostSimple.md)): every geometric fibre is semisimple,
   noncommutative, and has no smooth connected closed normal subgroups other than `1` and
   itself.

Then it quantifies over

- an `A`-algebra `T : CommAlgCat (CommRingCat.of A)`;
- a natural transformation `ψ` from the functor
  `Under.forget T ⋙ H.affinePointFunctor` to itself. Objects `X : Under T` are
  `A`-algebras `X.right` with an `A`-algebra map `X.hom : T ⟶ X.right`, that is,
  `T`-algebras; the functor sends `X` to the group `H(X.right)` of points of `H` with
  coefficients in `X.right`. So `ψ` is an endomorphism of the group functor of `H` restricted
  to `T`-algebras, i.e. an endomorphism of the base change `H_T` over `Spec T`.

It assumes

3. `ψ ≫ ψ = ψ` (idempotence);
4. for every `X : Under T` and points `h x` of `H(X.right)`,
   `ψ.app X (h * x * h⁻¹) = h * ψ.app X x * h⁻¹` (normality: `ψ` commutes with every
   inner automorphism, over every `T`-algebra).

The conclusion is that there is exactly one `e : B ⊗[A] T` such that `e` is idempotent and,
for every `X : Under T` and every point `x` of `H(X.right)`, writing

- `e'` for the image of `e` in `B ⊗[A] X.right` under
  `Algebra.TensorProduct.lTensor B X.hom.hom`,
- `g = AffineWeil.pointsEquiv A B G' X.right (ψ.app X x)` and
  `g₀ = AffineWeil.pointsEquiv A B G' X.right x`, the points of `G'` with coefficients in
  `B ⊗[A] X.right` corresponding to `ψ(x)` and `x`,

the image of `g` under the quotient map `B ⊗[A] X.right → (B ⊗[A] X.right) ⧸ (1 - e')`
equals the image of `g₀`, and the image of `g` under the quotient map
`B ⊗[A] X.right → (B ⊗[A] X.right) ⧸ (e')` is `1`. Images of points are taken with
`G'.affinePointMap` along the `B`-algebra quotient maps `Ideal.Quotient.mkₐ B`.

Since `B ⊗ X = (B ⊗ X)/(1 - e') × (B ⊗ X)/(e')` and `G'` is affine, a point of `G'` over
`B ⊗ X` is determined by its two images; so the conclusion says that `ψ` is the map
"keep the `e`-component, kill the `(1 - e)`-component", and that this `e` is unique.

## Mathematical content and correctness

Over an algebraically closed field `k` (`T = k`), `B ⊗_A k = k^n` and
`H_k = G'_1 × ⋯ × G'_n` with almost simple factors `G'_i` (the geometric fibres of `G'`
at the `n` points of `Spec (B ⊗ k)`). Let `ψ` be a normal idempotent endomorphism. For
`x ∈ G'_i` and `h ∈ G'_j`, `j ≠ i`, normality gives `ψ(x) = h ψ(x) h⁻¹`, so `ψ(G'_i)` lies
in `G'_i × ∏_{j ≠ i} Z(G'_j)`; as `G'_i` is smooth and connected and the centres are finite,
`ψ(G'_i) ⊆ G'_i`. The image of `ψ|G'_i` is a smooth connected normal subgroup of the almost
simple `G'_i`, so it is `1` or `G'_i`; in the second case the idempotent surjection
`ψ|G'_i` is the identity. Hence `ψ` is the projection onto the factors in a subset of
`{1, …, n}`, i.e. onto the component of an idempotent `e ∈ k^n`; `e` is unique because
the factors are nontrivial. Over a general `T` the statement asserts that these idempotents
glue: this is the rigidity of normal idempotent endomorphisms in families. At first order
it is automatic, since an idempotent deformation `id + εc` or `1 + εc` of `id` or `1`
satisfies `2εc = εc`, resp. `εc = 0`.

## Source and provenance

Provenance: derived. The statement is not stated in this form in the literature. It is
formulated as the intrinsic part of the uniqueness argument of

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I,
Panoramas et Synthèses 42–43, SMF, 2014, registered as
`conrad-2014-reductive-group-schemes` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`), printed page
numbers equal to one-based PDF page numbers:

- Proposition 6.4.4, p.232: an `S`-group isomorphism `R_{S′/S}(G′) ≃ R_{S′′/S}(G′′)` of
  Weil restrictions of semisimple groups with simply connected absolutely simple fibres
  "arises from a unique pair (α, f)".
- Its proof, pp.232–233: étale-locally `S′ = ∐ S`, and an isomorphism
  `∏ G′_i ≃ ∏ G′′_j` must "permute these factors according to some bijection
  α : I ≃ J and carry (G′_i)_0 isomorphically onto (G′′_{α(i)})_0", by the identification
  of the absolutely simple factors with the simple factors of the product over a field
  (Theorem 5.1.19).

The correspondence is as follows. Over a base where `S′ = ∐_{i ∈ I} S`, idempotents of
`B ⊗ T` are subsets of `I` (locally on `Spec T`), and the projections of `∏ G′_i` onto the
sub-products `∏_{i ∈ J} G′_i` are exactly the normal idempotent endomorphisms; an
isomorphism of Weil restrictions conjugates normal idempotent endomorphisms to normal
idempotent endomorphisms, so it induces the permutation `α` of the factors. Formulating
this with idempotents of `B ⊗_A T` for all `T` makes it intrinsic, so that no étale
localization or strictly henselian base is needed in the formal deduction of the
uniqueness clause from it. The statement drops the simply connected hypothesis of
Proposition 6.4.4, which the argument above does not use.

## Scope

All rings are in universe `u`; the base is affine. The proposition does not state the
uniqueness clause of Proposition 6.4.4 itself, nor any description of non-idempotent or
non-normal endomorphisms. It is intended as the input of a formal deduction of the
uniqueness clause of `AffineSimplyConnectedWeilRestrictionStatement`.
