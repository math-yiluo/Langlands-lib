# Statement: homomorphisms with commutative image from a semisimple Weil restriction

`Langlands.GroupScheme.WeilAbelianImageTrivialityStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports
[`Reductive.Semisimple`](Semisimple.md) (for `IsSemisimple` and, through it, `IsReductive`
and `geometricFiber` from [`Reductive.Basic`](Basic.md)) and
[`AffineWeilRestriction`](../AffineWeilRestriction.md) (for the Weil restriction
`AffineWeil.groupScheme`).

It is a derived statement: the perfectness of the Weil restriction `H = R_{B/A}(G')` of a
group with semisimple geometric fibres, in the form "every homomorphism from `H`, over any
base change, whose values commute with each other is trivial". It is intended, together
with
[`Reductive.RelativeAlmostSimpleNormalIdempotentStatement`](RelativeAlmostSimpleNormalIdempotentStatement.md),
as the input of a formal deduction of
[`Reductive.WeilFactorIdempotentRigidityStatement`](WeilFactorIdempotentRigidityStatement.md).

## Statement and quantifiers

The proposition quantifies over

- commutative rings `A B : Type u` with an `A`-algebra structure on `B` such that `B` is a
  finite (`Module.Finite A B`), projective (`Module.Projective A B`) and étale
  (`Algebra.Etale A B`) `A`-algebra;
- a group scheme `G' : GroupScheme (Spec B)` with instance witnesses
  `IsAffine G'.X.left` and `LocallyOfFiniteType G'.X.hom` (needed to form
  `H = AffineWeil.groupScheme A B G'`);

and assumes

1. `IsReductive G'` ([`Reductive.Basic`](Basic.md));
2. for every point `s'` of `Spec B`, `IsSemisimple (geometricFiber G' s')`
   ([`Reductive.Semisimple`](Semisimple.md)): every geometric fibre is connected reductive
   with finite centre.

Then it quantifies over

- a group scheme `M : GroupScheme (Spec A)` (arbitrary; no hypothesis on `M`);
- an `A`-algebra `T : CommAlgCat (CommRingCat.of A)`;
- a natural transformation `c` from `Under.forget T ⋙ H.affinePointFunctor` to
  `Under.forget T ⋙ M.affinePointFunctor`. Objects `X : Under T` are `T`-algebras, and the
  functors send `X` to the groups `H(X.right)` and `M(X.right)`; so `c` is a homomorphism
  of group functors `H_T → M_T` on `T`-algebras.

It assumes

3. for every `X : Under T` and points `x y` of `H(X.right)`,
   `Commute (c.app X x) (c.app X y)`: the values of `c` over each `T`-algebra commute with
   each other.

The conclusion is that `c.app X x = 1` for every `X : Under T` and every point `x` of
`H(X.right)`.

## Mathematical content and correctness

Assumption 3 says that `c` kills every commutator `x y x⁻¹ y⁻¹` of points of `H` over each
`T`-algebra, so the statement follows once every point of `H` is, locally for the fppf
topology, a product of commutators, because the point functor of the scheme `M` is an fppf
sheaf. For a reductive group with semisimple geometric fibres over any base this local
perfectness is
`Langlands.GroupScheme.relativeSemisimpleFppfPerfect` in
[`Reductive.RelativeSemisimpleFppfPerfectProof`](RelativeSemisimpleFppfPerfectProof.md)
(proof of `RelativeSemisimpleFppfPerfectStatement` in
[`RelativeDerivedInputs`](RelativeDerivedInputs.md)). For `H`, étale-locally on `Spec X`
the finite étale algebra `B ⊗_A X` splits as a finite product of copies of `X`, and then
`H_X` is the product of the corresponding fibres of `G'`, each a reductive group with
semisimple geometric fibres; a point of a product is a product of points of the factors.
The statement fails without the semisimplicity hypothesis: for `G' = 𝔾_m` and `B = A`,
the identity `c` of `𝔾_m` has commuting values and is not trivial.

Over an algebraically closed field `k`, `H_k = ∏ G'_i` is a product of semisimple groups,
which are perfect (equal to their derived subgroups), so every homomorphism from `H_k` to
a group with commutative image is trivial.

## Source and provenance

Provenance: derived. The statement is not stated in this form in the literature. It is the
perfectness of semisimple groups used in the uniqueness argument of

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I,
Panoramas et Synthèses 42–43, SMF, 2014, registered as
`conrad-2014-reductive-group-schemes` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`), printed page
numbers equal to one-based PDF page numbers:

- Proposition 6.4.4, p.232, and its proof, pp.232–233 (an isomorphism of products of
  absolutely simple groups permutes the factors);
- Theorem 5.3.1 and its proof, pp.160–163, especially the final paragraph on p.163 (the
  semisimple fppf-perfectness input formalized in `RelativeSemisimpleFppfPerfectStatement`).

In the formal deduction of `WeilFactorIdempotentRigidityStatement`, it is applied with
`M = H` to the homomorphism `x ↦ f·ψ((1 - f)·x)` (component notation for factor
projections) attached to a normal idempotent endomorphism `ψ` and an idempotent `f` of
`B ⊗_A T`. Normality of `ψ` makes the values of this homomorphism central in the
`f`-component, so they commute; the conclusion that it is trivial shows that `ψ` commutes
with the factor projections. Without this input, `ψ(x, y) = (1, χ(x) y)` with a nontrivial
homomorphism `χ` from the first factor to the centre of the second would be a normal
idempotent endomorphism that is not a factor projection.

## Scope

All rings are in universe `u`; the base is affine. Only homomorphisms of group functors on
`T`-algebras (natural in `X : Under T`) are considered.
