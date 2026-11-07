# Statement: the Isomorphism Theorem for split reductive groups over a local ring

Authors: Worker 1398.

This module contains one `Prop`-valued statement,
`Langlands.GroupScheme.LocalSplitIsomorphismTheoremStatement`. The Lean file
only defines the proposition. It proves nothing and adds no other
definitions, theorems or axioms. It imports
[`Reductive.FibrewiseRootDatum`](FibrewiseRootDatum.md), which supplies the
predicate `IsFibrewiseRootDatumOf`, and [`Reductive.Basic`](Basic.md), which
supplies `IsReductive`.

## Binders and hypotheses

The universe `u` is arbitrary. The proposition quantifies over:

- every commutative local ring `R : Type u` (`IsLocalRing R`). There is no
  Noetherian, domain, Henselian or characteristic hypothesis;
- group schemes `G H` over `Spec (CommRingCat.of R)` with affine structure
  morphisms (`[IsAffineHom G.X.hom]`, `[IsAffineHom H.X.hom]`, needed to state
  `IsFibrewiseRootDatumOf`) and with `IsReductive G` and `IsReductive H`.
  This published predicate says that the structure morphism is smooth and
  affine and that every geometric fibre is pseudo-reductive, in particular
  connected. So the instance arguments are implied by the reductivity
  hypotheses and add no restriction;
- finite types `I I' : Type u` and homomorphisms
  `i : splitTorus (Spec R) I ⟶ G` and `i' : splitTorus (Spec R) I' ⟶ H` from
  the coordinate split tori;
- the hypotheses `IsClosedSubgroup i` and `IsClosedSubgroup i'`: the
  underlying scheme maps are closed immersions;
- for every point `s` of `Spec R`, the hypothesis that the pullback of `i`
  along `Spec κ(s) → Spec R` satisfies `IsMaximalTorus` (its source is a
  torus, it is a closed subgroup, and every factorization through a closed
  torus of `G_{κ(s)}` has an isomorphism as its first map), and the same for
  `i'` in `H`;
- types `J J' : Type u` and Mathlib root data
  `P : RootDatum J (I → ℤ) (I → ℤ)` and `Q : RootDatum J' (I' → ℤ) (I' → ℤ)`
  with `IsFibrewiseRootDatumOf I G i P` and
  `IsFibrewiseRootDatumOf I' H i' Q`. By
  [`Reductive.FibrewiseRootDatum`](FibrewiseRootDatum.md), `P` is finite and
  reduced and its realization is the actual root datum (`IsRootDatumOf`) of
  the base change of `i` to every field `k : Type u` over `R`; likewise for
  `Q`, `H` and `i'`;
- an equivalence of root pairings `RootPairing.Equiv P Q`: a linear
  equivalence of the character lattices `I → ℤ ≃ I' → ℤ`, a contravariant
  linear equivalence of the cocharacter lattices compatible with the
  pairings, and a bijection `J ≃ J'` carrying roots to roots and coroots to
  coroots. This is an isomorphism of root data in the usual sense.

The torus hypotheses on `i` and `i'` are those of
[`Reductive.LocalSplitRootDatumExistenceStatement`](LocalSplitRootDatumExistenceStatement.md),
whose conclusion supplies `P` and `Q`.

## Conclusion

`Nonempty (G ≅ H)`: `G` and `H` are isomorphic as group schemes over
`Spec R`. This is an assertion about isomorphism classes; the isomorphism is
not required to carry `i` to `i'` or to induce the given equivalence of root
data.

## Necessity of the maximality hypotheses

Without residue-fibre maximality the statement would be false. Over any
local ring, take `G = GL_2`, `H` the trivial group, `I = I'` empty and `i`,
`i'` the inclusions of the trivial torus. The trivial torus acts trivially on
`Lie G`, so both fibrewise root data are the empty root datum on the zero
lattice, and they are equivalent; but `GL_2` is not isomorphic to the trivial
group. In this example the trivial torus of `GL_2` is not maximal on any
fibre, so it is excluded by the hypotheses.

## Provenance

The proposition is a derived consequence of Brian Conrad, *Reductive group
schemes* (2014), registered as `conrad-2014-reductive-group-schemes`, source
SHA256 `1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
It is stated here, rather than quoted, because it is the second of the two
steps into which
[`Reductive.LocalSplitGeometricIsoStatement`](LocalSplitGeometricIsoStatement.md)
is split. The source route is:

- Definition 3.2.1 (p.91) and Remark A.1.2 (p.267), resting on
  Grothendieck's Theorem A.1.1, make the residue-fibre maximal tori maximal
  tori of `G` and `H` over `Spec R` in Conrad's sense.
- Definition 5.1.1 (p.136): with `M = I → ℤ` and `M' = I' → ℤ`, the
  fibrewise root data `P` and `Q` say that the nontrivial weights on the Lie
  algebras and the coroots are the constant sections given by the roots and
  coroots of `P` and `Q`. Each root space is a finitely generated projective
  `R`-module of constant rank 1, hence free because `R` is local. So
  `(G, i, M)` and `(H, i', M')` are split reductive groups, and their root
  data `R(G, T, M)` and `R(H, T', M')` (Proposition 5.1.6, p.138) are `P`
  and `Q`, read on any fibre (`Spec R` is non-empty).
- Theorem 6.1.17 (Isomorphism Theorem, p.197), over the non-empty scheme
  `Spec R`, states that every isomorphism of root data
  `R(G', T', M') ≃ R(G, T, M)` arises from an isomorphism of split groups.
  Applied to the isomorphism of root data given by the equivalence
  `P ≃ Q`, it gives an isomorphism between `G` and `H`.

The listed results justify the statement; they are not imported Lean
proofs. The module proves none of them.
