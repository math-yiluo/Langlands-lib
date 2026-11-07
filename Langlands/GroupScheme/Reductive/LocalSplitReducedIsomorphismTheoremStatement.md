# Statement: the Isomorphism Theorem for split reductive groups over a reduced local ring

Authors: Worker 712 and Worker 1398. Worker 1398 asked for this statement in exactly this form
and wrote the Markdown of
[`Reductive.LocalSplitIsomorphismTheoremStatement`](LocalSplitIsomorphismTheoremStatement.md),
which this file adapts.

This module contains one `Prop`-valued statement,
`Langlands.GroupScheme.LocalSplitReducedIsomorphismTheoremStatement`. The
Lean file only defines the proposition. It proves nothing and adds no other
definitions, theorems or axioms. It imports
[`Reductive.FibrewiseRootDatum`](FibrewiseRootDatum.md), which supplies the
predicate `IsFibrewiseRootDatumOf`, and [`Reductive.Basic`](Basic.md), which
supplies `IsReductive`.

## Relation to the general statement

The proposition is the published
[`LocalSplitIsomorphismTheoremStatement`](LocalSplitIsomorphismTheoremStatement.md)
with one extra instance binder, `[IsReduced R]`, inserted right after
`[IsLocalRing R]`. Every other binder, hypothesis and the conclusion are
copied verbatim. So `LocalSplitIsomorphismTheoremStatement` implies this
proposition at once, and this proposition is the special case of it for
reduced local rings. This module neither proves nor uses that implication. It
does not import the general statement and leaves it untouched.

## Binders and hypotheses

The universe `u` is arbitrary. The proposition quantifies over:

- every commutative local ring `R : Type u` (`IsLocalRing R`) that is
  reduced (`IsReduced R`: `R` has no nonzero nilpotent elements). There is no
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

## Conclusion

`Nonempty (G ≅ H)`: `G` and `H` are isomorphic as group schemes over
`Spec R`. This is an assertion about isomorphism classes; the isomorphism is
not required to carry `i` to `i'` or to induce the given equivalence of root
data.

## Why reducedness is assumed

The general statement, for every local ring, is Conrad's Isomorphism Theorem
over `Spec R`. Its proof for a non-reduced base needs the integral theory of
generators and relations for split reductive groups: Conrad, §6.2,
Theorem 6.2.1 (p.198, after [SGA3, XXIII, 2.1]), Theorem 6.2.4 (p.201) and
Corollary 6.2.7 (p.204), with the rank-two computations of pp.204–208. Over a
non-reduced base the group laws are not determined by their values at
geometric points, so this theory cannot be bypassed there. None of it is in
the Library yet.

Over a reduced base, a smooth `R`-scheme is reduced. Two morphisms from a
reduced scheme into a separated scheme agree as soon as they agree at all
points with values in algebraically closed fields. So the compatibility of the
group laws of `G` and `H` on a common open cell can be checked over
algebraically closed fields, where the field Isomorphism Theorem applies.
This shorter route needs only the integral open-cell structure over `R`, not
§6.2. The intended consumer, a statement over strictly Henselian local
domains, needs only reduced local rings, since every domain is reduced. The
general `LocalSplitIsomorphismTheoremStatement` stays an open Library
statement for a later formalization of §6.2.

The extra hypothesis does not make the proposition vacuous: every field is a
reduced local ring.

## Provenance

The proposition is a derived consequence of Brian Conrad, *Reductive group
schemes* (2014), registered as `conrad-2014-reductive-group-schemes`, source
SHA256 `1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
It is the special case for reduced local rings of the general statement, whose
source route is the following:

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

The reducedness hypothesis is an internal restriction, chosen for the reason
given above; Conrad's theorem holds without it. The listed results justify
the statement; they are not imported Lean proofs. The module proves none of
them.
