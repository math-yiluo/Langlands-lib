# The split-radical product description of pseudo-parabolics

This module states the proposition
`Langlands.GroupScheme.PseudoParabolicSplitRadicalProductStatement.{u}`. It is
the first product equality of Proposition 2.2.4, stated on every relative
scheme test at arbitrary universe `u`. The module contains only this
`Prop`-valued definition. It proves nothing.

## Original source

The source is Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition
(2015), registered as `conrad-gabber-prasad-2015-pseudo-reductive`, SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`. The
readable original is
`/home/taskhub/central-library/Conrad-Gabber-Prasad--Pseudo-reductive groups (book, 2nd edition)--2015.pdf`.
Proposition 2.2.4 is stated at the bottom of printed p.63 (one-based PDF
p.89). Its proof is on printed p.64 (PDF p.90). The proposition reads:

> For any smooth connected affine k-group G and k-homomorphism
> λ : GL₁ → G, we have P_G(λ)R_{u,k}(G) = P_G(λ)R_{us,k}(G) and
> P_G(λ) = P′_G(λ) inside of G.

The present statement covers only the first equality. The current public notes
contain no errata note for this source.

## Correspondence

The definition quantifies over the following data:

- every field `k : Type u`, with `B = Spec (CommRingCat.of k)`;
- every actual group scheme `G` over `B` with instance hypotheses
  `[Smooth G.X.hom]`, `[IsAffineHom G.X.hom]` and `[ConnectedSpace G.X.left]`.
  These are CGP's "smooth connected affine k-group" and match the ambient
  hypotheses of `IsPseudoParabolicSubgroup`;
- every pair of actual group schemes `U, V` over `B` and homomorphisms
  `j : U ⟶ G` and `n : V ⟶ G` with `IsUnipotentRadical j` and
  `IsSplitUnipotentRadical n`. Their all-test images
  `SubgroupFunctor.range j` and `SubgroupFunctor.range n` play the roles of
  `R_{u,k}(G)` and `R_{us,k}(G)`;
- every actual cocharacter `χ : (Gm B).toGrp ⟶ G`, which is the source's `λ`.
  `Dynamic.parabolic χ` is the existing dynamic subgroup functor `P_G(λ)`;
- every relative scheme `T : Over B` and every point `x : T ⟶ G.X`.

The definition then asserts

```lean
SubgroupFunctor.FppfLocallyInProduct
  (Dynamic.parabolic χ) (SubgroupFunctor.range j) x ↔
SubgroupFunctor.FppfLocallyInProduct
  (Dynamic.parabolic χ) (SubgroupFunctor.range n) x
```

which is the equality `P_G(λ)R_{u,k}(G) = P_G(λ)R_{us,k}(G)`.

## The two radicals

The two radical predicates come from `Langlands.GroupScheme.Reductive.UnipotentRadical`
and are used unchanged.

- `IsUnipotentRadical j` is the ground-field radical `R_{u,k}(G)`. It says that
  `j` is a closed subgroup, `U` is smooth, connected and unipotent, and the
  image of `j` is normal. It also says that this image contains the image of
  every smooth connected unipotent normal closed subgroup over `k`.
- `IsSplitUnipotentRadical n` is the split ground-field radical `R_{us,k}(G)`,
  defined in CGP on p.63 as "the maximal k-split smooth connected unipotent
  normal k-subgroup". It has the same fields together with
  `RelativeRoot.IsSplitUnipotent V`, the existing finite-series split
  unipotence predicate. Its greatestness ranges only over competitors that
  are also split.

These are different predicates. The source proof notes on p.64, citing
Corollary B.3.5, that `R_{us,k}(G) = 1` means exactly that `R_{u,k}(G)` is
`k`-wound, so the two radicals need not agree. Neither radical is replaced by
the other here, and neither is replaced by a geometric radical formed after
base change to an algebraic closure. The Library
separately proves `IsSplitUnipotentRadical.range_le_unipotentRadical`, which
says that the split image lies in the ordinary image. Combined with
`SubgroupFunctor.FppfLocallyInProduct.mono`, it gives the right-to-left
implication. The left-to-right implication carries the content of the
proposition.

## The all-test fppf interpretation

Both products use the unchanged predicate
`SubgroupFunctor.FppfLocallyInProduct` from
`Langlands.GroupScheme.SubgroupFunctor.FppfProduct`.
`FppfLocallyInProduct F N x` holds when there are a relative scheme `W` and a
map `w : W ⟶ T` with the following properties:

- the underlying scheme map of `w` is flat, surjective and locally of finite
  presentation;
- there are points `p, m : W ⟶ G.X` with `p` in `F.carrier W` and `m` in
  `N.carrier W`, and `w ≫ x = p * m`, in this order.

The Library's pseudo-parabolic predicate `IsPseudoParabolicSubgroup` uses the
same internal fppf-image formulation of a subgroup product, through
`IsFppfProduct`. The equivalence is required for every test `T` and every
point `x`. The tests include nonaffine and nonreduced schemes, and the
statement is not restricted to rational points or geometric points. Neither
side requires `x` to factor on `T` itself. The statement does not assert that
either product is represented by a closed subgroup.

## Scope

The quantification includes every field: imperfect and finite fields and
fields of every characteristic. No reductivity, pseudo-reductivity,
perfectness or infinitude is assumed. No theorem-valued premise is added.
The definition takes the radical representatives `j` and `n` as data. It
asserts neither the existence of radicals nor the existence of product
representatives or local factorizations.

The definition is a statement target only. It supplies no proof. It does not
assert the second equality `P_G(λ) = P′_G(λ)` of Proposition 2.2.4, which
concerns the subgroup generated by smooth connected subgroups with
nonnegative Lie weights. It makes no quotient, rational-lifting or
local-section claim. The source proof divides by `R_{us,k}(G)` using
Corollary 2.1.9 and Corollary B.3.5. It then uses Proposition B.4.4, which
says that a torus acts trivially on a `k`-wound smooth connected unipotent
group. These inputs remain obligations for a proof of this statement.
