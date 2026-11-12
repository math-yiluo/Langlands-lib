# A uniform upper bound for point counts in families over the integers

Author: Worker 69.

This module states the upper-bound half of the Lang–Weil estimates, uniformly in a family over
the integers and pointwise in the fibre dimension. It is an input of the Library's Lang–Weil
route to Conrad's Lemma 4.6. The module contains no proof.

## The statement

`FamilyPointUpperBoundStatement` says: let `S` and `X` be schemes in a universe `u` and
`f : X ⟶ S` a morphism such that `S` is of finite type over `ℤ` (the map
`specULiftZIsTerminal.from S` to `Spec (ULift ℤ)` is locally of finite type and `S` is
quasi-compact) and `f` is locally of finite type and quasi-compact. Then there is a real number
`C > 0` with the following property. For every finite field `κ` (a type in universe `u`), every
morphism `s : Spec κ ⟶ S` and every `e : ℕ` such that the fibre `f.fiber y` over the point
`y = s (closedPoint κ)` of `S` (the image of the unique point of `Spec κ`) has topological Krull
dimension at most `e`, the number of morphisms `x : Spec κ ⟶ X` with `x ≫ f = s` is at most
`C · (#κ) ^ e`, where `#κ = Nat.card κ`.

There is no hypothesis on the fibres of `f`: the dimension condition is imposed only at the
`κ`-point considered, and the constant `C` does not depend on `κ`, `s` or `e`. An empty fibre has
dimension `⊥` and satisfies the condition for every `e`; then there are no points over `s`.

## Relation to the sources

- Serge Lang and André Weil, *Number of points of varieties in finite fields*, Amer. J. Math.
  76 (1954), 819–827 (registered source `lang-weil-1954-number-of-points`; PDF page = printed
  page − 817), Lemma 1, printed p.820 (PDF p.3): "There exists a constant `A_1(n, d, r)`
  depending only on `n, d, r` such that for any positive cycle `Z` in `P^n` of degree `d`,
  dimension `r`, and rational over `k`, we have `N_Z ≤ A_1 q^r`." Here `N_Z` is the number of
  points of the support of `Z` rational over the finite field `k` with `q` elements.
- Terence Tao, *The Lang–Weil bound* (blog post, 31 August 2012; registered source
  `tao-2012-lang-weil-bound`), Lemma 1 (Schwarz–Zippel type bound): for a variety `V` of
  complexity at most `M` over the algebraic closure of a finite field `F`,
  `|V(F)| ≪_M |F|^{dim V}`. Tao notes that, in this qualitative form, the bound goes back at least
  to Lemma 1 of Lang and Weil.

Provenance: derived. The statement transfers Lang–Weil's Lemma 1 (constants depending only on
`n, d, r`) and Tao's Lemma 1 (constants depending only on the complexity) to a family
`f : X ⟶ S` of finite type over a base of finite type over `ℤ`, as in Conrad's Lemma 4.6
(printed p.12 of `conrad-2011-weil-grothendieck-adelic-points`). Uniformity comes from finitely
many affine charts, whose fibres are cut out by polynomials of bounded number and degree. The
fibre
`X ×_S Spec κ` over `s` has the same dimension as the fibre `f.fiber y` over the residue field of
`y`, because dimension does not change under field extension. Its `κ`-points are the morphisms
`x` counted above.

## Use in the Library's route

The bound is used in `FamilyLangWeilCurveStatement` for the finitely many exceptional points of a
birational plane model (`e = 0`) and for small fields, and in `FamilyLangWeilSlicingStatement`
for the hyperplanes whose sections fail to be geometrically irreducible and for the slices of
smaller dimension. The reduction of the algebraic-space form of Conrad's Lemma 4.6 uses it for
lower-dimensional strata.

## Status

Open. A proof is to be supplied through its own focused proof task. A natural route is
Noetherian induction on `S`: over a dense open of an integral affine piece of `S`, the fibre
dimension is constant and a relative Noether normalization gives a quasi-finite map to affine
space whose fibres have uniformly bounded cardinality.
