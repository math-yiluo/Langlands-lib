# Statement: the canonical class quotient on the supplied split Steinberg product

Authors: Worker 1490 and Worker 1800. Worker 1490 designed the Lean
proposition and the first Markdown draft; Worker 1800 reread the cited
source pages, rechecked the declaration and refined this explanation.

This module states one proposition and proves nothing:
`Langlands.GroupScheme.SplitSteinbergQuotientStatement.{u}`, a
`Prop`-valued `def` with the single universe parameter `u`, in the module
`Langlands.GroupScheme.Rational.SplitSteinbergQuotientStatement`.

## Lean statement

```lean
def SplitSteinbergQuotientStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (p : SplitPinning G), IsSimplyConnected G →
    ∀ (r : ℕ) (e : Fin r ≃ p.base.support)
      (x : p.NormalizedSimpleRootParametrizations)
      (n : p.SimpleReflectionRepresentatives),
      IsIso (SplitPinning.steinbergProduct e x n ≫ ClassFunctions.rho G)
```

It imports only the published modules
`Langlands.GroupScheme.Rational.SteinbergRootProduct`,
`Langlands.GroupScheme.Rational.ClassFunctions` and
`Langlands.GroupScheme.SimplyConnected.Basic`, and uses their declarations
unchanged.

## Meaning

The quantified data are:

- an arbitrary field `k : Type u`, of any characteristic, finite or
  infinite, perfect or imperfect;
- an actual group scheme `G` over `Spec k` whose structure morphism is
  affine;
- a supplied `p : SplitPinning G`. It contains the proof that `G` is
  connected reductive, an actual split maximal torus `p.torus` with
  inclusion `p.inclusion`, a finite reduced root datum `p.rootDatum`
  that is the root datum of that torus, a base `p.base` and a
  Lie-algebra pinning of the simple roots. Splitness is part of these
  data; it is not inferred from quasi-splitness;
- the premise `IsSimplyConnected G`: `G` is semisimple, and every central
  isogeny (finite, flat, surjective and locally of finite presentation,
  with central scheme-theoretic kernel) from a semisimple `k`-group to `G`
  is an isomorphism.

For every `r : ℕ`, every bijection `e : Fin r ≃ p.base.support` (an
ordering of the simple roots, so `r` is the rank), every family
`x : p.NormalizedSimpleRootParametrizations` and every family
`n : p.SimpleReflectionRepresentatives`, the conclusion is

```lean
IsIso (SplitPinning.steinbergProduct e x n ≫ ClassFunctions.rho G)
```

in the category `Over (Spec (CommRingCat.of k))`, that is, an
isomorphism of `k`-schemes.

- `SplitPinning.steinbergProduct e x n` is the published morphism from
  `(VectorGroup.groupScheme (CommRingCat.of k) r).X`, the spectrum of the
  polynomial algebra over `k` in `Fin r` variables, to `G.X`. On every test
  scheme it sends coordinates `c` to the ordered product of the factors
  `x_(e j)(c_j) n_(e j)` in increasing `j`. Each `x a` is a closed
  subgroup inclusion of the additive group onto the whole intrinsic root
  subgroup of the simple root `a`, torus-equivariant through that root and
  with derivative the pinned root vector. Each `n a` is a `k`-rational
  point of `G` normalizing the torus through a supplied torus automorphism
  whose action on characters is the simple reflection of `a`.
- `ClassFunctions.rho G` is the published canonical map
  `G.X ⟶ ClassFunctions.quotient G`. Its target is the spectrum of
  `ClassFunctions.algebra G`, the equalizer of the conjugation pullback and
  the right tensor inclusion in the fixed coordinate algebra of `G`, that
  is, the regular functions invariant under conjugation on points with
  values in every commutative `k`-algebra in universe `u`. The map is the spectrum of the
  subalgebra inclusion, transported through the fixed coordinate
  presentation `Lie.coordinateIso G`.

So the proposition says that the regular class functions restrict to a
polynomial coordinate system on Steinberg's ordered product: the composite
from affine `r`-space to the spectrum of the invariant algebra has an
inverse over `Spec k`. The map in the conclusion is exactly
`ClassFunctions.rho G`; no other conjugation-invariant map, no
fundamental-character map and no comparison isomorphism between invariant
algebras appears as data or as a premise. The conclusion is asserted for
every choice of ordering, root maps and representatives. Nothing asserts
that such root maps or representatives exist. When the base is empty,
`r = 0` and the product is the constant identity morphism, by the
published `SplitPinning.steinbergProduct_zero`.

## Sources and provenance

Provenance: derived.

R. Steinberg, *Regular elements of semi-simple algebraic groups*,
Publications Mathématiques de l'IHÉS 25 (1965), 49–80, registered source
`steinberg-1965-regular-elements-semisimple-groups`, SHA-256
`bda20c4a4b3cf4a7e9e5b17a4eacd0147d0c9370063ab3a3778114a53c8349b9`
(PDF page = printed page − 47). The passages below were read in that
registered file. No errata note for this source was found in the project.

- 1.4 (printed p.50, PDF p.3) defines `N = X_1 σ_1 X_2 σ_2 … X_r σ_r` for
  a maximal torus `T`, simple roots `α_1, …, α_r` in any labelling, the
  root subgroups `X_i`, and elements `σ_i` of the normalizer of `T`
  representing the simple reflections.
- 6.1(b) (printed p.62, PDF p.15): if `G` is simply connected, the algebra
  of regular class functions is freely generated as a commutative algebra
  by the fundamental characters `χ_1, …, χ_r`.
- 6.10 (printed p.64, PDF p.17): in the simply connected case the fibres
  are the inverse images of points under
  `ρ(x) = (χ_1(x), …, χ_r(x))` from `G` to affine `r`-space `V`.
- 7.1 (printed pp.66–67, PDF pp.19–20): `N` is isomorphic as a variety to
  affine `r`-space under `(c_i) ↦ ∏ x_i(c_i) σ_i`.
- 7.5 (printed p.67, PDF p.20): replacing each `σ_i` by another
  representative modulo `T` replaces `N` by a `T`-conjugate.
- 7.9 (printed p.68, PDF p.21): if `G` is simply connected, `ρ` maps `N`,
  as a variety, isomorphically onto `V`.
- 7.14 and its proof (printed pp.68–69, PDF pp.21–22): with `σ_i` in the
  rank-one subgroup `G_i` and a normalization of the `x_i`, the
  fundamental characters on `N` equal the coordinates plus integral
  polynomials in coordinates lower for an order on fundamental weights.
  7.9 is deduced from 7.1, 7.5 and 7.14.
- 9.2 (printed p.72, PDF p.25): over a perfect field `k` over which `G`
  splits, `N` can be constructed over `k` by choosing each `σ_i`
  rational.

Steinberg works with varieties over an algebraically closed field `K`
(printed p.49, PDF p.2), with no restriction on its characteristic
(printed p.51, PDF p.4). Here the field is arbitrary, the
group is an actual group scheme, and the quotient is the scheme-theoretic
equalizer `ClassFunctions.algebra G` rather than Steinberg's algebra
`C[G]` of regular class functions on the points of `G`. The proposition is
the following derived translation:

1. Steinberg's `V` with coordinates `χ_i` is replaced by
   `ClassFunctions.quotient G`, and his `ρ` by `ClassFunctions.rho G`.
   Over an algebraically closed field and for a simply connected group,
   6.1(b) says that the fundamental characters identify `V` with the
   spectrum of the class-function algebra, compatibly with the two maps
   from `G`, once the scheme-theoretic invariants are identified with
   Steinberg's `C[G]`.
2. Steinberg's parametrization of `N` from 7.1 is the published
   `SplitPinning.steinbergProduct e x n`, with the labelling of the simple
   roots given by `e`, the maps `x_i` given by `x`, and the `σ_i` given by
   the rational points of `n`.
3. Theorem 7.9, combined with 7.1, then says that the composite from
   affine `r`-space to the quotient is an isomorphism. 7.5 shows that the
   choice of representatives does not matter: conjugation by an element of
   `T` is an isomorphism and does not change `ρ`.

The split pinning and the rational data `x` and `n` make the composite a
morphism of `k`-schemes, as in the rational construction of 9.2. The
isomorphism claim over an arbitrary, possibly imperfect, field `k`, for
the canonical equalizer quotient, is the derived content of this
statement; Steinberg states 7.9 only over an algebraically closed field.

## Remaining proof obligations

The proposition is stated so that a later proof must establish, not
assume, the following. None of them is a premise here.

- **Fundamental characters and invariants.** Identify
  `ClassFunctions.algebra` over an algebraically closed field with the
  polynomial algebra on the fundamental characters (Steinberg 6.1(b)).
  This requires the fundamental representations and their characters for
  the given group. It also requires comparing the all-algebra equalizer
  with functions invariant on rational points, which uses that the group
  is smooth.
- **Simple connectedness.** Deduce from the Library's `IsSimplyConnected`,
  a condition on central isogenies over `k`, that the geometric group is
  simply connected in Steinberg's sense, so that 6.1(b) and 7.9 apply.
- **Triangular coordinates and arbitrary data.** Over an algebraic
  closure, relate the supplied root maps to Steinberg's normalized `x_i`
  of 7.14. Both are torus-equivariant isomorphisms onto the same root
  subgroup, so they should differ by a nonzero scalar on each coordinate,
  which is an automorphism of affine `r`-space; this must be checked.
  Handle arbitrary representatives `n` by 7.5, and arbitrary orderings `e`
  by applying 7.9 to the labelling that `e` defines. A proof that
  reproduces 7.9 also needs the triangular formula of 7.14.
- **Base change and descent.** Compare the invariant algebra, the quotient
  and `rho` with their counterparts after extension to an algebraic
  closure. The separate published statement
  `ClassFunctions.FieldBaseChangeStatement` formulates this comparison;
  this module neither imports nor proves it. Also show that the Steinberg
  product and the supplied data are compatible with that extension. Finally, descend the
  isomorphism back to `k` along the faithfully flat extension; this step
  needs no perfectness of `k`.

## What is not stated

- The proposition asserts no existence of split pinnings, normalized root
  maps or reflection representatives.
- No Galois action or descent of the product to an arbitrary quasi-split
  form is claimed. In particular, this proposition does not supply
  the witnesses of `QuasiSplitSteinbergQuotientStatement`. That needs
  ordinary quasi-split descent of the cross-section (Steinberg 9.4,
  printed p.72, PDF p.25) and a separate treatment of outer forms with a
  factor of type `A_n`, `n` even (Steinberg 9.6 and 9.7, printed p.73,
  PDF p.26; 9.19, printed p.77, PDF p.30).
- Regularity of the image, the immersion property of the product, the
  geometric fibres of `rho` (Steinberg 6.11) and rational lifting
  are not stated here.
- The parent `QuasiSplitSteinbergQuotientStatement` pair, every pair it
  imports, and the `SteinbergRootProduct` and `ClassFunctions` pairs are
  unchanged.
