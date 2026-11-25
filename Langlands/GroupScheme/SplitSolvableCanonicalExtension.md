# The canonical extension of a split solvable group is split

This module proves the splitting half of Milne's Corollary 16.56. The main
theorem is
`Langlands.GroupScheme.SplitSolvableCanonical.canonicalExtension_split`. Let
`k : Type u` be a field and `S = Spec (CommRingCat.of k)`. Let `G`, `U`, `D` be
group schemes over `S`, and assume:

- `IsSplitSolvableGroupScheme G`;
- `i : U ⟶ G` with `IsClosedSubgroup i` and `IsUnipotent U`;
- `q : G ⟶ D` with `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q`;
- `IsMultiplicativeType D`.

Then `RelativeRoot.IsSplitUnipotent U ∧ IsSplitTorus D`. So `U` has a series
whose successive quotients are one-dimensional vector groups
(`RelativeRoot.HasSplitSeries`), and `D` is isomorphic as a group scheme to
`splitTorus S I` for some finite `I`. The theorem is about the given data
`(U, D, i, q)`. It does not construct a canonical extension. Normality of
`range i` is not assumed, because the fppf-quotient hypothesis already makes
`range i` a kernel.

## Source and provenance

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type over
a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`. Printed page numbers; the one-based PDF page is
the printed page plus 16. The text was read from the PDF, printed p.344.

- Proof of Proposition 16.54: "The unipotent subgroup G_u is split and the
  quotient D is smooth".
- Proof of Corollary 16.56: "Here G/G_u is a split torus, and so it is
  isomorphic to G_m^{n−r}. On the other hand, G_u has a subnormal series with
  quotients isomorphic to G_a."

Milne states these two facts without a detailed argument. This module proves
them by its own induction on the length of the split series of `G`. The
induction is an internal derived argument. It uses only published Library
results, listed below. The helper lemmas in the section "General helpers" are
elementary facts about point functors, kernels and fppf maps. They are internal
and claim nothing from Milne.

The final proof [`SplitSolvableSchemeProof`](SplitSolvableSchemeProof.md)
passes this theorem as the hypothesis of
`SplitSolvableScheme.splitSolvableSchemeProduct_of_split` (module
[`SplitSolvableSchemeFromCanonical`](SplitSolvableSchemeFromCanonical.md)),
which gives the product decomposition of the underlying scheme.

## General helpers

In this section `S` is any scheme and `W H C X` are group schemes over `S`.

- `DynamicContainment.isIso_of_range_eq_top`: a homomorphism `w` whose underlying morphism is
  a monomorphism and whose range is `⊤` has an invertible underlying morphism.
  The identity point of `H` factors through `w`, which gives the inverse.
- `range_eq_top_of_quotient_eq_zero`: if `c` is an fppf quotient by
  `range w` and `c = 0`, then `range w = ⊤`. The range of `kernelι c` is
  everything when `c` is zero.
- `eq_zero_of_comp_eq_zero`: if `g` is quasi-compact, flat and surjective and
  `g ≫ c = 0`, then `c = 0`. Both `c` and `0` descend `0` through `g`, so they
  are equal by the uniqueness in `FpqcHomDescent.unique`.
- `isNormal_of_commute`: if all points of `H` commute, every subgroup functor of
  `H` is normal.
- `comp_eq_zero_of_range_le`: if `range w ≤ range (kernelι c)` then
  `w ≫ c = 0` (test on the identity point of `W`, `mem_range_kernelι_iff`).
- `eq_zero_of_range_eq_bot`: a homomorphism with range `⊥` is zero.
- `quasiCompact_hom`: a homomorphism from a quasi-compact group scheme to a
  quasi-separated one is quasi-compact (`QuasiCompact.of_comp`).
- `isClosedSubgroup_of_comp`: if `f ≫ g` is a closed subgroup and `g` is
  separated, then `f` is a closed subgroup (`IsClosedImmersion.of_comp`).
- `isAffineHom_of_isClosedSubgroup`, `locallyOfFiniteType_of_isClosedSubgroup`:
  the source of a closed subgroup inherits affineness and local finite type over
  `S`.
- `range_kernelι_comp_eq`: for a monomorphism `j : N ⟶ H`, `q : H ⟶ C` and
  `i' : U' ⟶ N`, if on points of `range j` membership in `range (kernelι q)` is
  equivalent to membership in `range (i' ≫ j)`, then
  `range (kernelι (j ≫ q)) = range i'`.
- `range_id_eq_bot_of_mono`: a group scheme with a monomorphism into a trivial
  group scheme is trivial (uses `CenterQuotient.id_eq_one_of_range_id_eq_bot`).
- `isSplitTorus_of_range_id_eq_bot`: a trivial group scheme is
  `splitTorus S PEmpty`. Both sides have a single point over every test scheme;
  the isomorphism comes from `isoOfPointModels` with `splitTorus.pointsEquiv`.
- `range_kernelι_comp_mono`: composing with a monomorphism does not change the
  kernel.
- `eq_zero_of_range_id_eq_bot_source`: every homomorphism out of a trivial group
  scheme is zero.
- `range_zero_eq_bot`: the zero homomorphism has range `⊥`.

## Over a field

From now on `k` is a field and all group schemes are over `Spec k`.

- `quotient_geometry`: let `G` be affine and locally of finite type, and let
  `q : G ⟶ Q` be flat, surjective and locally of finite presentation. Then `Q`
  is affine and locally of finite type. Local finite type descends along `q`
  (`locallyOfFiniteType_of_surjective_flat_locallyOfFinitePresentation_comp`).
  `Q` is quasi-compact as a surjective image of the affine `G`, separated
  (`fieldSeparated`), and affine by `affineGroupSchemeQuotient`.
- `fppf_of_quotients_trivial` (Lemma A): let `f : X ⟶ Y` be a homomorphism of
  affine group schemes locally of finite type, where all points of `Y` commute.
  Assume: every homomorphism `c : Y ⟶ C` that is flat, surjective and locally of
  finite presentation, onto an affine `C` locally of finite type, with
  `f ≫ c = 0`, is zero. Then `f` is flat, surjective and locally of finite
  presentation.

  Proof: `affineHomImage` factors `f = π ≫ w` with `π` fppf and `w` a closed
  subgroup. Since points of `Y` commute, `range w` is normal, so
  `affineNormalSubgroupQuotient` gives an fppf quotient `c : Y ⟶ C` by
  `range w`, with `C` affine and locally of finite type. Then `w ≫ c = 0`, so
  `f ≫ c = 0`, hence `c = 0` by the assumption, hence `range w = ⊤`. So the
  underlying morphism of `w` is an isomorphism, and `f` is the fppf `π` followed
  by an isomorphism. The three properties respect isomorphisms.

## The induction

`SplitClaim k n` says: for every group scheme `H`, affine and locally of finite
type over `Spec k`, with `SplitSolvable.HasSeries n H`, and for all
`i : U ⟶ H`, `q : H ⟶ D` with `IsClosedSubgroup i`, `IsUnipotent U`,
`IsFppfQuotient (range i) q` and `IsMultiplicativeType D`, the conclusion
`IsSplitUnipotent U ∧ IsSplitTorus D` holds.

- `splitClaim_zero`: `H` is trivial. Then `U` is trivial
  (`range_id_eq_bot_of_mono`), which is a split series of length `0`. Every
  homomorphism out of `H` is zero, so `q ≫ 𝟙 D = 0` and `𝟙 D = 0` by
  `eq_zero_of_comp_eq_zero`. So `D` is trivial and a split torus
  (`isSplitTorus_of_range_id_eq_bot`).

- `splitClaim_succ_ga`: the series of `H` starts with a closed normal subgroup
  `j : N ⟶ H` and an fppf quotient `q₀ : H ⟶ V`, with `V` a one-dimensional
  vector group and `N` carrying a series of length `n`.
  1. `ψ := i ≫ q₀ : U ⟶ V` is fppf, by Lemma A. Points of `V` commute
     (`IsVectorGroupOfDimension.points_commute`). Let `c : V ⟶ C` be an fppf
     quotient with `ψ ≫ c = 0`. `C` is unipotent
     (`IsUnipotent.of_flat_surjective`, since `V` is unipotent). `q₀ ≫ c` kills
     `range i = range (kernelι q)`, so it descends through `q` to
     `μ : D ⟶ C` (`FpqcHomDescent`). `μ = 0` because `D` is of multiplicative
     type and `C` unipotent (`IsMultiplicativeType.hom_eq_zero_of_isUnipotent`).
     So `q₀ ≫ c = 0` and `c = 0`.
  2. Let `U' := kernel ψ`. It is a closed subgroup of `U`, hence unipotent
     (`unipotentClosedSubgroup`). Its image in `H` lies in `range j`, so it
     factors as `a : U' ⟶ N` (`SubgroupFunctor.factorOfRangeLE`), a closed
     subgroup.
  3. `j ≫ q : N ⟶ D` is fppf, by Lemma A. Points of `D` commute (`D` is
     commutative, `IsMultiplicativeType.isCommMonObj`). Let `c : D ⟶ C` be an
     fppf quotient with `j ≫ q ≫ c = 0`. `C` is of multiplicative type
     (`IsMultiplicativeType.of_fppfHom`). `q ≫ c` kills `range j`, so it
     descends through `q₀` to `λ : V ⟶ C`. `λ` has trivial range by the third
     part of `unipotentMultiplicativeTriviality`, so `λ = 0`, so `q ≫ c = 0` and
     `c = 0`.
  4. The kernel of `j ≫ q` is `range a`. On points of `N`, lying in
     `range (kernelι q) = range i` is the same as lying in the image of
     `kernel ψ` (`range_kernelι_comp_eq`).
  5. The induction hypothesis on `N` with `(U', D, a, j ≫ q)` gives a split
     series of some length `r` on `U'` and that `D` is a split torus.
  6. `U'` is isomorphic to `𝔸^r` as a scheme (`splitUnipotentAffineSpaceStatement`),
     hence smooth (`smooth_of_over_iso`) and connected
     (`Scheme.homeoOfIso`). `kernelι ψ` is a closed subgroup
     (`kernelι_isClosedImmersion`) with normal range
     (`HopfPrimitive.isNormal_range_kernelι`), and `ψ` is an fppf quotient by
     it. With `V` one-dimensional, this is a split series of length `r + 1` on
     `U`.

- `splitClaim_succ_gm`: as before, but `V ≅ G_m`.
  1. `i ≫ q₀ = 0`, since `U` is unipotent and `V` a split torus
     (`IsUnipotent.hom_eq_zero_of_isSplitTorus`). So `range i ≤ range j`, and
     `i` factors as a closed subgroup `i_N : U ⟶ N`.
  2. `q₀` kills `range i`, so it descends through `q` to `χ : D ⟶ V` with
     `q ≫ χ = q₀`. `χ` is fppf, by Lemma A (`V` is commutative): if
     `χ ≫ c = 0` then `q₀ ≫ c = 0`, so `c = 0`.
  3. Let `D' := kernel χ`, with closed inclusion `kernelι χ`. It is of
     multiplicative type (`IsMultiplicativeType.of_isClosedSubgroup`). Since
     `j ≫ q ≫ χ = j ≫ q₀ = 0`, the map `j ≫ q` factors as `q' : N ⟶ D'`
     (`pullback.lift`, the kernel being a pullback).
  4. The square with sides `q'`, `j`, `kernelι χ`, `q` is a pullback. Paste the
     pullback square of `kernelι χ` (`kernel_isPullback`) with the kernel square
     of `q₀`. The latter is moved to `N` via `IsFppfQuotient.kernelIso`
     (`IsPullback.of_right`). So `q'` is a base change of `q`, hence flat,
     surjective and locally of finite presentation
     (`MorphismProperty.of_isPullback`). Its kernel is `range i_N`, by
     `range_kernelι_comp_mono` and `range_kernelι_comp_eq`.
  5. The induction hypothesis on `N` with `(U, D', i_N, q')` gives that `U` is
     split unipotent and `D'` is a split torus.
  6. `D' → D → V` is a central extension of the split torus `V` by the split
     torus `D'`, with `χ` an fppf quotient by `range (kernelι χ)`. It is central
     because `D` is commutative. So `D` is a split torus by
     `CentralExtensionHopfSpec.isSplitTorus_of_split`.

- `splitClaim`: induction on `n`, splitting the successor case with
  `SplitSolvable.hasSeries_succ_iff` into the two steps above.

- `canonicalExtension_split`: `G` is affine and smooth, hence locally of finite
  type, and has a series of some length `n`. Apply `splitClaim n`.
