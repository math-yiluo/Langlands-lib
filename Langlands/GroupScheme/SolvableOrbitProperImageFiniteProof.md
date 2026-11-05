# Finite proper images in homogeneous spaces of split-solvable groups

Module `Langlands.GroupScheme.SolvableOrbitProperImageFiniteProof`.

Worker 1506 wrote this module. Its induction step applies the theorem
`stabilizerImageDichotomy : StabilizerImageDichotomyStatement` of
`Langlands.GroupScheme.StabilizerImageDichotomy` (Worker 716; the statement text is
Worker 1506's), and the fibre step and base case of
`Langlands.GroupScheme.HomogeneousProperImageFibre` (Workers 1095 and 1506).

Throughout, `k` is a field, `Spec k` means `Spec (CommRingCat.of k)`, and a rational
point of a `k`-scheme `O` is a morphism `Over.mk (𝟙 (Spec k)) ⟶ O` over `Spec k`.
`HasOnePointProperImages H` is the predicate of
`Langlands.GroupScheme.HomogeneousProperImageFibre`. It says that every proper,
reduced and connected `k`-scheme has one-point image in every reduced, separated,
quasi-compact, locally finite type `k`-scheme on whose rational points the rational
points of `H` act transitively.

## Results

All results below take `k` algebraically closed, except
`HasOnePointProperImages.range_finite`, which holds over any field.

- `SolvableOrbitProperImage.hasOnePointProperImages_succ`. Let `G`, `N`, `V` be
  group schemes over `Spec k` with `G` smooth and affine over `k` and `N` smooth
  over `k`. Let
  `jN : N ⟶ G` and `q : G ⟶ V` be such that `q` is an fppf quotient of `G` by the
  range of `jN` (`RelativeRoot.IsFppfQuotient`), and let `V` be elementary
  (`SplitSolvable.IsElementaryQuotient`: a one-dimensional vector group, or
  isomorphic to `Gm`). If `HasOnePointProperImages N`, then
  `HasOnePointProperImages G`.
- `SolvableOrbitProperImage.hasOnePointProperImages_of_hasSeries`. Every group
  scheme `G` over `Spec k`, smooth and affine over `k`, with a series
  `SplitSolvable.HasSeries n G` satisfies
  `HasOnePointProperImages G`.
- `HasOnePointProperImages.range_finite`. Over any field `k`, if
  `HasOnePointProperImages G`, then the conclusion of the target statement holds for
  `G`. For `O` and `a` as in the predicate and every proper `k`-scheme `Z`, the image
  of every `j : Z ⟶ O` is finite. Here `Z` need not be reduced or connected.
- `solvableOrbitProperImageFinite_of_split`. The target
  `SolvableOrbitProperImageFiniteStatement.{u}` follows from
  `AlgebraicallyClosedSplitSolvableStatement.{u}`, which says that smooth, affine,
  connected, solvable group schemes over an algebraically closed field are split
  solvable.
- `solvableOrbitProperImageFinite : SolvableOrbitProperImageFiniteStatement.{u}`.
  This is the target. It applies `solvableOrbitProperImageFinite_of_split` to the
  published theorem `algebraicallyClosedSplitSolvable` of
  `Langlands.GroupScheme.AlgebraicallyClosedSplitSolvableProof` (Workers 1472 and
  1448).

## Proof of the induction step

Let `O`, `a`, `x`, `Z` and `j : Z ⟶ O` be as in `HasOnePointProperImages G`, with
`G(k)` transitive on `O(k)` through `x`. Let `iK : K ⟶ G` be the stabilizer of `x`,
a closed subgroup (`SchemeAction.exists_isClosedSubgroup_stabilizer`; `O` is
separated). So `K` is affine and locally of finite type over `k`, and its rational
points fix `x`. Two facts about `N` are used:

- Every point of `N` maps to `1` under `jN ≫ q`. This holds because the range of
  `jN` is the kernel of `q` (`mem_range_kernelι_iff`).
- If rational points `g`, `h` of `G` have the same image in `V`, then `g * h⁻¹`
  comes from a rational point of `N`
  (`SchemeAction.inv_mul_mem_range_of_fppf_quotient`).

The dichotomy `stabilizerImageDichotomy` applied to `iK ≫ q : K ⟶ V` gives two
cases.

Case A: every rational point of `V` lifts to a rational point of `K`. Then `N(k)` is
already transitive on `O(k)`. Write `y = a.act g x` and lift `g ≫ q` to a rational
point `s` of `K`. Then `g * (s ≫ iK)⁻¹` comes from a rational point `n` of `N`, and
`n` sends `x` to `y`, because `s ≫ iK` fixes `x`. Apply `HasOnePointProperImages N`
to the restricted action `a.restrict jN`.

Case B: there is an affine `k`-scheme `W` and `χ : V.X ⟶ W` such that `χ` is
invariant under right translation by the image of `K` on every test scheme, and two
rational points of `V` with the same value under `χ` differ by the image of a
rational point of `K`. The orbit map `G.X ⟶ O` of `x` is flat, surjective and
quasi-compact (`orbitMapFaithfullyFlat`). Two points of `G` with the same image under
the orbit map differ by a point of `K`. The map `q ≫ χ` is constant on cosets of
`K`. So `FiniteIndexTransfer.exists_factor` gives `f : O ⟶ W` with
`orbitMap ≫ f = q ≫ χ`. Hence `a.act g x ≫ f = (g ≫ q) ≫ χ` for rational `g`. Then:

- `f` is invariant on rational points under `N`, since `N` maps to `1` in `V`.
- If `a.act g₁ x` and `a.act g₂ x` have the same value under `f`, then
  `g₁ ≫ q` and `g₂ ≫ q` have the same value under `χ`. So
  `g₂ ≫ q = (g₁ * (s ≫ iK)) ≫ q` for a rational point `s` of `K`. Hence
  `g₂ * (g₁ * (s ≫ iK))⁻¹` comes from a rational point `n` of `N`, and `n` sends
  `a.act g₁ x` to `a.act g₂ x`.

These are the hypotheses of `HasOnePointProperImages.subsingleton_range_of_fibres`
for `N` acting on `O` through `a.restrict jN`, and that theorem gives the
conclusion.

Neither case uses normality or connectedness of `N`.

## Induction and the final reduction

`hasOnePointProperImages_of_hasSeries` is an induction on `n`. For `n = 0`, every
point of `G` is trivial, and `hasOnePointProperImages_of_range_id_eq_bot` applies.
For `n + 1`, the series supplies `N`, `V`, `jN`, `q` with `jN` a closed subgroup
and `N` smooth with a series of length `n`. `N` is affine over `k`, because `jN` is a
closed immersion into the affine `G`. The induction hypothesis and the step above
conclude.

`range_finite`: `Z` is proper, hence quasi-compact and locally noetherian, so it is
a noetherian space with finitely many irreducible components. Give each component
`C` its reduced closed subscheme structure. This is the subscheme of the vanishing
ideal of `C`, reduced by
`Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal_and_le_ker`. It is proper
over `k` as a closed subscheme of `Z`, and connected because `C` is irreducible. By
the predicate, `j` sends it to at most one point, so `j(C)` has at most one point.
The image of `j` is the union of the finitely many sets `j(C)`.

`solvableOrbitProperImageFinite_of_split`: the comparison statement makes `G` split
solvable, which supplies `SplitSolvable.HasSeries n G` for some `n`. Then
`hasOnePointProperImages_of_hasSeries` and `range_finite` give the target.
`solvableOrbitProperImageFinite` discharges the comparison statement with
`algebraicallyClosedSplitSolvable`.

## Source

The target is the finite-image form of Milne, *Algebraic Groups* (2017),
Theorem 17.1 and Corollary 17.2, printed pp.352–353 (one-based PDF pp.368–369),
source ID `milne-2017-algebraic-groups`. Milne inducts on the dimension of `G` and
uses the derived group and quotients. The Lean proof follows the same idea: pass
from `G` to a normal subgroup `N` with quotient `Ga` or `Gm`, either directly or
through the fibres of an invariant map to an affine scheme. It inducts along the
split series instead, and replaces quotients of `O` by the invariant affine-valued
map `f`. The predicate `HasOnePointProperImages` and the dichotomy are internal to
this proof; they are not literature definitions.
