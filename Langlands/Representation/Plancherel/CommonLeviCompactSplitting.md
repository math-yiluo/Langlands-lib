# Small compact open subgroups splitting along two cocharacters with one Levi

Author: Worker 200.

## Source and provenance

This is derived support for J.-L. Waldspurger, *La formule de Plancherel
pour les groupes p-adiques (d'après Harish-Chandra)*, J. Inst. Math.
Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082. The registered
original is `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

In I.1, printed p.240 / PDF p.6, the source fixes a maximal compact subgroup
`K`, the fixer of a special point of the apartment of `A₀`, and gives every
closed algebraic subgroup `H` the left Haar measure with `mes(H ∩ K) = 1`.
In the proof of remark (3), printed pp.240–241 / PDF pp.6–7, it uses without
proof a compact open subgroup `H` of `K` such that, for every semi-standard
`P = MU`,
`H = [∏_{α ∈ Σred(P)} (H ∩ U_α)] (H ∩ M) [∏_{α ∈ Σred(P̄)} (H ∩ U_α)]`, with
the roots in any fixed order. IV.3(1), printed pp.285–286 / PDF pp.51–52,
applies the composition formula IV.1(12) four times. Each time the source
parabolic is opposite to the target parabolic and the middle parabolic has
the same Levi subgroup. The measures are the ones normalized by `K`.

The published composition theorem
`OppositeCharts.comp_hasIntegral_of_hasCompactOpenProduct` covers exactly this
opposite-source, common-Levi case. It still takes two Iwahori-type
factorizations of the normalizing compact open subgroup `Q` as inputs. This
module proves that such `Q` exist. For two cocharacters with the same Levi
points, every identity neighborhood contains a compact open subgroup with all
the factorizations needed by the four applications in IV.3(1).

The provenance is internal. The construction is not the source's: it uses
no root subgroups and no building. It combines the published
contraction-basis construction
`Jacquet.hasOppositeIwahoriContractionBasis_of_contraction` with the
published uniqueness of opposite-cell factorizations. No new translation of a
numbered literature result is asserted, and nothing is proved about the
source's subgroup `K`.

## Generic helpers

`Γ` is a group, with a topology where stated.

* `HasCompactOpenProduct.swap`: for an open subgroup `Q`, if every `g ∈ C ∩ Q`
  is `a * b` with `a ∈ A ∩ Q` and `b ∈ B ∩ Q`, then it is also `b' * a'` with
  `b' ∈ B ∩ Q` and `a' ∈ A ∩ Q`. Apply the hypothesis to `g⁻¹` and invert.
* `HasCompactOpenProduct.mono`: the factors `A` and `B` may be enlarged.
* `hasCompactOpenProduct_of_conj_mem` (splitting by a conjugation cut).
  Assume every `v ∈ V` is `o * m * w` with `o ∈ O'`, `m ∈ M'`, `w ∈ U'` and
  `o, w ∈ V`, and that such factorizations are unique. Let every `x ∈ H` be
  `a * b` with `a ∈ A ≤ O' ⊓ H` and `b ∈ B ≤ U' ⊓ H`. Let `C` be a set whose
  elements normalize `O'` and `U'`, and assume `x ∈ H` lies in `K` exactly
  when `c x c⁻¹ ∈ V` for all `c ∈ C`. Then every `x ∈ H ∩ K` is `a * b` with
  `a ∈ A ∩ K` and `b ∈ B ∩ K`. The proof writes `c x c⁻¹` as
  `(c a c⁻¹) · 1 · (c b c⁻¹)` and compares it with the factorization of
  `c x c⁻¹` in `V`. By uniqueness, `c a c⁻¹` and `c b c⁻¹` lie in `V`.
* `stablePiece V H h` is the subgroup of `x ∈ H` with `h^k x h^{-k} ∈ V` for
  every `k ≥ 0` (`mem_stablePiece`).
* `stablePiece_spec` proves, for compact `V`, closed `H` and `h` central in a
  subgroup `M` normalizing `H` and contracting `H` uniformly on compacts:
  `stablePiece V H h` lies in `H ∩ V`, is compact, is stable under
  conjugation by `h` and by `V ∩ M`, and contains every point of `H` in some
  identity neighborhood. These are the conclusions of the published
  `Jacquet.exists_stable_piece`, here for this explicit subgroup.
* `exists_iwahori_stablePieces` repeats the published construction of
  `Jacquet.hasOppositeIwahoriContractionBasis_of_contraction` and keeps its
  two radical pieces explicit. Assume `Γ` is a locally compact
  nonarchimedean group, `O`, `M`, `U` are subgroups with `O`, `U` closed,
  unique factorizations `o m u`, an identity-neighborhood open cell, and
  `g ∈ M` central in `M` contracting `U` and expanding `O`, as in the
  published theorem. Then every compact open subgroup `V` contains a compact
  open subgroup `K` with `K = (K ∩ O)(K ∩ M)(K ∩ U)`. Moreover, `x ∈ U` lies
  in `K` exactly when `g^j x g^{-j} ∈ V` for all `j ≥ 0`, and for one `n`,
  `x ∈ O` lies in `K` exactly when `c x c⁻¹ ∈ V` for all
  `c = g^{-j} g^n`, `j ≥ 0`. Here `K = A B₀ C₀` with `C₀ = stablePiece V U g`,
  `B₀ = V ∩ M` and `A` the conjugate by `g^{-n}` of `stablePiece V O g⁻¹`. The
  proof of the subgroup property and openness is the published one.

## Actual setting

`F` is a nonarchimedean local field of arbitrary characteristic. The group
scheme `G` over `F` is smooth, has affine structure morphism and is locally
of finite type. No reductivity, split or quasisplit condition is imposed.
`G(F)` carries the canonical point topology. For a cocharacter `t`,
`unipotentPoints t` is the literal radical `U(t)(F)`,
`Dynamic.inverseCocharacter t` is `t⁻¹`, and `Z(t)(F)` is the set of rational
points of the dynamic centralizer. "Same Levi points" for `t` and `m` means
`Z(t)(F) = Z(m)(F)`.

## Splitting along a cocharacter

`SplitsAlong Q t m` states
`HasCompactOpenProduct Q (U(t⁻¹) ⊓ U(m)) (U(m) ⊓ U(t)) U(m)`: every point of
`U(m) ∩ Q` is `a * b` with `a ∈ U(t⁻¹) ∩ U(m) ∩ Q` and
`b ∈ U(m) ∩ U(t) ∩ Q`.

* `SplitsAlong.inverse`: splitting along `t` gives splitting along `t⁻¹`,
  by `swap`, `t⁻¹⁻¹ = t` and commutativity of `⊓`.
* `SplitsAlong.second`: `SplitsAlong Q m t` gives
  `HasCompactOpenProduct Q (U(m) ⊓ U(t)) (U(m⁻¹) ⊓ U(t)) U(t)`. This is the
  order of the second chart of `OppositeCharts` for target `t` and middle `m`.
* `exists_mul_of_mem`: if `Z(t)(F) = Z(m)(F)`, every point of `U(m)` is a
  product of a point of `U(t⁻¹) ∩ U(m)` and a point of `U(m) ∩ U(t)`. This is
  surjectivity of the published `OppositeCharts.firstChart`.
* `splitsAlong_of_conj_mem`: assume `Z(t)(F) = Z(m)(F)`, every `v ∈ V` is
  `o z w` with `o ∈ V ∩ U(t⁻¹)`, `z ∈ Z(t)(F)` and `w ∈ V ∩ U(t)`,
  `C ⊆ Z(t)(F)`, and `x ∈ U(m)` lies in `Q` exactly when `c x c⁻¹ ∈ V` for all
  `c ∈ C`. Since `z = o⁻¹ v w⁻¹`, the middle factor then lies in
  `V ∩ Z(t)(F)`; the premise does not put all of `Z(t)(F)` in `V`. Then `SplitsAlong Q t m`. It is
  `hasCompactOpenProduct_of_conj_mem` with `O' = U(t⁻¹)`, `M' = Z(t)`,
  `U' = U(t)` and `H = U(m)`. Uniqueness is the published
  `RationalPointFamily.dynamic_opposite_factorization_unique`. Points of
  `Z(t)(F)` normalize both radicals by the published
  `Dynamic.centralizer_le_normalizer_unipotent` and `Z(t⁻¹) = Z(t)`.
* `splitsAlong_of_factor`: if every `q ∈ Q` is `o z w` with
  `o ∈ Q ∩ U(t⁻¹)`, `z ∈ Z(t)(F)` and `w ∈ Q ∩ U(t)` (so `z ∈ Q ∩ Z(t)(F)`), then
  `SplitsAlong Q t m` for every `m` with `Z(t)(F) = Z(m)(F)`. Take `V = Q` and
  `C = {1}`.

## Common-Levi splittings

`IsCommonLeviSplitting Q χ ψ` has four fields:

* `left : SplitsAlong Q χ ψ`;
* `left_inverse : SplitsAlong Q χ ψ⁻¹`;
* `right : SplitsAlong Q ψ χ`;
* `right_inverse : SplitsAlong Q ψ χ⁻¹`.

So `Q ∩ U(ψ)` and `Q ∩ U(ψ⁻¹)` split along `χ`, and `Q ∩ U(χ)` and
`Q ∩ U(χ⁻¹)` split along `ψ`. `symm` exchanges `χ` and `ψ`. `inverse_left`
replaces `χ` by `χ⁻¹` and `inverse_right` replaces `ψ` by `ψ⁻¹`. Both use
`SplitsAlong.inverse` and `χ⁻¹⁻¹ = χ`.

## Existence

The section uses the published Hausdorff, topological-group, local
compactness and nonarchimedean instances on `F` and `G(F)`.

`exists_iwahoriCut χ V hVc`: for every compact open subgroup `V` there are
`g ∈ Z(χ)(F)`, a compact open subgroup `K ⊆ V` whose every point is `o z w`
with `o ∈ K ∩ U(χ⁻¹)`, `z ∈ Z(χ)(F)` and `w ∈ K ∩ U(χ)` (then
`z = o⁻¹ k w⁻¹ ∈ K ∩ Z(χ)(F)`), and `n` such that

* `x ∈ U(χ)` lies in `K` exactly when `g^j x g^{-j} ∈ V` for all `j ≥ 0`;
* `x ∈ U(χ⁻¹)` lies in `K` exactly when `c x c⁻¹ ∈ V` for all
  `c = g^{-j} g^n`, `j ≥ 0`.

The proof applies `exists_iwahori_stablePieces` with `O = U(χ⁻¹)`,
`M = Z(χ)(F)` and `U = U(χ)`. The point `g`, central in `Z(χ)(F)`,
contracting `U(χ)` and expanding `U(χ⁻¹)`, comes from the published
`exists_central_contractingPoint`. The open cell is the published
`Dynamic.opposite_cell_mem_nhds_one`, transported by `rationalPointTopology_eq_rationalSchemeTopology`. Uniqueness
and normalization are as above, and both radicals are closed
(`isClosed_unipotentPoints`).

`exists_isCommonLeviSplitting hZ hW`: if `Z(χ)(F) = Z(ψ)(F)` and `W` is an
identity neighborhood of `G(F)`, there is a compact open subgroup `Q ⊆ W` with
`IsCommonLeviSplitting Q χ ψ`. The proof is:

1. Take a compact open subgroup `V₀ ⊆ W` (published
   `Jacquet.exists_isCompact_openSubgroup_subset`). Apply `exists_iwahoriCut`
   to `ψ` and `V₀` to get a compact open subgroup `V ⊆ V₀` whose every point
   is `o z w` with `o ∈ V ∩ U(ψ⁻¹)`, `z ∈ Z(ψ)(F)` and `w ∈ V ∩ U(ψ)`. Then
   `z ∈ V`, so `V = (V ∩ U(ψ⁻¹)) (V ∩ Z(ψ)(F)) (V ∩ U(ψ))`.
2. Apply `exists_iwahoriCut` to `χ` and `V`. This gives `g`, `n` and a compact
   open subgroup `Q ⊆ V` whose every point is `o z w` with
   `o ∈ Q ∩ U(χ⁻¹)`, `z ∈ Z(χ)(F)` and `w ∈ Q ∩ U(χ)`. Again `z ∈ Q`, so
   `Q = (Q ∩ U(χ⁻¹)) (Q ∩ Z(χ)(F)) (Q ∩ U(χ))`.
3. `left` and `left_inverse` follow from `splitsAlong_of_factor` applied to
   `Q`, for `m = ψ` and `m = ψ⁻¹`, using `Z(ψ⁻¹) = Z(ψ) = Z(χ)`.
4. `right` follows from `splitsAlong_of_conj_mem` for `t = ψ` and `m = χ`, with
   the factorization of `V` from step 1 and `C = {g^j : j ≥ 0}`. By step 2,
   this set cuts `Q ∩ U(χ)` out of `U(χ)`. Since `g ∈ Z(χ)(F) = Z(ψ)(F)`, it
   lies in `Z(ψ)(F)`.
5. `right_inverse` is the same with `m = χ⁻¹` and
   `C = {g^{-j} g^n : j ≥ 0}`.

## Composition

`comp_hasIntegral_of_isCommonLeviSplitting` takes the same arguments as the
published `OppositeCharts.comp_hasIntegral_of_hasCompactOpenProduct`: target
`χ` and middle `ψ` with `Z(χ)(F) = Z(ψ)(F)`, a compact open `Q`, explicit
measurable and Borel structures, semidirect decompositions `P₀ = M ⋉ U(χ⁻¹)`
and `P₁ = M ⋉ U(ψ)`, a canonical `SmoothRep.{0,u,uV} ℂ M` named `A`, the
integral witnesses `hf` and `hΦ`, and ordered absolute scalar integrability
`ha`. The two `HasCompactOpenProduct` inputs are replaced by one
`hs : IsCommonLeviSplitting Q χ ψ`. They are `hs.left` and
`hs.right.second`. The conclusion is unchanged: the direct integral of `f`
from the opposite of `P(χ)` to `P(χ)`, at
`DynamicSource.quotientMeasure Q hQ χ⁻¹ χ`, is `J`.

## Use in IV.3(1)

Let `χ` and `χ'` have the same Levi points. The four applications of IV.1(12)
in IV.3(1) are the instances (target, middle) = `(χ', χ)`, `(χ'⁻¹, χ⁻¹)`,
`(χ, χ'⁻¹)` and `(χ⁻¹, χ')` of the composition above. If
`hs : IsCommonLeviSplitting Q χ' χ`, the four required splittings are `hs`,
`hs.inverse_left.inverse_right`, `hs.symm.inverse_right` and
`hs.symm.inverse_left`. So one `Q` from `exists_isCommonLeviSplitting`, inside
any prescribed identity neighborhood, normalizes the measures of all four
applications at once. The four instantiations themselves are not written out
in Lean here.

## Scope

* `Q` is a small compact open subgroup produced by the construction. Nothing
  is proved about the source's special maximal compact subgroup `K`, nor
  about the subgroup `H` with root-product decompositions used in I.1.
* The measures are normalized by `Q`. They differ from the source's
  normalization `mes(H ∩ K) = 1` by positive constants, which are not
  computed here.
* Ordered absolute convergence, both integral witnesses and original-carrier
  representability remain explicit inputs. No convergence domain is shown to
  be nonempty.
* No rational continuation, operator identity, scalar `j`, independence of
  `P`, `μ` or Plancherel conclusion is claimed.
