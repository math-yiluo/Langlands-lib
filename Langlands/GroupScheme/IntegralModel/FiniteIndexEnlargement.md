# Finite-index enlargements of schematic integral-point subgroups

This module states the finite-index enlargement step of KP's construction of
integral models. It gives an interface, `IsOpenEnlargement`, and a closed
existence target, `FiniteIndexEnlargementStatement.{u}`. It does not prove
that an enlargement exists. That is left to a separate proof task.

## The interface `IsOpenEnlargement`

`M N : IntegralModel R K G` are two existing integral models of the same
generic group `G`. `j : M.Hom N (𝟙 G)` is an actual morphism of group schemes
`M.group ⟶ N.group` whose base change to `K`, composed with the chosen
generic-fibre identifications, is the identity of `G`.
`V : Subgroup (rationalPoints G)` is a subgroup of the group of actual
`K`-points of `G`. `IsOpenEnlargement M N j V` is the conjunction of:

- `N.IsSmooth`: the structural morphism of `N.group` is smooth;
- `N.integralPoints = V`. Here `integralPoints` is the Library's image of
  the actual sections `Spec R ⟶ N.group` in `rationalPoints G`. Each section
  is base-changed along `Spec K ⟶ Spec R` and then transported by
  `N.genericIso`;
- `IsOpenImmersion j.hom.hom.hom.left`: the underlying morphism of schemes
  `M.group.X.left ⟶ N.group.X.left` is an open immersion;
- preservation of every supplied relative identity-component
  representative. For every actual group scheme `C` over `Spec R` and every
  `i : C ⟶ M.group`, `IsRelativeIdentityComponent M.group i` implies
  `IsRelativeIdentityComponent N.group (i ≫ j.hom)`.

`IsRelativeIdentityComponent` is the Library's all-test predicate from
`Langlands.GroupScheme.RelativeIdentityComponent`. It holds when `i` is an
open immersion of underlying schemes and, for every scheme `T` over the base,
a `T`-point of the group factors through `i` exactly when its image in every
residue fibre lies in the identity component of that fibre. This is the
fibre-image condition of SGA 3, VI_B, Definition 3.1, as recorded in that
module. The predicate says that a given open subgroup represents the
component. It does not assert that one exists, so the last clause only
quantifies over representatives that are supplied. In this clause one
group scheme `C` represents both components: once by `i` and once by
`i ≫ j.hom`. That is how this file expresses the source's statement that
`j` induces an isomorphism between the relative identity components.

The existing `IntegralModel` record already makes `N.group` an affine, flat
group scheme of finite type over `Spec R`, with a specified isomorphism from
its actual generic fibre to `G`. Every interface clause refers to the given
generic group `G` through `IntegralModel.Hom`. No point group is replaced by
an abstract isomorphic group.

## Elementary consequences proved here

- `IsOpenEnlargement.integralPoints_le` (implicit `M N j V`): an open
  enlargement gives `M.integralPoints ≤ V`. The proof applies the Library
  lemma `IntegralModel.Hom.map_mem_integralPoints` to `j`, whose generic
  morphism is `𝟙 G`, and then rewrites with `N.integralPoints = V`.
- `IsOpenEnlargement.exists_relativeIdentityComponent`: if `M` is also
  smooth, the relative-component clause is not vacuous. There exist an actual
  `C` and `i : C ⟶ M.group` such that `i` represents the relative identity
  component of `M.group` and `i ≫ j.hom` represents that of `N.group`. The
  proof takes the representative supplied by the Library theorem
  `Langlands.GroupScheme.RelativeIdentityComponent.smoothExistence`, applied
  to the smooth group scheme `M.group`, and then applies the fourth clause of
  the enlargement.

Neither result constructs an enlargement.

## The target `FiniteIndexEnlargementStatement.{u}`

The target quantifies over:

- every discrete valuation ring `R : Type u` that is a Henselian local ring
  with algebraically closed residue field;
- every fraction field `K : Type u` of `R`;
- every group scheme `G` over `Spec K` whose structural morphism is affine
  and smooth;
- every existing integral model `M : IntegralModel R K G` with `M.IsSmooth`;
- every subgroup `V` of `rationalPoints G` with `M.integralPoints ≤ V`.

Suppose `M.integralPoints.subgroupOf V` is normal and of finite index in `V`.
The target then asserts that some `N : IntegralModel R K G` and some
`j : M.Hom N (𝟙 G)` satisfy `IsOpenEnlargement M N j V`. Normality and finite
index are only assumed inside `V`, through `subgroupOf V`. Normality in the
whole of `rationalPoints G` is not assumed.

## Comparison with the original source

The original is Kaletha and Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), registered as `kaletha-prasad-2023-bruhat-tits-new-approach`, content
SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
Proposition A.7.1 and its proof are on printed pp.647–649 / PDF pp.678–680.

KP's hypotheses are as follows. `H` is a smooth affine `K`-group. `U ⊂ V ⊂ H(K)`
are subgroups with `U` normal in `V` and bounded open in `H(K)`. `U` is
schematic with smooth affine integral model `𝒰`, and the source recalls that
`O` is strictly Henselian. Item by item:

1. *KP: there is a smooth separated group scheme `𝒱`, not necessarily affine,
   with generic fibre `H` and `𝒱(O) = V`.* Here `N` is smooth and
   `N.integralPoints = V`. `N` is affine because it is an `IntegralModel`, so
   it is separated.
2. *KP: `𝒱` comes with a morphism `𝒰 → 𝒱` extending the inclusion
   `U → V → H(K)`, unique because `𝒱` is separated.* Here `j : M.Hom N (𝟙 G)`
   is an actual group-scheme morphism that extends the identity of the generic
   group. This matches KP Definition 2.10.1(3), printed p.121 / PDF p.152,
   where a morphism of integral models extends the identity. Uniqueness of
   `j` is not part of the target.
3. *KP: the morphism is an open immersion and induces an isomorphism between
   the relative identity components.* Here the third clause of
   `IsOpenEnlargement` gives the open immersion, and the fourth clause gives
   the identity-component statement described above.
4. *KP: if `[V : U] < ∞`, then `𝒱` is affine and so is a smooth integral
   model of `H`.* The target only covers finite index, and it puts
   affineness into the conclusion by asking for an `IntegralModel`. In the
   proof, KP obtain affineness from Prasad–Yu, Proposition 3.1.

The target omits items (5) and (6). Item (5) is the formula
`𝒱(R') = 𝒰(R')·V` for local ring extensions `R'`, and item (6) is descent to
`o` for `Γ`-invariant `V`. It also omits the infinite-index case, in which
`𝒱` may fail to be affine.

**Base ring.** KP's Section 2.10 convention (printed p.121 / PDF p.152) takes
a Henselian discretely valued field `k` with ring of integers `o`, a maximal
unramified extension `K` with ring of integers `O`, and points in `O`. The
Appendix A convention is on printed p.593 / PDF p.624. In A.7.1 the models
`𝒰` and `𝒱` are `O`-group schemes, and the source recalls that `O` is
strictly Henselian. Here `R` plays the role of `O`, and the source's `K` is
the Lean `K = Frac R`. Let `R` be a Henselian DVR with algebraically closed
residue field, and put `k := Frac R`, `o := R`. The residue field is then
separably closed, so `k` has no nontrivial unramified extension. Hence the
source's `K` and `O` are `k` and `R`, and KP's `O`-points are exactly the
actual `R`-sections used by `integralPoints`. Conversely, a strictly
Henselian `O` has algebraically closed residue field exactly when that field
is perfect. So the target is the perfect-residue case of A.7.1, which is
narrower than the appendix. That is the case the consumer needs.

The registered authors' *Corrections and additions* (1 November 2024),
`kaletha-prasad-2024-corrections`, content SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`, require
a perfect residue field from Section 8.3 onward (PDF p.37). Their Appendix
corrections on PDF pp.49–50 concern A.4 and do not change A.7. The consumer
is Theorem 8.3.2, printed p.296 / PDF p.327. Its proof uses A.7.1 to pass
from an already schematic bounded subgroup to a larger, finite-index
stabilizer subgroup with the same relative identity component.

**Starting from a model rather than a bounded open subgroup.** KP assume that
`U` is bounded open and also schematic with smooth affine model `𝒰`, so that
`𝒰(O) = U` (Definition 2.10.15, printed p.126 / PDF p.157). The target takes
the model `M` as given and sets `U := M.integralPoints`. KP Remark 2.10.3
(printed p.122 / PDF p.153) shows that the point set of an affine
finite-type model is closed, open and bounded in the analytic topology of
the generic points, and it also applies over algebraic extensions. So the
bounded-open premise follows from the existence of `𝒰` and is not encoded
separately. The Lean file defines no valuation topology and does not prove
this remark. It is a justification of the formulation, not a formalized
claim. Remark 2.10.2 (printed p.121 / PDF p.152) states that the point map is
injective for flat models. The target does not need this, because
`integralPoints` is defined as an image subgroup.

**Generic group hypotheses.** The assumptions `[IsAffineHom G.X.hom]` and
`Smooth G.X.hom` mirror KP's "smooth affine `K`-group `H`". Given a smooth
`M`, both already follow from `M.genericIso`, since base change keeps
affineness and smoothness. They are kept so that the statement matches the
source. The target does not derive them.

**Relative identity component.** KP Definition 4.1.18 (printed p.162 /
PDF p.193) defines the relative identity component of a smooth `o`-group
scheme as its largest subgroup scheme with connected fibres. Citing SGA 3,
VI_B, Theorem 3.10, KP note that it exists, is open, and is the union of the
neutral components of the fibres. The Library's all-test predicate describes
the same open subgroup through its functor of points. For a smooth `M`, the
Library theorem `RelativeIdentityComponent.smoothExistence` supplies a
representative, which is why the clause is not vacuous here. Requiring the
clause for every supplied representative avoids choosing one. Informally,
any two representatives factor through each other, but this file does not
prove that.

**Affineness.** The source's affineness argument cites Prasad–Yu,
Proposition 3.1: a flat group scheme of finite type over a DVR with affine
generic fibre is affine if and only if it is separated. The citation is the
registered author preprint `prasad-yu-2006-quasi-reductive-author-preprint`,
content SHA-256
`138d931a21fa522d97449c77acf429918826b1ef649be940d4721d616a1fc73b`,
printed p.5 / PDF p.5. The published version, J. Algebraic Geom. 15 (2006),
507–549, has different page numbers. This file neither imports nor assumes
that result. Proving it, or an equivalent affineness argument, is part of
the proof obligation.

This is a derived algebraic formulation of the finite-index,
perfect-residue specialization of A.7.1(1)–(4), not a literal transcription
of the printed statement.

## Remaining work and scope

A proof of `FiniteIndexEnlargementStatement` must construct the enlargement.
Following the source, it would glue copies of `M.group` along their common
generic fibre, extend the group law, and prove separatedness and
affineness. This module supplies no schematic closure, smoothening, bounded
stable lattice, building-stabilizer comparison, torus identification or
special-fibre quotient construction. In particular, it does not establish
`IntegralModelAxiomsStatement`.
