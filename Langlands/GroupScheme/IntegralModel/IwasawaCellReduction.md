# Maximal compactness from opposite Iwasawa coverings and cell integrality

Author: Worker 4686.

This internal module gives a conditional reduction of the published
`Langlands.GroupScheme.IntegralModel.MaximalCompactStatement` to an explicit
datum, `IwasawaCellData M`, built from opposite subgroups of the generic group.
It does not construct that datum, and it does not prove the published
statement unconditionally. It is an alternative to the building route of
`BuildingComparison.lean`: no building, metric or fixed-point theorem is used.

## Setting

Throughout, `F : Type u` is a field with `[ValuativeRel F]`,
`[TopologicalSpace F]` and `[IsNonarchimedeanLocalField F]`, `G` is a group
scheme over `Spec F`, and `M : IntegralModel 𝒪[F] F G` is a supplied model over
the canonical valuation integers. `M.integralPoints` is the existing image of
the model's integral sections in `rationalPoints G`, through the supplied
generic isomorphism. Topologies on rational points are always the existing
`rationalPointTopology`.

## The datum `IwasawaCellData M`

The structure has the following fields.

* Three group schemes over `Spec F`: `parabolic` (written `P`),
  `oppositeParabolic` (`P⁻`) and `levi` (`Z`), each with an affine structure
  morphism (`IsAffineHom`, registered as instances).
* Homomorphisms `parabolicHom : P ⟶ G` and `oppositeParabolicHom : P⁻ ⟶ G`
  whose underlying scheme morphisms are closed immersions
  (`parabolicHom_closed`, `oppositeParabolicHom_closed`), and a homomorphism
  `leviHom : Z ⟶ G`.
* Sections `leviSection : Z ⟶ P`, `oppositeLeviSection : Z ⟶ P⁻` and
  retractions `leviProj : P ⟶ Z`, `oppositeLeviProj : P⁻ ⟶ Z`. Both sections
  followed by the inclusions into `G` equal `leviHom`
  (`leviSection_comp`, `oppositeLeviSection_comp`), and both sections followed
  by the corresponding retractions are the identity of `Z`
  (`leviSection_proj`, `oppositeLeviSection_proj`).
* `iwasawa`: `Set.range (rationalPoints.map parabolicHom) * M.integralPoints`
  is all of `rationalPoints G`; that is, `G(F) = P(F) · M(𝒪)`.
  `oppositeIwasawa` is the same equality for `P⁻`.
* `levi_maximal`: for the rational-point topology on `Z(F)`, every compact
  subgroup `C` of `Z(F)` that contains
  `M.integralPoints.comap (rationalPoints.map leviHom)` (the points of `Z(F)`
  whose image in `G(F)` is integral) is contained in it.
* `cell_integral`: if `v ∈ P⁻(F)` and `w ∈ P(F)` lie in the kernels of the two
  retractions, and the product of their images in `G(F)` lies in
  `M.integralPoints`, then the image of `w` lies in `M.integralPoints`.

`IwasawaCellDataStatement.{u}` is the proposition that such a datum exists for
every `F`, every `G` with `IsConnectedReductive G`, and every supplied `M`
whose actual special-fibre pullback
`(GroupScheme.baseChange (Spec.algebraMap 𝒪[F] 𝓀[F])).obj M.group` is connected
reductive. These are exactly the quantifiers and hypotheses of
`MaximalCompactStatement`. It is an internal construction target; this module
does not prove it.

## Main results

`IwasawaCellData.maximalCompact` assumes `[IsAffineHom G.X.hom]` and
`D : IwasawaCellData M`. It proves compactness of `M.integralPoints` and
`L = M.integralPoints` for every compact subgroup `L` of `G(F)` with
`M.integralPoints ≤ L`.

`maximalCompactStatement_of_iwasawaCellData` deduces the exact
`MaximalCompactStatement.{u}` from `IwasawaCellDataStatement.{u}`. It obtains
the affine instance from `hG.isAffineHom`, as the target does, and applies
`maximalCompact`.

## Implemented proof

Write `K = M.integralPoints`, and let `L ⊇ K` be a compact subgroup.
Compactness of `K` is the published `isCompact_integralPoints_localField`.
It remains to show `L ≤ K`; the reverse inclusion is the hypothesis.

1. *Iwasawa factors* (`exists_integral_mul`). From `G(F) = P(F) · K` applied to
   `g⁻¹`, every `g` is `k · i(b)` with `k ∈ K` and `b ∈ P(F)`.
2. *Compact retraction images* (`isCompact_retract_image`). For a closed
   subgroup `i : P ⟶ G` and a homomorphism `p : P ⟶ Z`, the subgroup
   `p(i⁻¹(L))` of `Z(F)` is compact. The published
   `isClosedEmbedding_rationalPointMap` makes `i` a closed embedding on
   rational points (the field is Hausdorff), so `i⁻¹(L)` is compact, and
   `continuous_rationalPointMap` makes its image compact.
3. *Kernel factors* (`exists_kernel_factor`). Let `b ∈ P(F)` with
   `i(b) ∈ L`, and `t = p(b)`. The compact subgroup `p(i⁻¹(L))` contains
   every `z ∈ Z(F)` with integral image: the section `s(z)` lies in `P(F)`,
   its image `i(s(z))` equals the image of `z` in `G(F)`, which lies in
   `K ⊆ L`, and `p(s(z)) = z`. By `levi_maximal`, the image of `t` in `G(F)`
   is integral. Put `w = s(t)⁻¹ · b`. Then `p(w) = 1`, `i(w) ∈ L`, and
   `i(b) = k · i(w)` with `k` the integral image of `t`.
4. *Assembly* (`maximalCompact`). Given `l ∈ L`, step 1 for `P` gives
   `l = k₁ · i(b)`; since `k₁ ∈ L`, also `i(b) ∈ L`. Step 3 gives
   `i(b) = k₂ · i(w)` with `w` in the kernel of `P → Z` and `i(w) ∈ L`.
   Step 1 for `P⁻` gives `i(w) = k₃ · i⁻(c)`, so `i⁻(c) ∈ L`, and step 3 for
   `P⁻` gives `i⁻(c) = k₄ · i⁻(v)` with `v` in the kernel of `P⁻ → Z`.
   Hence `i⁻(v) · i(w⁻¹) = (k₃ k₄)⁻¹ ∈ K`. Since `w⁻¹` is also in the kernel,
   `cell_integral` gives `i(w⁻¹) ∈ K`, so `i(w) ∈ K`, and
   `l = k₁ k₂ i(w) ∈ K`.

Only group laws, the two closed embeddings, continuity and the four
conditions of the datum are used. The universe `u` is arbitrary, and no
characteristic or residue-field restriction is imposed.

## Provenance and intended instances

The reduction is derived internally. Its structure follows the final steps of
Marco Maculan, *Maximality of hyperspecial compact subgroups avoiding
Bruhat–Tits theory*, Ann. Inst. Fourier 67(1) (2017), 1–21, registered as
`maculan-2017-hyperspecial-maximality`: the Iwasawa decomposition
(Proposition 4.2(3), printed pp.9–10 / PDF pp.10–11), the torus step
(Proposition 4.6, printed p.11 / PDF p.12, and the Claim in Lemma 5.1,
printed p.14 / PDF p.15), and the unipotent step (Lemma 5.2, printed
pp.14–15 / PDF pp.15–16). Maculan's unipotent
step uses a metric on the flag variety; here it is replaced by the second
Iwasawa covering and the cell condition, so no metric is needed. The Lean
statements above are not taken from that paper.

The intended instance, which this module does not construct, takes `P` and
`P⁻` to be the generic fibres of opposite Borel subgroups of `M.group` over
`𝒪[F]` and `Z` the generic fibre of their common maximal torus. Over a finite
residue field such a pair exists by Maculan's Propositions 4.1 and 4.2(1)
(printed pp.9–10 / PDF pp.10–11).
The Iwasawa coverings are then instances of the published
`IntegralParabolicCovering.range_mul_integralPoints_eq_univ`, whose quotient
hypotheses are supplied by the published theorem
`Langlands.Global.IntegralIwasawaFamily.relativeParabolicQuotient`, a proof of
`RelativeParabolicQuotient.ExistenceStatement`. Every compact subgroup of the
torus's rational points then lies in the integral points of the model torus
(Maculan, Proposition 4.6). The cell condition expresses integrality of the
open cell `U⁻ × T × U` of `M.group` at points whose torus component is `1`.
Each of these is a separate obligation.

The fields also allow a parabolic subgroup with a reductive Levi factor in
place of a Borel subgroup. Then `levi_maximal` is a maximality property of the
integral points of the Levi factor, a form suited to induction on dimension.
