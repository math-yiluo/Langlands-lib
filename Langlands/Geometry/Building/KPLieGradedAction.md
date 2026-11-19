# The adjoint action on the graded pieces `𝔤_{x,r}/𝔤_{x,r+}` and `𝔤*_{x,r}/𝔤*_{x,r+}`

This module formalizes, at the level of rational points and for supplied
lattices, the actions of Kaletha–Prasad §13.3.4 on the strict graded pieces of
the Moy–Prasad Lie filtration and of its dual.

## Setting

`F` is a nonarchimedean local field with ring of integers `𝒪 = 𝒪[F]` and
maximal ideal `𝔪 = 𝓂[F]`. `G` is a group scheme over `Spec F` with
`[IsAffineHom G.X.hom]`. `P : ParahoricBuildingData G` and
`L : P.LieFiltrationData` are supplied data. For `x : P.Apartment` they give:

- the lattices `𝔤_{x,r} = L.lieFiltration x r` for `r ≥ 0` (Library,
  `Geometry.Building.KPLieFiltration`);
- their extension `L.lieFiltrationReal x r` to real `r`, the lattices
  `𝔤_{x,r+} = L.lieFiltrationPlusReal x r` (the supremum of the `𝔤_{x,s}`,
  `s > r`, which is KP's union under periodicity), and the dual lattices
  `𝔤*_{x,r} = L.dualLieFiltration x r` and `𝔤*_{x,r+} = L.dualLieFiltrationPlus x r`
  in `𝔤* = Module.Dual F 𝔤` (Library, `Geometry.Building.KPLieFiltrationDual`).

Here `𝔤 = GenericLie 𝒪[F] G` is the Lie algebra of `G`. The adjoint action of
`g ∈ G(F)` is the Library's `GenericLie.adjoint 𝒪[F] g`
(`GroupScheme.IntegralModel.LieLatticeAdjoint`), with `adjoint_mul` and
`adjoint_one`.

All declarations are in the namespace
`Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData`.

## Adjoint and coadjoint actions

- `adjointF g : 𝔤 →ₗ[F] 𝔤` is the adjoint action as an `F`-linear map.
  `adjointF_apply` says that it agrees with `GenericLie.adjoint 𝒪[F] g`, by
  `rfl`. Also proved: `adjointF_mul`, `adjointF_one` and `adjointF_inv_apply`.
- `coadjoint g : 𝔤* →ₗ[F] 𝔤*` is the coadjoint action
  `X ↦ X ∘ Ad(g⁻¹)`, defined as `(adjointF g⁻¹).dualMap`. The lemmas are
  `coadjoint_apply`, `coadjoint_mul` and `coadjoint_one`.

## The stabilizer of the filtration

- `filtrationStabilizer x : Subgroup (rationalPoints G)` is the set of `g`
  such that `Ad(g)` and `Ad(g⁻¹)` both map every `𝔤_{x,r}`, `r ≥ 0`, into
  itself. Closure under products and inverses follows from `adjoint_mul`.
- `adjoint_mem_lieFiltration`: an element `g` of the stabilizer maps
  `𝔤_{x,r}` into itself.
- `adjoint_mem_lieFiltrationReal`: `g` also maps the real-depth lattice
  `L.lieFiltrationReal x r` into itself, for every real `r`. This needs no
  periodicity, because `Ad(g)` is `𝒪`-linear: if `a • X ∈ 𝔤_{x,r+n}` for all
  `a ∈ 𝔪^n`, then `a • Ad(g) X = Ad(g)(a • X) ∈ 𝔤_{x,r+n}`.
- `adjoint_mem_lieFiltrationPlusReal`: `g` maps `𝔤_{x,r+}`, the supremum of the
  `𝔤_{x,s}` over `s > r`, into itself.
- `coadjoint_mem_dualLieFiltration`: `g` maps `𝔤*_{x,r}` into itself under
  the coadjoint action. For `X ∈ 𝔤*_{x,r}` and `Y ∈ 𝔤_{x,s}` with `s > -r`,
  `(coadjoint g X)(Y) = X(Ad(g⁻¹) Y)`, and `Ad(g⁻¹) Y ∈ 𝔤_{x,s}` because the
  stabilizer is a subgroup. So the membership criterion `mem_dualLieFiltration`
  holds.
- `coadjoint_mem_dualLieFiltrationPlus`: `g` maps `𝔤*_{x,r+}` into itself.

## The graded representations

- `gradedLie x r` (for real `r`) is the `𝒪`-module
  `𝔤_{x,r} ⧸ (𝔤_{x,r} ∩ 𝔤_{x,r+})`: the quotient of the real-depth lattice by
  the inverse image of `𝔤_{x,r+}`. Under periodicity, `𝔤_{x,r+} ≤ 𝔤_{x,r}`
  (`lieFiltrationPlusReal_le`) and `𝔤_{x,r+}` is KP's union
  `⋃_{s>r} 𝔤_{x,s}` (`mem_lieFiltrationPlusReal`), so `gradedLie x r` is
  KP's `𝔤_{x,r}/𝔤_{x,r+}`. For arbitrary supplied data `𝔤_{x,r+}` is only
  the supremum of the `𝔤_{x,s}`, `s > r`, and need not lie in `𝔤_{x,r}`.
  The representations below need no periodicity.
- `gradedAdjointMap x r g` is the map induced by `Ad(g)` on the quotient
  (`Submodule.mapQ` of the restriction). `gradedAdjointMap_mk` gives its value
  on a class, by `rfl`.
- **`gradedAdjoint x r : filtrationStabilizer x →* Module.End 𝒪 (gradedLie x r)`**
  is the representation on `𝔤_{x,r}/𝔤_{x,r+}`. It is the declaration of this
  unit.
- `dualGradedLie x r : Submodule 𝒪 (𝔤* ⧸ 𝔤*_{x,r+})` is the image of
  `𝔤*_{x,r}` in `𝔤* ⧸ 𝔤*_{x,r+}`. Since `𝔤*_{x,r+} ⊆ 𝔤*_{x,r}`
  (`dualLieFiltrationPlus_le`), this image is `𝔤*_{x,r}/𝔤*_{x,r+}` by the
  second isomorphism theorem. That isomorphism is not stated in Lean. The image
  form is used because the quotient of the subtype of `𝔤*_{x,r}` does not
  elaborate in this environment. The subtype's additive monoid comes from
  `LinearMap.addCommMonoid` and is not recognized as the one underlying an
  additive group, so `HasQuotient` is not found.
- `coadjointQuot x r g` is the map induced by the coadjoint action on
  `𝔤* ⧸ 𝔤*_{x,r+}`. `coadjointQuot_mk` gives its value on a class.
  `coadjointQuot_mem_dualGradedLie` says it preserves `dualGradedLie x r`.
- `dualGradedAdjoint x r : filtrationStabilizer x →* Module.End 𝒪 (dualGradedLie x r)`
  is the representation on `𝔤*_{x,r}/𝔤*_{x,r+}`. `dualGradedAdjoint_apply`
  gives its value.

## Restriction and factorization

- For a subgroup `H ≤ filtrationStabilizer x`, such as the parahoric subgroup
  `P.parahoricAt x`, `subgroupGradedAdjoint` and `subgroupDualGradedAdjoint`
  are the restricted representations.
- `ActsTriviallyOnGraded x r N` says that every `n ∈ N` and every
  `X ∈ 𝔤_{x,r}` satisfy `Ad(n) X - X ∈ 𝔤_{x,r+}`.
  `ActsTriviallyOnDualGraded x r N` says the same for the coadjoint action
  on `𝔤*_{x,r}` and `𝔤*_{x,r+}`.
- `le_ker_subgroupGradedAdjoint` and `le_ker_subgroupDualGradedAdjoint`: such
  an `N` lies in the kernel of the restricted representation of `H`, as the
  subgroup `N.subgroupOf H` of `H`.
- `quotientGradedAdjoint` and `quotientDualGradedAdjoint` take as input such an
  `N` with `N.subgroupOf H` normal in `H`. They are the induced representations
  of `H ⧸ N.subgroupOf H` (`QuotientGroup.lift`). `quotientGradedAdjoint_mk`
  says that the class of `h` acts as `h`. With `H = P_x` and `N = P_{x,0+}`
  (`Zf.moyPrasadPlus x 0` in `KPMoyPrasadFiltration`), this is an action of
  `P_x/P_{x,0+}`.

## From the Lie graded pieces to the dual graded pieces

`ActsTriviallyOnGraded` and `ActsTriviallyOnDualGraded` are separate
hypotheses on the supplied data. Neither the definitions nor periodicity make
the second a consequence of the first. What matters is the endpoint
convention of the filtration at the opposite depth, not whether its jumps are
discrete.

- `IsLeftContinuousAt x t` (definition): there is `s < t` with
  `𝔤_{x,u} ⊆ 𝔤_{x,t}` for every `u` with `s < u ≤ t`. For a decreasing
  filtration this says that `𝔤_{x,u} = 𝔤_{x,t}` for `u` in `(s, t]`. KP's
  filtration has this property at every depth, since its steps are cut out by
  non-strict inequalities `ψ(x) ≥ r` and its jumps are discrete. This module
  does not prove it for the supplied data; it is a hypothesis.
- `exists_lieFiltrationPlusReal_le hL hc`: under periodicity and left
  continuity at `t`, `𝔤_{x,s+} ⊆ 𝔤_{x,t}` for some `s < t`. For `u > s`, either
  `u ≤ t` and the hypothesis applies, or `u > t` and `lieFiltrationReal_antitone`
  applies.
- `actsTriviallyOnDualGraded_of_lieFiltrationPlusReal_le hN hs hle`: if `N`
  satisfies `ActsTriviallyOnGraded x (-r) N` and `𝔤_{x,s+} ⊆ 𝔤_{x,-r}` for some
  `s < -r`, then `N` satisfies `ActsTriviallyOnDualGraded x r N`. No
  periodicity is needed. For `n ∈ N`, `X ∈ 𝔤*_{x,r}` and `Y ∈ 𝔤_{x,s+}`,
  `(n·X - X)(Y) = X(Ad(n⁻¹) Y - Y)`. Since `Y ∈ 𝔤_{x,-r}` and `n⁻¹ ∈ N`, the
  difference `Ad(n⁻¹) Y - Y` lies in `𝔤_{x,(-r)+}`, where `X` takes values in
  `𝔪`. So `n·X - X ∈ 𝔤*_{x,-s}`, which lies in `𝔤*_{x,r+}` because `-s > r`.
- `actsTriviallyOnDualGraded_of_isLeftContinuousAt hL hc hN`: under
  periodicity and left continuity at `-r`, `ActsTriviallyOnGraded x (-r) N`
  implies `ActsTriviallyOnDualGraded x r N`.

The condition is local at `-r`: it concerns only an interval to the left of
`-r`, and it says nothing about whether the jumps elsewhere are discrete.
Without it the transfer can fail even for a periodic filtration with discrete
jumps. Take a lattice `W` and the
right-continuous family `𝔤_{x,t} = ϖ^{⌊t⌋} W`. Then `𝔤_{x,t+} = 𝔤_{x,t}` for
every `t`, so every graded piece `𝔤_{x,t}/𝔤_{x,t+}` is zero and every subgroup
satisfies `ActsTriviallyOnGraded` at every depth. On the dual side,
`𝔤*_{x,0}` consists of the forms with `X(W) ⊆ 𝔪`, and `𝔤*_{x,0+}` of those with
`X(W) ⊆ 𝔪²`, because `𝔤_{x,u} = ϖ^{-1} W` for `-1 ≤ u < 0`. For `W` the
diagonal lattice in `𝔤𝔩₂`, the coordinate swap preserves every `𝔤_{x,t}`. It
moves `X = ϖ·(first diagonal entry)` to `ϖ·(second diagonal entry)`, and the
difference takes the value `-ϖ ∉ 𝔪²` on the first diagonal matrix unit. So the
swap acts nontrivially on `𝔤*_{x,0}/𝔤*_{x,0+}`. This family is not
left-continuous at `0`.

## Comparison with Kaletha–Prasad

Kaletha–Prasad, 13.3.4 (printed p. 471; PDF p. 502), reads: "Let `x ∈ B(G)`.
As `G(K)_{x,r}` is a normal subgroup of `G(K)^0_x` by Proposition 13.2.5, the
conjugation action of `G` on itself extends (see Corollary 2.10.10) to an action
of the group scheme `𝒢_x^0` on the group scheme `𝒢_{x,r}`, and hence also on
the Lie algebra `𝔤_{x,r}` and its dual `𝔤*_{x,r}`, for all `r ∈ ℝ`. This action
descends to a k-rational action of `𝒢̄_x^0` on `𝔤_{x,r} ⊗_o 𝔣`, which induces
an `𝔣`-rational action of the reductive quotient `Gred_x` on
`𝔤_{x,r}/𝔤_{x,r+}`, as well as on `𝔤*_{x,r}/𝔤*_{x,r+}`." The extracted text
has "k-rational" in the second sentence, with `𝒢̄_x^0` the special fibre over
the residue field.

The module relates to this as follows.

- The integral-model action of `𝒢_x^0` on `𝒢_{x,r}` is not constructed.
  Instead, the module works with the group of rational points that stabilize
  the supplied lattices. KP's statement that `𝒢_x^0(o) = P_x` preserves
  `𝔤_{x,r}` becomes the hypothesis `P.parahoricAt x ≤ filtrationStabilizer x`
  of the restricted representations. For the Lie lattice of a single supplied
  model, the Library's `IntegralModel.map_adjoint_lieLattice` proves this
  preservation.
- What the module proves, rather than assumes, is the passage to the
  real-depth lattices, to `𝔤_{x,r+}` and to the dual lattices
  `𝔤*_{x,r}`, `𝔤*_{x,r+}`. Stabilizing all `𝔤_{x,r}`, `r ≥ 0`, implies
  stabilizing all of them, for every real `r`.
- KP's factorization through `Gred_x` becomes, at the level of points, the
  factorization through `H ⧸ N`. The triviality of `N` (for KP,
  `P_{x,0+}`, the kernel of `P_x → Gred_x(𝔣)` by 13.2.6) is the hypothesis
  `ActsTriviallyOnGraded` or `ActsTriviallyOnDualGraded`. Under periodicity
  and left continuity at `-r`, the first at depth `-r` implies the second at
  depth `r` (`actsTriviallyOnDualGraded_of_isLeftContinuousAt`).

The corrections of 1 November 2024 have no entry for §13.3, Proposition 13.2.5
or Corollary 2.10.10.

## Provenance

Derived. The definitions transcribe the actions of KP 13.3.4 at the level of
rational points, for the supplied lattices of `KPLieFiltration` and
`KPLieFiltrationDual`. The following are internal: the stabilizer subgroup, the
image form of the dual graded piece, the predicates for trivial action, the
left-continuity predicate and the transfer criterion between the two trivial-action
predicates. The Lean code uses the Library's `GenericLie.adjoint`, `adjoint_mul`,
`adjoint_one` (`IntegralModel.LieLatticeAdjoint`) and
`GroupScheme.adjoint`. It also uses `lieFiltration`, `lieFiltrationReal`,
`mem_lieFiltrationReal`, `lieFiltrationPlusReal`,
`lieFiltrationReal_le_lieFiltrationPlusReal`, `IsPeriodic`,
`lieFiltrationReal_antitone`, `dualLieFiltration`, `mem_dualLieFiltration`,
`dualPairingSubmodule`, `mem_dualPairingSubmodule`, `dualLieFiltrationPlus` and
`mem_dualLieFiltrationPlus` (`KPLieFiltration`, `KPLieFiltrationDual`). From Mathlib it uses `LinearMap.dualMap`,
`Submodule.mapQ`, `LinearMap.restrict` and `QuotientGroup.lift`. No external
code is adapted.

## Not claimed

- The action of the group scheme `𝒢_x^0` on `𝒢_{x,r}` (KP Corollary 2.10.10)
  and on the lattices is not constructed. The representations are of groups of
  rational points on `𝒪`-modules. They are not shown to come from algebraic
  (`𝔣`-rational) representations of `Gred_x`.
- That `P_x` stabilizes the supplied filtration, and that `P_{x,0+}` acts
  trivially on the graded pieces, are hypotheses. They are not proved for
  supplied data.
- The identification of `P_x/P_{x,0+}` with `Gred_x(𝔣)` (KP 13.2.6) is not
  connected to these data here.
- The isomorphism between `dualGradedLie x r` and the quotient
  `𝔤*_{x,r}/𝔤*_{x,r+}` is not stated. The `𝔣`-vector-space structure of the
  graded pieces and the pairing between `𝔤_{x,r}/𝔤_{x,r+}` and
  `𝔤*_{x,-r}/𝔤*_{x,(-r)+}` are not treated.
