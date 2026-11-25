# The Lie algebra of the reductive quotient: `g_{x,0} / g_{x,0+}`

This module formalizes Kaletha–Prasad §13.3.2 for supplied integral-model data.
Let `R` be a local domain with fraction field `K`, maximal ideal `𝔪` and
residue field `𝔣`. Let `G` be a group scheme over `Spec K`. Fix the following
data.

- `D : RelativeComponentModelData R K G` (Library,
  `BruhatTits.IntegralModels.RelativeComponent`). Its neutral model
  `𝒢° = D.neutral` is a smooth model of `G` (`D.neutral_smooth`) with connected
  fibres. For a point `x` of the building, `𝒢°` plays the role of the
  parahoric group scheme `𝒢_x^0 = 𝒢_{x,0}`.
- `Q : SpecialFibreQuotientData D` (Library,
  `BruhatTits.IntegralModels.SpecialFibre`). It consists of a group `R_u` with
  `Q.radicalInclusion : R_u ⟶ H`, where `H = D.neutral.specialFibre` is the
  special fibre of `𝒢°`, and a group `Gred` with
  `Q.projection : H ⟶ Gred`.
- `hQ : Q.IsReductiveQuotient`. This says three things: `R_u` is the unipotent
  radical of `H` (the greatest smooth connected normal unipotent closed
  subgroup), `Q.projection` is an fppf quotient of `H` by the image of `R_u`,
  and `Gred` is connected reductive. So `Gred` is the maximal reductive
  quotient of `H`, as in KP 13.2.6.

The lattices are `g_0 = D.neutral.lieLattice ⊆ GenericLie R G` (Library,
`IntegralModel.LieLattice`; this is KP's `𝔤_{x,0}`) and the lattice `g_0+`
defined below. Reduction `Lie(𝒢°) → Lie(H)` is
`IntegralModel.lieReduction` from the companion module
`Langlands.GroupScheme.IntegralModel.LieLatticeReduction`.

All declarations are in the namespace
`Langlands.BruhatTits.IntegralModels.SpecialFibreQuotientData`.

## KP §2.4(a) on the special fibre

Assume `hQ`.

- `radical_isAffineHom`: `R_u` is affine over `Spec 𝔣`. The inclusion is a
  closed immersion (`hQ.1.isClosedSubgroup`), and `H` is affine over `Spec 𝔣`.
- `radical_lie_eq_range`: the tangent submodule
  `(SubgroupFunctor.range Q.radicalInclusion).lie 𝔣` of the image of `R_u` is
  the range of the differential of `Q.radicalInclusion`. This is the Library's
  `SubgroupFunctor.lie_eq_range` applied to the closed immersion.
- `specialFibreLieQuotientEquiv hQ :
  (Lie(H) ⧸ (SubgroupFunctor.range Q.radicalInclusion).lie 𝔣) ≃ₗ[𝔣] Lie(Gred)`,
  where `Lie(H)` and `Lie(Gred)` are the identity kernels with coefficients
  in `𝔣`. It is induced by the differential of `Q.projection`. The Library's
  `ker_projection_eq_radical_lie` identifies the kernel of the differential.
  It is surjective by `projection_smooth` and
  `Lie.targetMapLinear_surjective_of_smooth`. Both `ker_projection_eq_radical_lie`
  and `projection_smooth` are in `BruhatTits.IntegralModels.ReductiveQuotientRoots`.
  `specialFibreLieQuotientEquiv_mk` gives the value on a class, by `rfl`.

## The positive lattice `g_0+` and the isomorphism `g_0 ⧸ g_0+ ≃ Lie(Gred)`

From here on assume `[IsAffineHom G.X.hom]`.

- `radicalLie : Submodule R (GenericLie R H)` is the tangent submodule of the
  image of `R_u`, viewed as an `R`-submodule of `GenericLie R H`.
  `mem_radicalLie` unfolds membership, by `Iff.rfl`. Under `hQ`,
  `mem_radicalLie_iff` says that `X ∈ radicalLie` exactly when `X` is the
  differential `GenericLie.map R Q.radicalInclusion Z` of some `Z ∈ Lie(R_u)`.
- `positiveLieLattice : Submodule R (GenericLie R G)` is the lattice `g_0+`.
  It is the image under the Lie map `D.neutral.lieMap : Lie(𝒢°) → Lie(G)` of
  those `X ∈ Lie(𝒢°)` whose reduction `D.neutral.lieReduction X` lies in
  `radicalLie`. Thus, inside `g_0`, `g_0+` is the inverse image of `Lie(R_u)`
  under reduction. This definition uses no model for `𝒢_{x,0+}`.
- `positiveLieLattice_le`: `g_0+ ≤ g_0`.
- `smul_lieLattice_le_positiveLieLattice`: `𝔪 • g_0 ≤ g_0+`. The reduction of
  `𝔪 • Lie(𝒢°)` is zero (`smul_top_le_ker_lieReduction`).
- `reductiveLieMap : Lie(𝒢°) →ₗ[R] GenericLie R Gred` is reduction followed by
  the differential of `Q.projection`. `latticeReductiveLieMap` is the same map
  on `g_0`, through the Library's `D.neutral.lieLatticeEquiv`.

Assume `hQ` again.

- `map_projection_eq_zero_iff`: for `X ∈ Lie(H)`, the differential of
  `Q.projection` kills `X` exactly when `X ∈ radicalLie`. This is
  `ker_projection_eq_radical_lie`, moved to `GenericLie`.
- `ker_reductiveLieMap`: the kernel of `reductiveLieMap` is the inverse image
  of `radicalLie` under reduction.
- `reductiveLieMap_surjective`: reduction is surjective because `𝒢°` is smooth
  (`IntegralModel.lieReduction_surjective`). The differential of the smooth
  projection is surjective (`GenericLie.map_surjective`).
- `ker_latticeReductiveLieMap`: the kernel of `latticeReductiveLieMap` is
  `g_0+`, viewed inside `g_0`. The proof uses `ker_reductiveLieMap` and the
  injectivity of the Lie map (`IntegralModel.lieMap_injective`).
- `latticeReductiveLieMap_surjective`.
- **`reductiveQuotientLieEquiv hQ`** (the declaration of this module):
  `(g_0 ⧸ g_0+) ≃ₗ[R] GenericLie R Gred`. Here `g_0+` is viewed as a submodule
  of `g_0` (`Q.positiveLieLattice.comap D.neutral.lieLattice.subtype`). It is
  the first isomorphism theorem (`LinearMap.quotKerEquivOfSurjective`) for
  `latticeReductiveLieMap`.

## The conditional KP form: `g_0+` as the Lie lattice of a model

KP define `𝔤_{x,0+}` as the Lie algebra of the integral model `𝒢_{x,0+}`.
This module does not construct that model. Instead it takes a supplied model.

- `N : IntegralModel R K G` is a model with a model homomorphism
  `φ : N.Hom D.neutral (𝟙 G)`, so `N` maps to `𝒢°` over the identity of `G`.
- `s : N.specialFibre ⟶ R_u` and
  `hs : φ.specialFibreMap = s ≫ Q.radicalInclusion` say that the special-fibre
  map of `φ` factors through the radical.

Under these hypotheses and `hQ`:

- `lieLattice_le_positiveLieLattice`: `N.lieLattice ≤ g_0+`. The reduction of
  the differential of `φ` factors through `Lie(R_u)`. This uses
  `Hom.lieReduction_naturality` from the companion module and `hs`. Its image
  in `Lie(G)` is `N.lieLattice` (`Hom.lieMap_naturality` and
  `GenericLie.map_id`).
- `exists_lieReduction_eq` (the lifting step): suppose `N` is smooth and `s`
  is smooth (`Smooth s.hom.hom.left`). If `X ∈ Lie(𝒢°)` has reduction in
  `radicalLie`, then some `Y ∈ Lie(N)` has
  `lieReduction (dφ Y) = lieReduction X`. To find `Y`, write the reduction of
  `X` as `d(radicalInclusion) Z`. Since `s` is smooth, `ds` is surjective, so
  `Z = ds W` for some `W ∈ Lie(N_𝔣)`. Since `N` is smooth, reduction from
  `Lie(N)` is surjective, so `W` is the reduction of some `Y`. Then use
  naturality of reduction and `GenericLie.map_comp`.
- `lieMap_eq_add` (`IsLocalRing`, `hQ` and `hs` not needed): for `X ∈ Lie(𝒢°)` and
  `Y ∈ Lie(N)`,
  `D.neutral.lieMap X = N.lieMap Y + D.neutral.lieMap (X - dφ Y)`.
- `positiveLieLattice_eq_sup`: if `N` and `s` are smooth, then
  `g_0+ = N.lieLattice ⊔ 𝔪 • g_0`. For `≤`, the difference `X - dφ Y` from
  `exists_lieReduction_eq` lies in the kernel of reduction. That kernel is
  `𝔪 • Lie(𝒢°)` because `𝒢°` is smooth (`IntegralModel.ker_lieReduction`).
- `positiveLieLattice_eq`: if moreover `𝔪 • g_0 ≤ N.lieLattice`, then
  `g_0+ = N.lieLattice`.
- `lieLatticeQuotientEquiv`: under the same hypotheses,
  `(g_0 ⧸ N.lieLattice) ≃ₗ[R] GenericLie R Gred`.

## Comparison with Kaletha–Prasad

Kaletha–Prasad, 13.3.2 (printed p. 470; PDF p. 501), reads: "Let `Gred_x`
denote the maximal reductive quotient of the special fiber of the parahoric
group scheme `𝒢_x^0`. According to 13.2.6, `Gred_x = cok(𝒢̄_{x,0+} → 𝒢̄_{x,0})`.
From the discussion of §2.4(a) and the smoothness of
`ker(𝒢̄_{x,0+} → 𝒢̄_{x,0})` due to Proposition 8.5.18, we see that
`Lie(Gred_x) = cok(𝔤_{x,0+} ⊗_o 𝔣 → 𝔤_{x,0} ⊗_o 𝔣) = 𝔤_{x,0}/𝔤_{x,0+}`,
where the last identity comes from the inclusions
`𝔪 · 𝔤_{x,0} ⊂ 𝔤_{x,0+} ⊂ 𝔤_{x,0}` of `o`-lattices in the `k`-vector space
`𝔤 = Lie(G)`."

KP §2.4(a) (printed pp. 81–82) is about a homomorphism `A → B` of smooth affine
algebraic groups over a perfect field, with kernel `K`. When the image is
normal, `cok(A → B)` is the quotient of `B` by the image. KP state that the
following are equivalent: "(1) `K` is smooth. (2) The inclusion
`im(Lie(A) → Lie(B)) ⊂ Lie(im(A → B))` is an equality. (3) The surjection
`cok(Lie(A) → Lie(B)) → Lie(cok(A → B))` is an isomorphism."

The module relates to these statements as follows.

- `specialFibreLieQuotientEquiv` is the case of §2.4(a)(3) where `A` is the
  radical `R_u` and `A → B` is its closed immersion into `H`. The kernel is
  trivial, so the statement is that `Lie(H)/Lie(R_u) ≃ Lie(Gred)`. The field
  `𝔣` need not be perfect: the radical and the quotient are supplied with the
  properties stated in `IsReductiveQuotient`.
- The intrinsic lattice `g_0+` satisfies `𝔪 • g_0 ≤ g_0+ ≤ g_0`, and
  `reductiveQuotientLieEquiv` gives `g_0/g_0+ ≃ Lie(Gred)`. Both hold
  unconditionally for the supplied data.
- KP's `𝔤_{x,0+}` is `Lie(𝒢_{x,0+})`. The module identifies `g_0+` with the
  Lie lattice of a supplied model `N` (`positiveLieLattice_eq`). It needs
  three hypotheses, each standing for a step that KP take from elsewhere.
  The homomorphism `φ` stands for KP 8.5.17's `ρ : 𝒢_{x,0+} → 𝒢_{x,0}`,
  which extends the identity of `G`.
  - The factorization `hs` through the radical stands for 13.2.6: the image of
    `𝒢̄_{x,0+} → 𝒢̄_{x,0}` is the kernel of the map to `Gred_x`.
  - The smoothness of `s` stands for Proposition 8.5.18. KP apply (1) ⇒ (3)
    of §2.4(a) to `A = 𝒢̄_{x,0+}` and `B = 𝒢̄_{x,0}`, whose kernel is smooth
    by 8.5.18. In the module, smoothness of `s` makes the differential `ds`
    surjective. This is statement (2) for `A → B`, and together with
    `specialFibreLieQuotientEquiv` it gives (3). The hypothesis follows from
    8.5.18: `s` is the faithfully flat map of `A` onto its image `R_u`, and
    its kernel is smooth, so `s` is flat with smooth fibres.
  - `𝔪 • g_0 ≤ N.lieLattice` stands for the inclusion
    `𝔪 · 𝔤_{x,0} ⊂ 𝔤_{x,0+}` quoted above.
  The smoothness of `N` itself is also assumed. KP's `𝒢_{x,0+}` is smooth by
  construction (Theorem 8.5.2).

The corrections of 1 November 2024 have no entry for §2.4, §8.5, 13.2.6 or
§13.3.

## Provenance

Derived. The statements are those of KP §13.3.2 and §2.4(a) for supplied data,
as explained above. The definition of `g_0+` as an inverse image under
reduction is internal: KP define `𝔤_{x,0+}` through the model `𝒢_{x,0+}`. The
Lean route is internal and composed from published Library constructions.
These are `SpecialFibreQuotientData`, `IsReductiveQuotient`
(`BruhatTits.IntegralModels.SpecialFibre`), `projection_smooth` and
`ker_projection_eq_radical_lie` (`BruhatTits.IntegralModels.ReductiveQuotientRoots`),
`SubgroupFunctor.lie_eq_range` (`Lie.SubgroupTangent`),
`Lie.targetMapLinear_surjective_of_smooth` (`Lie.SmoothDifferential`), and
`IntegralModel.lieMap`, `lieMap_injective`, `lieLattice`, `lieLatticeEquiv`,
`Hom.lieMap_naturality` (`IntegralModel.LieLattice`). They also include the
companion module's `lieReduction`, `smul_top_le_ker_lieReduction`,
`lieReduction_surjective`, `ker_lieReduction`, `Hom.lieReduction_naturality`,
`GenericLie.map_id`, `map_comp` and `map_surjective`. The quotient
isomorphisms use Mathlib's `LinearMap.quotKerEquivOfSurjective` and
`Submodule.quotEquivOfEq`. No external code is adapted.

## Not claimed

- The Moy–Prasad models `𝒢_{x,0+}` and `𝒢_{x,r}` (KP Theorem 8.5.2) are not
  constructed. KP's `𝔤_{x,0+} = Lie(𝒢_{x,0+})` appears only through the
  conditional results for a supplied model `N`.
- Proposition 8.5.18 (smoothness of `ker(𝒢̄_{x,0+} → 𝒢̄_{x,0})`), the
  identification 13.2.6 of `Gred_x` as a cokernel, and the inclusion
  `𝔪 · 𝔤_{x,0} ⊂ 𝔤_{x,0+}` are not proved. In the conditional results they are
  replaced by the hypotheses `hs`, `Smooth s.hom.hom.left` and
  `𝔪 • g_0 ≤ N.lieLattice`.
- The general equivalence of KP §2.4(a) for an arbitrary homomorphism `A → B`
  is not formalized. Only the case of the radical inclusion is treated.
- The Lie bracket is not treated: all isomorphisms are of modules.
- `reductiveQuotientLieEquiv` is `R`-linear. The induced `𝔣`-module structure
  on `g_0/g_0+` is not constructed.
- The filtration `𝔤_{x,r}` for `r ≠ 0, 0+` and the dual lattices `𝔤*_{x,r}`
  are not treated.
