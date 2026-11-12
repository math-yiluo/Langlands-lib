# Harris's divisible systems on the quasi-étale site of an analytic space

Author: Worker 26. Builds on the following modules:

- `Langlands.Sheaf.Equivariant.AnalyticQuasiEtaleCompactCohomology` (Worker 26). It gives
  the points `quasiEtalePoints L h x` of the quasi-étale site at the `L`-valued points
  of `X`, essential smallness of the quasi-étale and twisted quasi-étale sites,
  sheafification (`quasiEtale_hasSheafify`, `twistedQuasiEtale_hasSheafify`), enough
  injectives (`twistedQuasiEtale_enoughInjectives`), compactly supported sections
  `quasiEtaleGSheafCompactSections` (`Γ_{c,X{G}}`) and Berkovich's compactly supported
  cohomology `quasiEtaleGSheafCompactCohomology L ρ h R q` (`H^q_c(X{G}, -)`) of
  quasi-étale `G`-sheaves.
- `Langlands.Cohomology.DivisibleSystem.TwistedInverseLimit` (Worker 26), and through it
  `TwistedTruncation`, `DivisibleSystem.TwistedGodement` and
  `Langlands.Sheaf.Equivariant.TwistedGodement` (all Worker 26). They give Harris's
  constructions of §2 for discrete sheaves of a local action system on an arbitrary
  twisted site: the discrete Godement functor `discreteZeroFunctor` with its
  coaugmentation, the Godement resolution system (Lemma 2.2), its truncation (Lemma
  2.2 bis), the compact section system and (2.3), the complexes `C^•_m`, (2.6), (2.7) and
  Lemma 2.8.
- From Worker 21, through these modules: the quasi-étale site `QuasiEtaleSite X`, the
  point axioms `QuasiEtaleSite.PointAxioms L x` and the point equivariance
  `QuasiEtaleSite.pointEquivariance L ρ h`.
- Worker 3's statements `ProPInvariantSubcomplexStatement` and
  `FiniteCohomologyInverseLimitStatement`. Neither is proved in the Library. They appear
  here only as hypotheses `hS` and `hS'`.

All declarations are in the namespace `Langlands.Cohomology.DivisibleSystem.Analytic`.

## Purpose

Harris's §2 works with étale sheaves on an analytic space `U(ẽ)` with an action of a
group `S(ẽ)`. The published `DivisibleSystem` modules carry out his constructions for an
arbitrary twisted site. This module applies them to Berkovich's quasi-étale `G`-sheaves
on a `K`-analytic space `X` (`QuasiEtaleGSheaf ρ`, the discrete sheaves of the lift
system `compactLiftSystem ρ` on the twisted quasi-étale site). The Godement resolutions
use the `L`-valued points of `X`, and the compactly supported cohomology is
`H^q_c(X{G}, -)` of `AnalyticQuasiEtaleCompactCohomology`.

The one new mathematical input is the existence of the right Kan extensions that define
the Godement functor. Every other declaration instantiates a published twisted-site
declaration with the quasi-étale site `quasiEtaleTopology X`, the lift system
`compactLiftSystem ρ`, the points `quasiEtaleGodementPoints L h`, the compact-support
points `quasiEtalePoints L h` with their equivariance
`QuasiEtaleSite.pointEquivariance L ρ h`, and the size, sheafification and injectivity
results of `AnalyticQuasiEtaleCompactCohomology`. The twisted-site modules take the
latter as instances; here they are supplied locally with `haveI`, because Lean's
instance search cannot solve the universe constraints of
`AnalyticQuasiEtaleCompactCohomology`'s theorems.

## Data and universes

- `K : Type u` is a complete ultrametric normed field, and `X` an object of Worker 21's
  `LocalizedCategory.{u, v, v} (K := K)`.
- `G` is a group with `ρ : G →* Aut X`. It lies in `Type z`, except in the section on
  inverse limits, where `G : Type u` (see below). All declarations except the Kan
  extension theorem assume `[TopologicalSpace G]`. Those on compact sections and on
  inverse limits also assume `[IsTopologicalGroup G]`.
- `L : Type uL` is a normed field with `[NormedAlgebra K L]`, and
  `h : ∀ x, QuasiEtaleSite.PointAxioms L x` says that every `L`-valued point of `X`
  satisfies the point axioms of the quasi-étale site.
- Coefficients: write `w = max u (v + 1) uL`, the universe of Worker 21's points. The
  ring `R : Type w` is commutative, and sheaves take values in `ModuleCat.{w} R`.
- `[Small.{w} G]`. It holds whenever `G` lies in a universe at most `w`, in particular
  for `G : Type u`.
- `[(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedQuasiEtaleTopology ρ)]`,
  assumed by all declarations except the Kan extension theorem. It is the published
  condition that makes quasi-étale `G`-sheaves an abelian category (see
  `AnalyticQuasiEtaleCompactCohomology`). It is not proved.

## Hypotheses of Harris's constructions

As in the twisted-site modules, the following are hypotheses. The first three are
Harris's Fact 3, the acyclicity of Berkovich's `F(T)` and Harris's Fact 2.

- `[PreservesFiniteLimits (quasiEtaleGodementFunctor L ρ h R)]` and
  `[PreservesFiniteColimits (quasiEtaleGodementFunctor L ρ h R)]`: the Godement functor is
  exact (Harris's Fact 3).
- `hF`: every `H^{r+1}_c(X{G}, G⁰(M))` vanishes, that is, Godement sheaves are acyclic
  for `Γ_{c,X{G}}`.
- `hT`: `H^n_c(X{G}, T m) = 0` for all `m` and all `n > D` (Harris's Fact 2 bounds the
  cohomological dimension by `D`).
- `hpoints`: the fibre functors at the `L`-valued points,
  `(quasiEtalePoints L h x).sheafFiber`, are jointly faithful on module sheaves on the
  quasi-étale site.

## Kan extensions

- `quasiEtale_hasPointwiseRightKanExtension ρ R F` (with `[Small.{w} G]`): every presheaf
  `F` of `R`-modules on `QuasiEtaleSite X` has a pointwise right Kan extension along the
  opposite of the inclusion `ι quasiEtale ρ` into the twisted quasi-étale site. The value
  at an object `Y` is a limit over `StructuredArrow Y (ι quasiEtale ρ).op`. That category
  is essentially small in `w` (Mathlib's `StructuredArrow.essentiallySmall`), because both
  sites are (`quasiEtaleSite_essentiallySmall_points`,
  `twistedQuasiEtale_locallySmall_points`). So the limit exists in `ModuleCat.{w} R`
  (Mathlib's `hasLimitsOfShape_of_essentiallySmall`).

This is the instance that `discreteZeroFunctor` requires. The definitions below supply
it locally.

## Godement functor

- `quasiEtaleGodementPoints L h`: the points `quasiEtalePoints L h x`, indexed by
  `ULift.{w}` of the `L`-valued points of `X`. The published Godement construction needs
  an index type in the universe of the points.
- `jointlyFaithful_quasiEtaleGodementPoints L h R hpoints`: joint faithfulness passes to
  the reindexed family.
- `quasiEtaleGodementFunctor L ρ h R`: the published `discreteZeroFunctor` for these
  points, an endofunctor of `QuasiEtaleGSheaf ρ (ModuleCat.{w} R)`. On a quasi-étale
  `G`-sheaf it is the discrete part of the induction to the twisted site of the product
  of the skyscraper sheaves at the `L`-valued points.
- `quasiEtaleGodementCoaugmentation L ρ h R`: its coaugmentation `𝟭 ⟶ G⁰`, the published
  `discreteCoaugmentation`.
- `mono_quasiEtaleGodementCoaugmentation L ρ h R hpoints F`: the coaugmentation is a
  monomorphism, by the published `mono_discreteCoaugmentation_of_jointlyFaithful`.

## Godement resolutions (Lemma 2.2 and Lemma 2.2 bis)

- `QuasiEtaleDivisibleSystem ρ R ℓ` and `QuasiEtaleComplexDivisibleSystem ρ R ℓ`:
  Harris's `ℓ`-divisible systems (2.1) of quasi-étale `G`-sheaves of `R`-modules and of
  cochain complexes of them, that is, Worker 61's `DivisibleSystem` in these categories.
  The abelian structure uses `twistedQuasiEtale_hasSheafify`.

Let `T : QuasiEtaleDivisibleSystem ρ R ℓ`.

- `quasiEtaleGodementResolutionSystem ρ R L h T hpoints`: Harris's Lemma 2.2, the
  `ℓ`-divisible system of the Godement resolutions of the levels of `T`
  (`discreteGodementResolutionSystem`).
  `quasiEtaleGodementResolutionSystemObjIso m` identifies level `m` with the Godement
  complex `discreteComplexFunctor` of `T m`, and
  `quasiEtaleGodementResolutionSystem_obj_exactAt m q` says that level `m` is exact in
  degree `q + 1`.
- `quasiEtaleGodementTruncatedResolutionSystem ρ R L h T hpoints D`: Harris's
  `G^•_m = τ_{≤ D+1}(F^•_m)` (Lemma 2.2 bis), the published
  `discreteGodementTruncatedResolutionSystem`. Further:
  - `quasiEtaleGodementTruncatedResolutionHom`: the inclusion `G^• ⟶ F^•`.
  - `quasiIso_quasiEtaleGodementTruncatedResolutionHom m`: the inclusion is a
    quasi-isomorphism at every level.
  - `isZero_quasiEtaleGodementTruncatedResolutionSystem_obj_X m hq`: level `m` is zero in
    degrees `q > D + 1`.
  - `quasiEtaleGodementTruncatedAugmentation m`: the augmentation `T m ⟶ G^•_m`.
  - `quasiIso_quasiEtaleGodementTruncatedAugmentation m`: the augmentation is a
    quasi-isomorphism, so `G^•_m` is a resolution of `T m` of length `D + 1`.

## Compact sections and (2.3)

In addition to the hypotheses above, these declarations take `hF` and `hT`.

- `isZero_quasiEtaleGSheafCompactCohomology_truncatedResolutionSystem_obj_X m i r`: every
  term of every `G^•_m` is acyclic for `Γ_{c,X{G}}`, that is,
  `H^{r+1}_c(X{G}, G^i_m) = 0`.
- `quasiEtaleGodementTruncatedCompactSectionsSystem ρ R L h T hpoints D hF hT`: Harris's
  `ℓ`-divisible system of finite-length complexes `Γ_{c,X{G}}(G^•_m)` of smooth
  representations of `G`. By
  `quasiEtaleGodementTruncatedCompactSectionsSystem_obj m` (proved by `rfl`), level `m`
  is `quasiEtaleGSheafCompactSections` applied termwise to `G^•_m`.
- `quasiEtaleGodementTruncatedCompactHomologyIso m n`: Harris's (2.3),
  `Hⁿ(Γ_{c,X{G}}(G^•_m)) ≅ H^n_c(X{G}, T m)`, the published
  `discreteGodementTruncatedCompactHomologyIso`.
- `isZero_quasiEtaleGodementTruncatedCompactSectionsSystem_homology m hn`: this cohomology
  vanishes in degrees `n > D`, by (2.3) and `hT`.

## Inverse limits: (2.6), (2.7) and Lemma 2.8

Here `G : Type u`, so that the representations of `TwistedInverseLimit`, which live in
the universe `max w' uG` of its coefficients `w'` and of `G : Type uG`, are again
`R`-modules in `w` (with `w' = w` and `uG = u`). The assumption `[Small.{w} G]` then
holds automatically. It is still a variable of this section, because without it Lean
fails to elaborate the declarations within its time limit. Any user can discharge it by
instance search.

The further data are those of `TwistedInverseLimit`: a filtered preorder `ι : Type u`, an
antitone family `H : ι → Subgroup G` of normal subgroups of finite index with `Fintype`
and `DecidableEq` instances on the quotients, and Worker 61's hypotheses

- `hK`: every projection of the compact section system stays an epimorphism on
  `H i`-invariants;
- `hk`: the orders of the kernels of the projections `G ⧸ H j ⟶ G ⧸ H i` are invertible in
  `R`.

The declarations are the published twisted-site ones, specialized as above.

- `quasiEtaleGodementQuotientInvariantsLimit`: Harris's `C^•_m`, an `ℓ`-divisible system
  of `ℤ`-graded complexes in `Rep R G` (`discreteGodementQuotientInvariantsLimit`).
- `quasiEtaleGodementQuotientInvariantsLimitToRepExtend`: Harris's comparison (2.6),
  `C^•_m ⟶ Γ_{c,X{G}}(G^•_m)`, with target the underlying representations extended by
  zero to `ℤ`.
- `quasiIso_quasiEtaleGodementQuotientInvariantsLimitToRepExtend hS hP hR m htriv`: (2.6)
  is a quasi-isomorphism at level `m`. The hypotheses are `hS`, that every `H i` is a
  pro-`p` subgroup (`IsProPSubgroup p (H i)`), that `p` is invertible in `R`, and that
  every `H i` acts trivially on every `H^q_c(X{G}, T m)` (`htriv`).
- `quasiEtaleGodementQuotientInvariantsLimitHomologyIso hS hP hR m htriv n`: Harris's
  (2.7), `Hⁿ(C^•_m) ≅ SmoothRep.toRep.obj (H^n_c(X{G}, T m))`.
- `quasiEtaleGodementQuotientInvariantsInverseLimit`: Harris's `lim_m C^•_m`.
- `quasiEtaleGodementQuotientInvariantsInverseLimitHomologyIso hS hS' hP hR htriv hfin n`:
  Harris's Lemma 2.8,
  `Hⁿ(lim_m C^•_m) ≅ limit (m ↦ SmoothRep.toRep.obj (H^n_c(X{G}, T m)))` in `Rep R G`.
  Besides the hypotheses of (2.7) for all `m`, it takes `hS'` and the finiteness of every
  `H^q_c(X{G}, T m)` (`hfin`).

## Original source

Harris, *Galois properties of cohomological automorphic forms on GL(n)*, J. Math. Kyoto
Univ. 39 (1999), registered as
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, §2, printed pp.303–306 =
PDF pp.5–8. Worker 26 read the rendered pages for the earlier twisted-site modules and
checked the p.303–304 passages again for this module.

- p.303, Fact 2: "There is an integer `D > 0` such that `H^q_c(U, T) = 0` for all
  `q > D` and any étale morphism `U → U(ẽ)`."
- p.304: "In Proposition 1.4.1 of [B4], Berkovich shows how to construct an acyclic
  resolution of a finite `ℓ`-torsion sheaf `T` on `U(ẽ)` by a complex of smooth
  `S(ẽ)`-modules. [...] is a smooth `G`-equivariant version of the Godement flasque
  resolution."
- p.304: "Here `T` is an 'étale sheaf in smooth `ℤ/ℓ^mℤ[S(ẽ)]`-modules' if, for any
  quasi-étale morphism `U → U(ẽ)` with `U` compact the action of the stabilizer
  `S(ẽ)_U ⊂ S(ẽ)` on `T(U)` is smooth; in other words, `T` is what Berkovich calls
  discrete."
- p.304: "Fact 3. The functor `T → F(T)` is exact. [...] By induction, we thus have
  Lemma 2.2. For each `m` the constant sheaf `ℤ/ℓ^mℤ` admits an `RΓ_c`-acyclic resolution
  `0 → ℤ/ℓ^mℤ → F_m^0 → F_m^1 → ⋯` such that, for each `q`, `{F_m^q}` is an
  `ℓ`-divisible system of `S(ẽ)`-modules over `U(ẽ)`."
- p.305: "We let `G_m^• = τ^{≤D+1}(F_m^•)`. [...] Lemma 2.2 bis. For each `m` the constant
  sheaf `ℤ/ℓ^mℤ` admits an `RΓ_c`-acyclic resolution of finite length [...] Thus Lemma
  2.2 provides an isomorphism (2.3) `H^q_c(U(ẽ)_F̄, ℤ/ℓ^mℤ) ⥲ Z_m^q/B_m^q =
  H^q(G_m^•(U(ẽ)_F̄))`."
- p.306: "Taking the direct limit as `H` shrinks to the identity, we obtain an
  `ℓ`-divisible system of complexes `C^•_m` of projective `ℤ/ℓ^mℤ[S(e)]`-modules and a
  natural `S(ẽ)`-equivariant quasi-isomorphism (2.6) `C^•_m → G^•_m(U(e, N)_F̄)`. Now
  (2.3) and (2.6) imply that (2.7) [...] Lemma 2.8. For every `q`, there is a canonical
  isomorphism `H^q(lim_m C^•_m(U(ẽ)_F̄)) ⥲ lim_m H^q_c(U(ẽ)_F̄, ℤ/ℓ^mℤ)`."

Berkovich's quasi-étale `G`-sheaves and `H^q_c(X{G}, F)` are cited in
`AnalyticQuasiEtaleCompactCohomology`.

## Provenance and correspondence

This module specializes derived infrastructure. The correspondence with Harris is:

- Harris's étale sheaves in smooth modules on `U(ẽ)` with the action of `S(ẽ)` are
  replaced by quasi-étale `G`-sheaves on an arbitrary `K`-analytic space `X` with an
  arbitrary group `G`. Harris's smoothness condition, on the sections over compact
  quasi-étale objects, is the discreteness condition built into `QuasiEtaleGSheaf`. As
  explained in `AnalyticQuasiEtaleCompactCohomology`, étale `G`-sheaves embed fully
  faithfully into quasi-étale ones (Berkovich, Theorem 1.4.2 and Corollary 1.4.3), and
  the derived functors are taken among quasi-étale `G`-sheaves. The comparison with the
  étale cohomology is not formalized.
- Harris's constant system `ℤ/ℓ^mℤ` is an arbitrary `ℓ`-divisible system `T`.
- Berkovich's embedding `T ↪ F(T)` is the discrete Godement functor built from the
  `L`-valued points. Its exactness, its acyclicity, the joint faithfulness of the points,
  the point axioms and Harris's Fact 2 are hypotheses, as listed above.
- The subgroup family, the trivial action of the `H i`, the finiteness of `H^q_c`, and
  Worker 3's two statements enter as in `TwistedInverseLimit`.
- The existence of the right Kan extensions is ours. It is needed to define the Godement
  functor on this site.

## Not formalized here

The hypotheses listed above, the spaces `U(ẽ)` and `U(e, N)`, the groups `S(ẽ)` and their
pro-`p` subgroups, the constant system, projectivity of the terms of `C^•_m`, and the
comparison with étale cohomology are not formalized here.
