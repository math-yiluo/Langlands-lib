# The constant `ℓ`-divisible system of quasi-étale `G`-sheaves

Author: Worker 26. Builds on the following modules:

- `Langlands.Sheaf.Equivariant.LocalActionConstant` (Worker 26, submitted together with
  this module). It provides the constant sheaf functor with values in discrete sheaves,
  `discreteConstantSheaf L J R`, and its exactness and additivity instances.
- `Langlands.Cohomology.DivisibleSystem.ConstantCoefficients` (Worker 61). It provides the
  `ℓ`-divisible system `scalarSystem R ℓ hℓ` of the `R`-modules `R / ℓ ^ m R`, for `ℓ` a
  non-zero-divisor of `R` (`hℓ : IsSMulRegular R (ℓ : R)`), and the identification
  `scalarSystemObjIso hℓ m` of its level `m` with `R ⧸ Ideal.span {ℓ ^ m}`. Through it,
  the module uses Worker 61's `DivisibleSystem` and its `map` along exact additive
  functors.
- `Langlands.Cohomology.DivisibleSystem.AnalyticQuasiEtale` (Worker 26). It provides
  Harris's Lemma 2.2, Lemma 2.2 bis and (2.3) for an arbitrary `ℓ`-divisible system `T` of
  quasi-étale `G`-sheaves (`QuasiEtaleDivisibleSystem ρ R ℓ`), with the Godement
  functor built from the `L`-valued points of `X`. Through it, the module uses
  `AnalyticQuasiEtaleCompactCohomology` (Worker 26): sheafification on the twisted
  quasi-étale site (`twistedQuasiEtale_hasSheafify`) and Berkovich's compactly supported
  cohomology `quasiEtaleGSheafCompactCohomology L ρ h R n` (`H^n_c(X{G}, -)`). It also
  uses Worker 21's quasi-étale site, points and point axioms.

The generic declarations are in the namespace `Langlands.Cohomology.DivisibleSystem`, the
quasi-étale ones in `Langlands.Cohomology.DivisibleSystem.Analytic`.

## Purpose

The published module `AnalyticQuasiEtale` carries out Harris's Lemma 2.2, Lemma 2.2 bis
and (2.3) for an arbitrary `ℓ`-divisible system of quasi-étale `G`-sheaves, while Harris
states them for the constant sheaves `ℤ/ℓ^mℤ`. This module constructs the constant system
and specializes those results to it. For the constant system, (2.3) computes
`H^n_c(X{G}, R / ℓ ^ m R)`.

## The constant system of discrete sheaves

Let `L : LocalActionSystem T G` be a local action system on a category `T` with a
Grothendieck topology `J`. Assume `[HasSheafify J (ModuleCat.{w} R)]` and
`[L.HasFiniteEquivariantRefinements J]`. Here `R : Type w` is a commutative ring and
`hℓ : IsSMulRegular R (ℓ : R)`.

- `discreteConstantSystem L J R hℓ`: the `ℓ`-divisible system of discrete sheaves
  `(scalarSystem R ℓ hℓ).map (discreteConstantSheaf L J R)`, the constant sheaves
  `R / ℓ ^ m R`. `DivisibleSystem.map` applies because `discreteConstantSheaf` is additive
  and preserves finite limits and finite colimits (`LocalActionConstant`).
- `discreteConstantSystemObjIso L J R hℓ m`: its level `m` is the constant sheaf of the
  `R`-module `R ⧸ Ideal.span {ℓ ^ m}`. This is the image of `scalarSystemObjIso hℓ m` under
  the constant sheaf functor.
- `discreteConstantSystem_projection`, `discreteConstantSystem_inclusion`: the maps `j`
  and `i` of the system are the constant sheaf maps of those of `scalarSystem`. Under
  `scalarSystemObjIso` these are the reduction `R / ℓ ^ m R → R / ℓ ^ m' R` and
  multiplication by `ℓ ^ (m - m')` (Worker 61). Both statements hold by `rfl`.

## The constant system of quasi-étale `G`-sheaves

Data and universes are those of `AnalyticQuasiEtale`:

- `K : Type u` is a complete ultrametric normed field, and `X` an object of Worker 21's
  `LocalizedCategory.{u, v, v} (K := K)`.
- `G : Type z` is a group with a topology and `ρ : G →* Aut X`.
- Write `w = max u (v + 1) uL`. The ring `R : Type w` is commutative, and sheaves take
  values in `ModuleCat.{w} R`.
- `[Small.{w} G]`, and the published, unproved finite equivariant refinement condition
  `[(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedQuasiEtaleTopology ρ)]`.

The declarations below that do not take the field `L` determine `uL` only through `w`,
so their uses carry explicit universes `.{u, v, uL}`.

- `isSMulRegular_uLiftInt_natCast hℓ`: a nonzero natural number `ℓ` is a non-zero-divisor
  of `ULift ℤ`.
- `quasiEtaleConstantSheaf ρ R`: the constant quasi-étale `G`-sheaf functor
  `ModuleCat.{w} R ⥤ QuasiEtaleGSheaf ρ (ModuleCat.{w} R)`, that is,
  `discreteConstantSheaf` for the lift system `compactLiftSystem ρ` on the twisted
  quasi-étale site. By `quasiEtaleConstantSheaf_comp_inclusion` (`rfl`), followed by the
  inclusion into all sheaves it is Mathlib's `constantSheaf` of the twisted quasi-étale
  topology: the sheafification of the constant presheaf.
- `quasiEtaleConstantSystem ρ R hℓ : QuasiEtaleDivisibleSystem ρ R ℓ`: the constant
  `ℓ`-divisible system `{R / ℓ ^ m R}` of quasi-étale `G`-sheaves, the case
  `discreteConstantSystem` of this lift system.
- `quasiEtaleConstantSystemObjIso ρ R hℓ m`: its level `m` is
  `(quasiEtaleConstantSheaf ρ R).obj (ModuleCat.of R (R ⧸ Ideal.span {ℓ ^ m}))`.
- `quasiEtaleIntConstantSystem ρ hℓ` (for `ℓ ≠ 0`): the case `R = ULift.{w} ℤ`, Harris's
  system of constant sheaves `ℤ/ℓ^mℤ`. The integers are lifted to the universe `w` of the
  coefficients. The levels are `ULift ℤ ⧸ (ℓ ^ m)`, which is `ℤ/ℓ^mℤ` up to an
  isomorphism that is not formalized.

## Lemma 2.2 and Lemma 2.2 bis for the constant system

These declarations take the hypotheses of `AnalyticQuasiEtale`, which stay hypotheses:

- the field `L : Type uL` with `[NormedAlgebra K L]` and the point axioms
  `h : ∀ x, QuasiEtaleSite.PointAxioms L x` at the `L`-valued points;
- exactness of the quasi-étale Godement functor,
  `[PreservesFiniteLimits (quasiEtaleGodementFunctor L ρ h R)]` and
  `[PreservesFiniteColimits (quasiEtaleGodementFunctor L ρ h R)]` (Harris's Fact 3);
- `hpoints`: joint faithfulness of the fibre functors at the `L`-valued points.

The declarations are:

- `quasiEtaleConstantGodementResolutionSystem ρ R hℓ L h hpoints` (an abbreviation):
  Harris's Lemma 2.2, the `ℓ`-divisible system of the Godement resolutions of the constant
  sheaves `R / ℓ ^ m R`, that is, `quasiEtaleGodementResolutionSystem` applied to
  `quasiEtaleConstantSystem`. Its properties are those proved in `AnalyticQuasiEtale`, for
  example exactness in positive degrees
  (`quasiEtaleGodementResolutionSystem_obj_exactAt`).
- `quasiEtaleConstantGodementTruncatedResolutionSystem ρ R hℓ L h hpoints D` (an
  abbreviation): Harris's Lemma 2.2 bis, the truncation `G^•_m = τ_{≤ D+1}(F^•_m)`.
- `quasiEtaleConstantGodementTruncatedAugmentation ρ R hℓ L h hpoints D m`: the augmentation
  from the constant sheaf `R / ℓ ^ m R` (as a complex in degree `0`) to `G^•_m`. It is the
  published augmentation `T m ⟶ G^•_m` precomposed with the inverse of
  `quasiEtaleConstantSystemObjIso`.
- `quasiIso_quasiEtaleConstantGodementTruncatedAugmentation m`: this augmentation is a
  quasi-isomorphism, so `G^•_m` is a resolution of length `D + 1` of the constant sheaf
  `R / ℓ ^ m R`. Proof: the published augmentation is a quasi-isomorphism
  (`quasiIso_quasiEtaleGodementTruncatedAugmentation`), and so is the image of an
  isomorphism.

## Compact sections and (2.3) for the constant system

In addition, these declarations take `[IsTopologicalGroup G]` and two hypotheses:

- `hF`: Godement sheaves are acyclic for `Γ_{c,X{G}}`, as in `AnalyticQuasiEtale`;
- `hC`: `H^n_c(X{G}, R / ℓ ^ m R) = 0` for all `m` and all `n > D`, stated for the constant
  sheaves `(quasiEtaleConstantSheaf ρ R).obj (ModuleCat.of R (R ⧸ Ideal.span {ℓ ^ m}))`
  (Harris's Fact 2 for constant coefficients).

The declarations are:

- `isZero_quasiEtaleGSheafCompactCohomology_constantSystem_obj ρ R hℓ L h D hC m n hn`: `hC`
  transfers to the levels of `quasiEtaleConstantSystem` along
  `quasiEtaleConstantSystemObjIso`. This gives the hypothesis `hT` of
  `AnalyticQuasiEtale` for the constant system.
- `quasiEtaleConstantCompactSectionsSystem ρ R hℓ L h hpoints D hF hC` (an abbreviation):
  Harris's `ℓ`-divisible system of finite-length complexes `Γ_{c,X{G}}(G^•_m)` of smooth
  representations of `G`, for the constant sheaves.
- `quasiEtaleConstantCompactHomologyIso m n`: Harris's (2.3) for the constant sheaves,
  `Hⁿ(Γ_{c,X{G}}(G^•_m)) ≅ H^n_c(X{G}, R / ℓ ^ m R)`. It is the published
  `quasiEtaleGodementTruncatedCompactHomologyIso` followed by `H^n_c` applied to
  `quasiEtaleConstantSystemObjIso`.

## Original source

Harris, *Galois properties of cohomological automorphic forms on GL(n)*, J. Math. Kyoto
Univ. 39 (1999), registered as
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, §2, printed pp.303–305 =
PDF pp.5–7. Worker 26 checked p.304 with `pdftotext` and a rendering of the page for this
module; the p.303 and p.305 passages are those cited in `AnalyticQuasiEtale`.

- p.303, Fact 2: "There is an integer `D > 0` such that `H^q_c(U, T) = 0` for all `q > D`
  and any étale morphism `U → U(ẽ)`."
- p.304, (2.1) (rendered page checked): "By an `ℓ`-divisible system of `S(ẽ)`-modules over
  `U(ẽ)` we mean a collection `{T_m}` of étale sheaves in smooth `ℤ/ℓ^mℤ[S(ẽ)]`-modules
  over `U(ẽ)`, `m ≥ 1`, with morphisms `i = i_{m',m} : T_{m'} → T_m` and
  `j = j_{m,m-m'} : T_m → T_{m-m'}` for all `m > m' ≥ 1` such that `T_m` is free over
  `ℤ/ℓ^mℤ`, `i` identifies `T_{m'}` with the `p^{m'}`-torsion in `T_m`, and (2.1)
  `0 → T_{m'} → T_m → T_{m-m'} → 0` is exact." (The `p^{m'}` is as printed; `ℓ^{m'}` is
  meant.)
- p.304: "Lemma 2.2. For each `m` the constant sheaf `ℤ/ℓ^mℤ` admits an `RΓ_c`-acyclic
  resolution `0 → ℤ/ℓ^mℤ → F_m^0 → F_m^1 → ⋯` such that, for each `q`, `{F_m^q}` is an
  `ℓ`-divisible system of `S(ẽ)`-modules over `U(ẽ)`."
- p.305: "Lemma 2.2 bis. For each `m` the constant sheaf `ℤ/ℓ^mℤ` admits an
  `RΓ_c`-acyclic resolution of finite length [...] Thus Lemma 2.2 provides an isomorphism
  (2.3) `H^q_c(U(ẽ)_F̄, ℤ/ℓ^mℤ) ⥲ Z_m^q/B_m^q = H^q(G_m^•(U(ẽ)_F̄))`."

## Provenance and correspondence

- Harris's constant sheaves `ℤ/ℓ^mℤ` on `U(ẽ)` with the action of `S(ẽ)` correspond to the
  constant quasi-étale `G`-sheaves of `R / ℓ ^ m R` on an arbitrary `K`-analytic space `X`
  with an arbitrary group `G`. For `R = ℤ` (lifted to `ULift ℤ`) the levels are `ℤ/ℓ^mℤ`
  up to an isomorphism that is not formalized. The constant sheaf is the sheafification on
  the twisted quasi-étale site of the constant presheaf. Its comparison with the constant
  sheaf on the quasi-étale site of `X` and with the étale constant sheaf is not
  formalized.
- That these sheaves form an `ℓ`-divisible system in the sense of (2.1) is implicit in
  Harris. Here it follows from Worker 61's `scalarSystem` and the exactness of the constant
  sheaf functor into discrete sheaves (`LocalActionConstant`). Worker 61's
  `DivisibleSystem` encodes the freeness of `T_m` over `ℤ/ℓ^mℤ` and the torsion conditions
  by exactness conditions.
- The specializations of Lemma 2.2, Lemma 2.2 bis and (2.3) are the published
  `AnalyticQuasiEtale` declarations applied to the constant system. The only additions are
  the transfer of `hC` along `quasiEtaleConstantSystemObjIso` and the composition of the
  augmentation and of (2.3) with that isomorphism.

## Not formalized here

The hypotheses listed above (exactness and acyclicity of the Godement functor, joint
faithfulness of the points, the point axioms, finite equivariant refinements, and Harris's
Fact 2 for constant coefficients), the spaces `U(ẽ)` and the groups `S(ẽ)`, and the
comparison of the constant quasi-étale `G`-sheaves with étale constant sheaves are not
formalized here. Lemma 2.8 and the inverse limit constructions of `AnalyticQuasiEtale`
apply to `quasiEtaleConstantSystem` when `G : Type u`; this module does not restate them.
