# Inverse limit topology on limits of discrete representations

Author: Worker 61. Built on the published modules
`Langlands.Representation.Smooth.Definitions` (`IsSmooth`,
`IsSmoothVector`, `fixedVectors`) and
`Langlands.Cohomology.DivisibleSystem.EtaleAdicCohomology` of Worker 61
(`equivariantAdicCohomology`), which uses Worker 13's
`EtaleCohomologyAction.EquivariantSheaf` and
`EtaleCohomologyAction.pullbackCohomologyFunctor`. From Mathlib it uses
`ContRepresentation` (with `ContRepresentation.ofMonoidHom`),
`ContIntertwiningMap`, `TopRep` (with `TopRep.of`, `TopRep.ofHom`,
`TopRep.hom_ext` and `TopRep.toActionTopModFunc`), `ContAction` and
`Action.isContinuous_def`, `TopModuleCat`, `Rep.ActionToRep`,
`IsLocallyConstant`, `Concrete.isLimit_ext`, `isLimitOfPreserves`, `IsAdic`
and `isAdic_iff`, `lim`, `limit.cone` and `limMap_π`.

The declarations are in the namespaces
`Langlands.Cohomology.ContinuousLimit` (general cones) and
`Langlands.Cohomology.EtaleAdicCohomology` (étale cohomology). Composition
`f ≫ g` is `f` followed by `g`.

## Conventions

`R : Type u` is a commutative ring and `G : Type v` a group. A
representation is an object of `Action (ModuleCat.{u} R) G`: an `R`-module
`V` with a monoid map `ρ : G →* End V`. `J` is a category,
`M : J ⥤ Action (ModuleCat R) G` a diagram of representations with levels
`M_j`, and `c : Cone M` a cone with point `c.pt` and projections
`c.π.app j : c.pt ⟶ M_j`. When `G` has a topology, a representation is smooth
(`IsSmooth`, published) if every vector is fixed by an open subgroup; for a
level `M_j` this is stated for `(Rep.ActionToRep R G).obj M_j`, the same
module and action seen as an object of `Rep R G`. "Discrete" means the
discrete topology. Smoothness of the levels and continuity of the group
multiplication are explicit hypotheses wherever they are used.

## The topology on a cone point

- `ConeSpace c`: the underlying type of `c.pt`, with its `R`-module
  structure. `proj c j : ConeSpace c →ₗ[R] M_j` is the projection and
  `act c g : ConeSpace c →ₗ[R] ConeSpace c` the action of `g`;
  `proj_act`: `proj c j (act c g x) = g · proj c j x`.
- The topology on `ConeSpace c` (instance) is the infimum over `j` of the
  topologies induced by `proj c j` from the discrete topology on `M_j`: the
  coarsest topology for which every projection to a discrete level is
  continuous. For a limit cone this is the inverse limit topology of the
  discrete levels.
- `continuous_iff`: a map `f : X → ConeSpace c` from a topological space is
  continuous if and only if every `proj c j ∘ f` is locally constant.
  `isLocallyConstant_proj`: every projection is locally constant.
- `ConeSpace c` is a topological additive group (instance), and each
  `act c g` is continuous (`continuous_act`).
- `t2Space_of_isLimit`: if `c` is a limit cone, and the forgetful functors
  `Action (ModuleCat R) G ⥤ ModuleCat R` and `ModuleCat R ⥤ Type` preserve
  the relevant limits (instance arguments, satisfied by Mathlib's instances
  for the diagrams used below), `ConeSpace c` is Hausdorff. Proof: two
  different points differ in some level (`Concrete.isLimit_ext`), and the
  fibres of that projection are disjoint open sets.
- `continuous_hom`: for a cone `c'` over `M'`, a morphism of diagrams
  `α : M ⟶ M'` and a morphism `f : c.pt ⟶ c'.pt` with
  `f ≫ c'.π.app j = c.π.app j ≫ α.app j` for every `j`, the map `f` is
  continuous.

## Smooth levels and joint continuity

`G` carries a topology for which multiplication is continuous.

- `eventually_eq_of_isSmooth`: for a smooth representation `ρ` on `V`, every
  `g₀ ∈ G` and every `v ∈ V`, `ρ g v = ρ g₀ v` for all `g` in a
  neighbourhood of `g₀` (namely `g₀ K`, for an open subgroup `K` fixing `v`).
- `continuous_of_isSmooth`: a smooth representation on a discrete module has
  a jointly continuous action map `G × V → V`, `(g, v) ↦ ρ g v`. The
  published `isSmoothVector_iff_continuous_orbitMap`
  (`Langlands.Representation.Smooth.DiscreteOrbitProof`, not imported)
  concerns the orbit maps `g ↦ ρ g v` of single vectors; here both
  variables move.
- `continuous_action`: if every level `M_j` is smooth, the action
  `G × ConeSpace c → ConeSpace c`, `(g, x) ↦ act c g x`, is jointly
  continuous. Proof: by `continuous_iff`, it suffices that each
  `(g, x) ↦ proj c j (act c g x) = g · proj c j x` be locally constant, and
  near `(g₀, x₀)` it is constant by `eventually_eq_of_isSmooth` and the local
  constancy of `proj c j`.

The cone point itself is not claimed to be smooth: a vector of the limit need
not be fixed by an open subgroup (Milne's remark that the action "need not
factor through a finite quotient").

## Continuity of scalar multiplication

`R` carries a topology.

- `continuousSMul`: if, for every level `M_j` and every `y ∈ M_j`, the map
  `r ↦ r • y` is locally constant, scalar multiplication on `ConeSpace c` is
  continuous (`ContinuousSMul R (ConeSpace c)`).
- Instance: this holds when `R` is discrete.
- `isLocallyConstant_smul_of_ideal`: for a topological ring `R` (additive
  group structure suffices), an open ideal `I` and an element `y` of an
  `R`-module with `r • y = 0` for all `r ∈ I`, the map `r ↦ r • y` is locally
  constant. `continuousSMul_of_ideal`: if every element of every level is
  killed by some open ideal, scalar multiplication on `ConeSpace c` is
  continuous.
- `continuousSMul_of_isAdic`: if `R` carries the `I`-adic topology
  (`IsAdic I`) and every level `M_j` is killed by some power `I ^ n`,
  scalar multiplication on `ConeSpace c` is continuous. This is the case
  of levels killed by powers of `ℓ` over a ring with the `(ℓ)`-adic
  topology; that `ℤ_ℓ` with its usual topology satisfies `IsAdic` is not
  proved here.

These results concern the topology of `R` and continuity of
`R × ConeSpace c → ConeSpace c`; they do not compare the topology on
`ConeSpace c` with an `I`-adic topology on `ConeSpace c`.

## Packaging with Mathlib's continuous representations

- `act_one`, `act_mul`: `act c` is a monoid action.
- `contRepresentation c : ContRepresentation R G (ConeSpace c)`: `g` acts by
  the continuous linear map `act c g` (`contRepresentation_apply`). Mathlib's
  `ContRepresentation` asks only that each `g` act continuously, not joint
  continuity.
- `contIntertwiningMap c c' α f hf`: the continuous intertwining map
  `ConeSpace c → ConeSpace c'` given by `f` under the hypotheses of
  `continuous_hom` (`contIntertwiningMap_apply`).
- `topRep c : TopRep R G`, for a topological ring `R` with
  `ContinuousSMul R (ConeSpace c)` (for example `R` discrete, or one of the
  lemmas above): `TopRep.of (contRepresentation c)`.
- `contAction c hM : ContAction (TopModuleCat R) G`, under the same
  hypotheses on `R` and smooth levels `hM`: `topRep c` as an object of
  `Action (TopModuleCat R) G` (Mathlib's `TopRep.toActionTopModFunc`),
  together with the joint continuity of the action (`continuous_action`), as
  Mathlib's `ContAction` requires.
- `limitTopRepFunctor R G J : (J ⥤ Action (ModuleCat R) G) ⥤ TopRep R G`,
  for a discrete ring `R` and `J` such that `Action (ModuleCat R) G` has
  limits of shape `J`: a diagram `M` goes to `topRep (limit.cone M)`, a
  morphism `α` to the continuous intertwining map given by `lim.map α`.
  `limitTopRepFunctor_obj_V`, `limitTopRepFunctor_obj_ρ`,
  `limitTopRepFunctor_map_apply`: its underlying module is that of
  `limit M`, with the action of `limit M` and the maps `limMap α`, by
  definition.

## Étale cohomology

As in the published `EtaleAdicCohomology`, `X : Scheme.{u}` is a scheme,
`R : Type u` a commutative ring, `G : Type w` a group, `ρ : G →* (Aut X)ᵐᵒᵖ`
an action of `G` on `X`, `q` a natural number and
`F : ℕᵒᵖ ⥤ EtaleCohomologyAction.EquivariantSheaf R ρ` an inverse system of
`ρ`-equivariant étale sheaves of `R`-modules. The published
`equivariantAdicCohomology R ρ q` sends `F` to the limit in
`Action (ModuleCat R) G` of the representations
`H^q(X, F_m) = pullbackCohomologyFunctor R ρ q (F_m)`, that is,
`lim_m H^q(X, F_m)` with its action of `G`.

- `AdicCohomologySpace R ρ q F`: `ConeSpace` of the limit cone of
  `F ⋙ pullbackCohomologyFunctor R ρ q`, that is, `lim_m H^q(X, F_m)` with
  the inverse limit topology of the discrete modules `H^q(X, F_m)`;
  `adicCohomologySpace_eq`: its type is that of the underlying module of
  `equivariantAdicCohomology R ρ q` of `F`, by definition. It is Hausdorff
  (instance, `t2Space_of_isLimit`).
- `continuous_map`: for a morphism `φ : F ⟶ E` of inverse systems, the map
  `lim_m H^q(X, F_m) → lim_m H^q(X, E_m)` given by
  `(equivariantAdicCohomology R ρ q).map φ` is continuous.
- `continuous_action`: if every `H^q(X, F_m)` is a smooth representation of
  a group `G` with a topology for which multiplication is continuous, the
  action `G × lim_m H^q(X, F_m) → lim_m H^q(X, F_m)` is jointly continuous.
- `adicContRepresentation R ρ q F`: `contRepresentation` of this cone.
  `adicContAction R ρ q F hF`: `contAction` of this cone, for smooth levels
  `hF` and a topological ring `R` with continuous scalar multiplication.
- `equivariantAdicCohomologyTopRep R ρ q`, for a discrete ring `R`:
  `equivariantAdicCohomology R ρ q` followed by the topology, as a functor
  to `TopRep R G` (the cohomology functor on levels followed by
  `limitTopRepFunctor R G ℕᵒᵖ`). `equivariantAdicCohomologyTopRep_obj_V`:
  its underlying module is that of `equivariantAdicCohomology R ρ q` of `F`,
  by definition.

## Provenance and interpretation

Milne, *Étale Cohomology* (1980), Chapter V, §1, printed p.164 (one-based
PDF page 178; Worker 61 read the text layer of the scanned page): "In
particular, if `X` is connected with geometric point `x`, then the action of
`π₁(X, x)` on `F_x = lim (F_n)_x` need not factor through a finite quotient.
However, the action is continuous when `F_x` is given the `l`-adic
topology". Here `F = (F_n)` is an `l`-adic sheaf (p.163) and each `F_n` is
killed by `l^n` (p.164).

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999) (Worker 61 read the rendered scanned
pages):

- §3, printed p.308 (one-based PDF page 10): "More generally, we can let `𝓛`
  be any continuous `K_ℓ`-module; then `𝒜_ℓ(GJ, 𝓛, K)`, defined by analogy
  with (3.7), still makes sense." and "Let `𝓛` be a free `𝒪/ℓ^m𝒪`-module of
  finite order with a continuous action of `K_ℓ`, which we suppose to factor
  through the quotient group `K_{ℓ,n} = K_ℓ/K_ℓ(n)`."
- §4, printed p.312 (one-based PDF page 14), (4.10.4): the abutment
  `H^{i+j}(S̄_{K(N)}, 𝓛̃)` of the inverse system `{𝓛̃_m}`, read in the
  published `EtaleAdicCohomology` as `lim_m H^{i+j}(S̄_{K(N)}, 𝓛̃_m)`.

Interpretation. A level killed by `ℓ^m` whose action factors through the
quotient by an open normal subgroup, as on p.308 (where `K_ℓ(n)` is a normal
congruence subgroup), is a smooth representation, and with the discrete
topology its action is jointly continuous (`continuous_of_isSmooth`). We model
the topological module of Milne's remark by the limit of the levels with the
inverse limit topology of the discrete levels, and `continuous_action` is the
continuity of the action on it. For a finitely generated `ℤ_ℓ`-module `N`
the `ℓ`-adic topology of `N` agrees with the inverse limit topology of the
discrete quotients `N/ℓ^m N`; this comparison is standard but is not
formalized here, so the module proves continuity for the inverse limit
topology only. All statements and proofs are ours (derived): the topology is
the standard limit topology, and the proofs use only the definitions.

## Scope

The module defines the inverse limit topology on cone points and proves its
basic properties. It does not compare this topology with the `ℓ`-adic (or
`I`-adic) topology on the limit, prove that the limit topology is compact or
complete, prove smoothness of any level (in particular of `H^q(X, F_m)`;
smoothness of Galois or Hecke actions on cohomology stays an explicit
hypothesis), or treat `ℚ_ℓ`-coefficients or continuous cohomology. It builds
no bridge to the published `Langlands.Cohomology.Continuous` modules (for
example `DiscreteModule`). The étale part uses the published
`equivariantAdicCohomology` with its qualifications: `X`, `G` and `ρ` are
inputs, not identified with Harris's Shimura varieties and the groups acting
on them.

Source registrations: Milne 1980, `milne-1980-etale-cohomology`, SHA-256
`0a2f02682f82db8385e4dc6c77c7113900b11d6c313f34f8b354a3a9a391d232`; Harris
1999, `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
