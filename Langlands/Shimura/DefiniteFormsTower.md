# Harris's tower of congruence subgroups `K_ℓ(n)`

Author: Worker 61. Built on the published
`Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.RamificationQuotients.Filtration`
(Naganori Yamaguchi's `AntitoneNormalSubgroupFiltration`, adapted from the
NYLL ClassFieldTheory repository, with its normality instance
`lower_normal_instance`), `Langlands.Representation.Smooth.Definitions`
(`fixedVectors`, `IsSmoothVector`, `IsSmooth`),
`Langlands.Shimura.DefiniteFormsDoubleCoset` (Worker 61: `localLevel`,
`localLevelMap`, `ellModuleForms`, `primeToLevel`, `congruenceLevel`,
`congruenceLevel_le`, `congruenceLevel_subgroupOf`,
`primeToLevel_le_congruenceLevel`) and `Langlands.Shimura.DefiniteFormsTensor`
(Worker 61: `congruenceTensorSpace`, `congruenceTensorAction`,
`congruenceTensorEquiv`), and on Worker 57's similitude groups
(`AlgebraInvolution.FiniteAdelicPoints`, the continuous `ℓ`-component map
`σ.finiteLocalMap ℓ`, the topology on `σ.Points`). From Mathlib it uses
open subgroups (`OpenSubgroup`, `OpenNormalSubgroup`,
`Subgroup.isClosed_of_isOpen`), compactness
(`IsCompact.elim_directed_family_closed`), quotient groups
(`QuotientGroup.lift`, `QuotientGroup.mk'`) and representations
(`Representation.invariants`, `Representation.comp`).

The module formalizes the tower of Harris 1999, p.308: "a lattice of normal
congruence subgroups `K_ℓ(n) ⊂ K_ℓ`" decreasing to `{1}`, the levels
`K(n) = K_ℓ(n) × K^ℓ`, and the hypothesis that the continuous action of
`K_ℓ` on a finite module `𝓛` factors through `K_{ℓ,n} = K_ℓ/K_ℓ(n)`. For
compact groups it shows that this hypothesis holds for some `n` as soon as
the action is smooth, and it restates (3.8) for such an action.

## Conventions

As in the published `DefiniteFormsDoubleCoset.md`:
`σ : AlgebraInvolution ℚ A` is an involution of a finite-dimensional
`ℚ`-algebra `A`, and `σ.FiniteAdelicPoints` is the group of finite adelic
points of its similitude group (Harris's `GJ(𝔸^f)`). `ℓ` is a finite place
of `ℚ` and `K` a subgroup of `σ.FiniteAdelicPoints`. `localLevel σ ℓ K`
(Harris's `K_ℓ`) is the image of `K` under the `ℓ`-component map, a
subgroup of `σ.Points ℚ_ℓ` with the subspace topology, and
`localLevelMap σ ℓ K : K →* localLevel σ ℓ K` is `k ↦ k_ℓ`.
`primeToLevel σ ℓ K` (Harris's `K^ℓ`) is the set of `k ∈ K` with `k_ℓ = 1`.
For a subgroup `H` of `K_ℓ`, `congruenceLevel σ ℓ K H` (Harris's `K(n)`
for `H = K_ℓ(n)`) is the set of `k ∈ K` with `k_ℓ ∈ H`. For a
representation `ρ'` of `K_ℓ`, `ellModuleForms σ ℓ K ρ'` is Harris's
`𝒜_ℓ(GJ, 𝓛, K)` of (3.7).

For a representation `ρ` of a topological group `G` on an `R`-module `V`
(`R` a commutative ring), the published `fixedVectors ρ H` is the
submodule of vectors fixed by a subgroup `H`; `IsSmoothVector ρ v` says
that `v` is fixed by some open subgroup, and `IsSmooth ρ` that every vector
is smooth. `ρ.ker` is the kernel of `ρ : G →* (V →ₗ[R] V)`.

## The tower

Namespace `Langlands`, for a group `G` with a topology.

- `CongruenceTower G`: a structure extending the published
  `AntitoneNormalSubgroupFiltration G` (fields `lower : ℕ → Subgroup G`,
  `lower_normal`: every `lower n` is normal, `antitone`:
  `m ≤ n → lower n ≤ lower m`) by `isOpen_lower`: every `lower n` is open,
  and `iInf_lower`: `⨅ n, lower n = ⊥`. For `T : CongruenceTower G`,
  `T.lower n` is Harris's `K_ℓ(n)`.
- `CongruenceTower.openLevel T n`: `T.lower n` as a Mathlib
  `OpenNormalSubgroup` (`openLevel_toSubgroup`).
- `antitone_lower`: `T.lower` is antitone. `eq_one_of_forall_mem`: an
  element lying in every `T.lower n` is `1`.

In a compact group (`[SeparatelyContinuousMul G] [CompactSpace G]`):

- `exists_lower_subset`: every open set `U` containing `1` contains some
  `T.lower n`. Proof: open subgroups are closed, so the sets
  `T.lower n ∩ Uᶜ` form a directed family of closed sets; its intersection
  is empty because `⋂_n T.lower n = {1}` and `1 ∈ U`, so by compactness one
  member is empty.
- `exists_lower_le`: every open subgroup contains some `T.lower n`.

For a representation `ρ` of `G` on an `R`-module `V`:

- `fixedVectors_mono`: `n ↦ fixedVectors ρ (T.lower n)` is monotone (no
  compactness needed).
- `isSmoothVector_iff` (compact `G`): `v` is smooth iff it is fixed by some
  `T.lower n`.
- `isSmooth_iff_iSup` (compact `G`): `ρ` is smooth iff
  `⨆ n, fixedVectors ρ (T.lower n) = ⊤`.
- `exists_lower_le_ker` (compact `G`, `[Module.Finite R V]`): if `ρ` is
  smooth then `T.lower n ≤ ρ.ker` for some `n`. Proof: each of finitely
  many generators is fixed by some `T.lower (N v)`; the largest index works
  since the fixed vectors increase with `n`.
- `factorRep T hn`, for `hn : T.lower n ≤ ρ.ker`: the representation of
  `G ⧸ T.lower n` induced by `ρ` (Mathlib's `QuotientGroup.lift`), with
  `factorRep_mk` (`[g]` acts as `g`) and `factorRep_comp_mk'` (composing
  with `G → G ⧸ T.lower n` gives back `ρ`).
- `isSmooth_comp_mk' T n ρ'`: a representation `ρ'` of `G ⧸ T.lower n`
  inflated to `G` is smooth, since `T.lower n` is open (no compactness
  needed).
- `isSmooth_iff_exists_lower_le_ker` (compact `G`, `[Module.Finite R V]`):
  `ρ` is smooth iff `T.lower n ≤ ρ.ker` for some `n`, that is, iff `ρ`
  factors through some `G ⧸ T.lower n`.

## Harris's setting

Namespace `Langlands.Shimura.DefiniteForms`, with `σ`, `ℓ`, `K` as in the
conventions.

- `continuous_localLevelMap σ ℓ K`: `k ↦ k_ℓ` is continuous for the
  subspace topologies.
- `isCompact_localLevel σ ℓ K hK` and `compactSpace_localLevel σ ℓ K hK`: for
  `K` compact (`hK : IsCompact (K : Set σ.FiniteAdelicPoints)`), `K_ℓ` is
  compact, as the image of `K` under the continuous `σ.finiteLocalMap ℓ`.
- `congruenceLevel_mono σ ℓ h`: `H ≤ H'` implies
  `congruenceLevel σ ℓ K H ≤ congruenceLevel σ ℓ K H'`.
- `coe_congruenceLevel`: `K(n)` is the image under the inclusion `K → GJ(𝔸^f)`
  of its trace `(congruenceLevel σ ℓ K H).subgroupOf K` on `K`.
- `isOpen_congruenceLevel σ ℓ hK hH`: for `K` open in `GJ(𝔸^f)` and `H` open
  in `K_ℓ`, `K(n)` is open. Its trace on `K` is the preimage of `H` under the
  continuous `k ↦ k_ℓ` (published `congruenceLevel_subgroupOf`), and the
  inclusion of the open set `K` is an open map.
- `isCompact_congruenceLevel σ ℓ hK hH`: for `K` compact and `H` open in
  `K_ℓ`, `K(n)` is compact: `H` is closed, its preimage is a closed subset
  of the compact `K`.

For a tower `T : CongruenceTower (localLevel σ ℓ K)` (Harris's `K_ℓ(n)`):

- `antitone_congruenceLevel σ ℓ T`: `n ↦ congruenceLevel σ ℓ K (T.lower n)`
  is antitone.
- `iInf_congruenceLevel σ ℓ T`:
  `⨅ n, congruenceLevel σ ℓ K (T.lower n) = primeToLevel σ ℓ K`, that is,
  `⋂_n K(n) = K^ℓ`. One inclusion is the published
  `primeToLevel_le_congruenceLevel`; for the other, an element of every
  `K(n)` lies in `K` and its `ℓ`-component lies in every `T.lower n`, hence
  is `1`.
- `exists_lower_le_ker σ ℓ T hK hρ`: for `K` compact and a smooth
  representation `ρ` of `K_ℓ` on a finitely generated `R`-module `V`, some
  `T.lower n` acts trivially. It is `CongruenceTower.exists_lower_le_ker`
  with `compactSpace_localLevel`.
- `smoothTensorEquiv σ ℓ T hn`, for `[Module.Free R V] [Module.Finite R V]`
  and `hn : T.lower n ≤ ρ.ker`: the `R`-linear equivalence from the
  `K_ℓ ⧸ T.lower n`-invariants of `congruenceTensorAction σ ℓ K (T.lower n)
  (T.factorRep hn)` on `𝒜_ℓ(GJ, R, K(n)) ⊗[R] V` to
  `ellModuleForms σ ℓ K ρ`. It is the published `congruenceTensorEquiv` for
  `T.factorRep hn`, whose target
  `ellModuleForms σ ℓ K ((T.factorRep hn).comp (QuotientGroup.mk' _))` is
  `ellModuleForms σ ℓ K ρ` by definition; the published
  `congruenceTensorEquiv_apply_coe` describes it. This is Harris's (3.8),
  `𝒜_ℓ(GJ, 𝓛, K) ≅ [𝒜_ℓ(GJ, 𝒪/ℓ^m𝒪, K(n)) ⊗ 𝓛]^{K_{ℓ,n}}`, in the
  opposite direction, stated for the action `ρ` of `K_ℓ` itself rather than
  for a representation of `K_{ℓ,n}`.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), §3 "The totally definite case". Worker 61
read the rendered scanned pages. Printed p.306 (one-based PDF page 8), as
quoted in the published `DefiniteForms.md`: "Let `K ⊂ GJ(𝔸^f)` be an open
compact subgroup [...] `K^ℓ = K ∩ GJ^ℓ`, and all functions are taken to be
continuous." Printed p.308 (one-based PDF page 10): "Fix a lattice of
normal congruence subgroups `K_ℓ(n) ⊂ K_ℓ`, `n = 0, 1, 2, …`, with
`⋯ ⊃ K_ℓ(n) ⊃ K_ℓ(n+1) ⊃ ⋯` such that `⋂_n K_ℓ(n) = {1}`. Let
`K(n) = K_ℓ(n) × K^ℓ ⊂ GJ(𝔸^f)`. Let `𝓛` be a free `𝒪/ℓ^m𝒪`-module of
finite order with a continuous action of `K_ℓ`, which we suppose to factor
through the quotient group `K_{ℓ,n} =def K_ℓ/K_ℓ(n)`. Then there is a
canonical isomorphism (3.8)
`𝒜_ℓ(GJ, 𝓛, K) ⥲ [𝒜_ℓ(GJ, 𝒪/ℓ^m𝒪, K(n)) ⊗ 𝓛]^{K_{ℓ,n}}`." The readings
of `K_ℓ`, `K^ℓ`, `K(n)` and (3.7) are those of
`DefiniteFormsDoubleCoset.md`, and that of (3.8) is the one of
`DefiniteFormsTensor.md`.

How the module relates to Harris (an explanation, not formalized):

- The tower. Harris's "lattice of normal congruence subgroups" is read as a
  sequence `n ↦ K_ℓ(n)` of open normal subgroups of `K_ℓ`, decreasing, with
  trivial intersection. "Congruence" (definition by congruence conditions
  on the `ℓ`-adic group) is not formalized; of it we keep only openness,
  which congruence subgroups of the `ℓ`-adic group have. The tower is given
  data: the module constructs no tower for a particular `K_ℓ`. The abstract
  `CongruenceTower G` is for any topological group `G`; Harris's case is
  `G = K_ℓ = localLevel σ ℓ K`.
- Compactness. Harris's `K` is open and compact. The lemmas that need it
  assume `IsCompact (K : Set _)` (and `IsOpen` for
  `isOpen_congruenceLevel`), as the published levels carry no topological
  conditions. For an abstract `G`, compactness and separately continuous
  multiplication (`[SeparatelyContinuousMul G] [CompactSpace G]`) suffice;
  no Hausdorff or total disconnectedness assumption is used.
- `K(n)`. Harris's `K(n) = K_ℓ(n) × K^ℓ` is the published
  `congruenceLevel σ ℓ K (T.lower n)`. `antitone_congruenceLevel`,
  `iInf_congruenceLevel` (`⋂_n K(n) = K^ℓ`), `isOpen_congruenceLevel` and
  `isCompact_congruenceLevel` are our derived statements, not printed in
  Harris 1999.
- Continuous action on `𝓛`. Harris's `𝓛` is finite, hence discrete. An
  action of a topological group on a discrete module is continuous exactly
  when every vector has an open stabilizer, which is the published
  `IsSmooth`. We use `IsSmooth`, so `V` carries no topology.
- Factoring through `K_{ℓ,n}`. Harris supposes that the action factors
  through `K_ℓ/K_ℓ(n)` for the given `n`. `exists_lower_le_ker` shows that
  for compact `K` a smooth action on a finitely generated module factors
  through some `K_ℓ/K_ℓ(n)`, and `isSmooth_iff_exists_lower_le_ker` that
  the actions factoring through some `K_ℓ/K_ℓ(n)` are exactly the smooth
  ones; these are our derived statements. Harris's "free of finite order"
  is weakened to `Module.Finite` for them; (3.8) keeps the published
  hypotheses `Module.Free R V` and `Module.Finite R V`. The coefficient
  ring `𝒪/ℓ^m𝒪` is an arbitrary commutative ring `R`.
- (3.8). The published `congruenceTensorEquiv` takes a representation of
  `K_ℓ ⧸ H`; `smoothTensorEquiv` applies it to `factorRep`, so that the
  forms are those of the given action `ρ` of `K_ℓ`. Harris's derivation of
  (3.8) through (3.9)-(3.11) is not used (see `DefiniteFormsTensor.md`).
- All declarations are ours, derived from Mathlib and the published
  modules named above. `CongruenceTower` reuses Yamaguchi's
  `AntitoneNormalSubgroupFiltration` (published for ramification
  filtrations) for the decreasing normal subgroups. Worker 13 (first
  executor of task 23471a9e) reported that this unit does not overlap
  their level towers (`Langlands.Shimura.LevelColimit`,
  `RestrictedLevelColimit`, `CofinalLevelReindex`), which index colimits
  over compact open subgroups rather than a fixed decreasing sequence.

## Related declarations

- Mathlib `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one`
  (`Topology/Algebra/ClopenNhdofOne`): in a compact totally disconnected
  topological group, every open neighbourhood of `1` contains some open
  normal subgroup. `exists_lower_subset` instead finds a member of a given
  tower, for any compact group with separately continuous multiplication.
- Library `Langlands.Induction.openNormalSubgroup_shrink`
  (`Cohomology/DivisibleSystem/RegularFreeLimit`): the same Mathlib
  statement for neighbourhoods of `1`.
- Library `Langlands.Weil.open_kernel_of_continuous_nonarchimedean_representation`
  and `representation_continuous_of_open_kernel`
  (`Weil/Representation/ContinuityProof`): for finite-dimensional complex
  normed representations, continuity and openness of the kernel.
  `isSmooth_iff_exists_lower_le_ker` concerns algebraic smoothness over an
  arbitrary ring and kernels containing a member of a tower.

## Scope

The module inherits the scope of the published `DefiniteFormsDoubleCoset`:
levels are not decomposed as products `K^ℓ × K_ℓ` and `K_ℓ` is the image of
`K` in the `ℓ`-adic points. It constructs no particular tower of congruence
subgroups, does not treat `D_m(K_ℓ)` along the tower (the direct limit of
the `D_m(K_{ℓ,n})`), limits in `m` or `n`, or Harris's derivation of (3.8)
from (3.10) and (3.11), and constructs no cohomology.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are Mathlib and the published modules named above, pinned to
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
