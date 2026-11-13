# Renard VI.2.3 for G(F), conditional on Chapter V structure and VI.2.2

This module reduces the uniform admissibility theorem for `G(F)`,
`RationalPointsUniformAdmissibilityStatement.{u, v}`, to four published Library
propositions that are not yet proved. It is a conditional, intermediate result.
It does not prove the uniform admissibility theorem.

The source is Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, Theorem VI.2.3 and its proof (printed
pp.140–141 / PDF pp.146–147). It is registered as
`renard-2026-representations-groupes-reductifs-padiques`. The conclusion is the
published proposition in
`Langlands/Representation/CuspidalSupport/UniformAdmissibilityStatements.lean`,
and its Markdown gives its correspondence with the source.

## The reduction statement

`CuspidalSupport.RationalPointsUniformAdmissibilityReductionStatement.{u, v}` is
the implication

```
BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement.{u} →
  StandardCocharacterStatement.{u} → RelativeRootSystemStatement.{u} →
    RationalPointsIrreducibleAdmissibleStatement.{u, v} →
      RationalPointsUniformAdmissibilityStatement.{u, v}
```

Here `u` is the universe of the local field and `v` that of the representation
carriers. The four premises are published Library propositions, used exactly as
published:

- `BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement`
  (`Langlands/BruhatTits/SpecialCompact/JointBasisStatement.lean`). For a maximal
  split torus with a generic cocharacter, it gives a special vertex whose
  special compact subgroup `K₀` has the Chapter V properties used in Renard
  V.5. These include the Cartan comparison, standard-Levi compatibility, and a
  basis of compact open subgroups normal in `K₀` and adapted to every standard
  parabolic subgroup (`SimultaneousStandardBasisAt`).
- `GroupScheme.StandardCocharacterStatement`
  (`Langlands/GroupScheme/Rational/StandardCocharacterStatement.lean`): the
  existence of standard cocharacters.
- `GroupScheme.RelativeRootSystemStatement`
  (`Langlands/GroupScheme/Rational/Statement.lean`): the relative roots form a
  root system.
- `Aubert.General.RationalPointsIrreducibleAdmissibleStatement`
  (`Langlands/Representation/Aubert/General/IrreducibleAdmissibleStatement.lean`):
  Renard VI.2.2, every irreducible smooth representation of `G(F)` is admissible.

The conclusion is the VI.2.3 Theorem for `G(F)` with carriers in `Type v`.
Nothing else is assumed or concluded.

The reduction is internal content. It is a composition of published Library
theorems with the four premises, and the same module proves it. Renard's proof
uses the same three ingredients:

- the finiteness of `V^K` for irreducible `V` (VI.2.2);
- the decomposition of the level-`K` Hecke algebra
  `H(G, K) = Σ_j H₀ A D_j H₀` from Theorem V.5.3, with `A` commutative;
- the bound on the dimension of simple modules of such an algebra.

The Lean proof follows this route. It uses the Library's fixed-level sandwich
data in place of the printed form of V.5.3, so its constant differs from
Renard's `(h²q)^(2^(d-1))`.

## Proof

### Generic lemmas in `Langlands.Hecke`

- `centralTwistHom f g hg` is the monoid homomorphism `x ↦ f x * g x`, where
  `g` takes central values.
- `subtype_mem_map_inf` and `exists_mem_inf_of_mem_map_inf` move membership in
  `A ⊓ B` across the inclusion of a subgroup `H`.
- `subtype_mem_iwahoriPositiveMonoid_map`: if `a ∈ H` lies in
  `iwahoriPositiveMonoid K N M Nbar` for subgroups of `H`, its image lies in the
  positive monoid of the image subgroups.
- `exponentPrecompHom f` precomposes exponent vectors with `f`, and
  `powProdHom c` sends an exponent vector `n` to `∏ j, c j ^ n j` in a
  commutative monoid. Both are monoid homomorphisms.
- `exists_center_monoid_generators P` takes a homomorphism `P : G →* B` to a
  commutative group `B` that is finitely generated over `ℤ`. It gives finitely
  many central elements `c j` such that every central `z` has the same image
  under `P` as some product `∏ j, c j ^ n j` with `n j ∈ ℕ`. The image of the
  centre is a subgroup of a Noetherian `ℤ`-module, hence finitely generated as a
  group and so as a monoid (`Subgroup.fg_iff_submonoid_fg`). The `c j` are
  preimages of a finite monoid generating set.

### The main bound

`Aubert.General.RationalPointFamily.exists_uniform_fixedVectors_rank_bound`
fixes a maximal split torus `i` with a generic cocharacter `ν`, the four
premises, and an open subgroup `K` of `G(F)`. `G(F)` carries the point topology.
The theorem gives `c` with `rank (A^K) ≤ c` for every irreducible smooth complex
representation `A` of `G(F)`. Write `⁰G = Plancherel.rationalCommonNormKernel G`.

1. *Cartan data.* `nonempty_normKernelFundamentalCocharacters` (standard
   cocharacters and relative root system) gives fundamental cocharacters `d`.
   Their orthant homomorphism `d.orthantHom` takes `ℕ^Δ` to `⁰G`, where `Δ` is
   the set of simple relative roots. The joint statement gives `D, x` with the
   special compact subgroup `K₀ = D.specialCompactSubgroup x`, compact, and with
   the simultaneous basis `hbasis`. `exists_isFiniteLatticeTransversal` and
   `d.exists_finite_centralCartanFactorization` then give a finite set `R` such
   that every `g ∈ G(F)` is `k₁ * (d.orthantHom n * t) * k₂ * z` with
   `k₁, k₂ ∈ K₀`, `t ∈ R`, `n ∈ ℕ^Δ` and `z` central.
2. *A common level.* `nonempty_normKernelCompressionLevel`, applied to the
   preimage of `K` in `⁰G`, gives a compact open subgroup `L.level` of `⁰G`
   below it. The level has an Iwahori factorization along the standard minimal
   parabolic subgroups of `⁰G`. Every orthant element lies in its positive
   monoid and conjugates its Levi part into it. `K₀ ∩ ⁰G` normalizes it. Its
   image `KL = Plancherel.rationalNormKernelAmbientLevel G L.level` in `G(F)`
   is compact open by `Plancherel.isCompact_rationalNormKernelAmbientLevel`,
   and `KL ≤ K`.
3. *Central directions.* The rational character lattice is finitely
   generated (`GroupScheme.rationalCharacterLattice`, proved). Hence so is the
   valuation image `Plancherel.rationalValuationImageProjection G`, whose kernel
   is `⁰G` (`Plancherel.rationalValuationImageProjection_ker`).
   `exists_center_monoid_generators` gives central `c₁, …, c_r` such that each
   central `z` is `∏ c_j^(m j) * w` with `w ∈ ⁰G ∩ Z(G)`.
4. *Sandwich data.* Let `N', M', N̄'` be the images in `G(F)` of the norm-kernel
   standard unipotent, Levi and opposite unipotent subgroups for the empty set
   of simple roots. Let `e : ℕ^(Δ ⊕ Fin r) → G(F)` be
   `centralTwistHom` of the orthant on the first coordinates and of
   `powProdHom c` on the last ones. The level data of step 2 transport to `KL`
   in `G(F)`. They give the Iwahori factorization `KL = (KL ∩ N̄')(KL ∩ M')(KL ∩ N')`,
   positivity of every `e n` (central factors are positive by
   `Hecke.center_le_iwahoriPositiveMonoid`), and `e n (KL ∩ M') (e n)⁻¹ ⊆ KL`.
   `Γ = K₀ ⊔ (⁰G ⊓ Z(G))` is compact by `isCompact_sup_of_central` and
   `Plancherel.isCompact_rationalCommonNormKernel_inf_center`. It normalizes
   `KL` by `L.ambient_normalized` and because central elements normalize every
   subgroup. Steps 1 and 3 give the decomposition `g = a * (e n * t) * b` with
   `a, b ∈ Γ`, `t ∈ R`. The central factor `∏ c_j^(m j)` is moved into `e`, and
   `w` into `b`. `Hecke.nonempty_fixedLevelSandwich_of_residual_iwahoriCartan`
   then gives finite sandwich data `S` for the Hecke corner at level `KL` with
   Haar measure.
5. *The bound.* Take `c = S.dimensionBound`. For irreducible `A`, the premise
   VI.2.2 makes `A^KL` finite-dimensional. `FixedLevelSandwich.finrank_le` bounds
   `finrank A^KL` by `c`. Since `KL ≤ K`, `A^K ⊆ A^KL` (`fixedVectors_antitone`),
   so `rank A^K ≤ c`.

### The reduction

`CuspidalSupport.rationalPointsUniformAdmissibilityReduction` proves the
reduction statement. Given `F`, `G` and a compact open `K`, it picks a maximal
split torus with a generic cocharacter by
`exists_maximalSplitTorus_genericCocharacter`. Finiteness of the simple roots
comes from `finite_simpleRoot`. The relative root system for that torus comes
from `RelativeRootSystemStatement`, and the result is
`exists_uniform_fixedVectors_rank_bound`. Compactness of `K` is not used,
because the bound is obtained at the compact level `KL ≤ K`.

## Scope

The theorems are unconditional apart from their stated premises. Proving the
VI.2.3 Theorem for `G(F)` still requires proofs of the four premises. With such
proofs at carrier universe `max u v`, the assembly reduction
`UniformAdmissibilityAssemblyReductionStatement` (module
`Langlands/Representation/CuspidalSupport/UniformAdmissibilityAssemblyReduction.lean`,
a separate candidate) reduces the target `UniformAdmissibilityStatements.{u, v}`
to VI.2.4 alone.
