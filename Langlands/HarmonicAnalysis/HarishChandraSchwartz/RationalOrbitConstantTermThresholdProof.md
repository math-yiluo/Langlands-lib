# The uniform constant-term threshold for the actual orbit coefficients

Module `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitConstantTermThresholdProof`,
namespace `Langlands.HarishChandraSchwartz`.

**Main theorem.** `rationalOrbitConstantTermThreshold :
RationalOrbitConstantTermThresholdStatement hG hi hν I hKc hPK π C hC mu hsq I' hA`, for all the
data of the published statement (module `RationalOrbitPositiveConstantTerm`) and its independent
universes `u` (field) and `uV` (representation). The statement pair is imported unchanged.

## What is proved

For every smooth orbit section `ψ ∈ C^∞(O, P)` there is one `t > 0`, chosen before the orbit
point and the chamber point, such that for **every** `ω` in the unitary orbit `O` and **every**
point `m` of the actual minimal Levi `M_0(F)` in the closed chamber with `⟨α, H_0(m)⟩ ≥ t` for
all simple roots `α ∉ Δ_0^{M'}`,
`f_ω(m) = δ_{U'}(m)^{1/2} (f_ω)_{P'}(m)`, where `f_ω = E^G_P ψ_ω` is
`rationalInducedOrbitCoefficientMap … ψ ω`, `(f_ω)_{P'}` is the published
`rationalOrbitConstantTerm` (the Proposition I.6.2 constant term `standardConstantTerm hA` for
the target's split component `A`), and `δ_{U'}^{1/2}` is `standardHalfModulus`. Every standard
index `I'` is allowed, including `I' = Δ_0` (`P' = G`). No hypothesis is added: the theorem has
exactly the target's type. Of the target's structural premises, the proof uses the standard
cocharacter `ζ` of `I'`, the compactness of `K0`, `SimultaneousStandardBasisAt i ν K0` and the
Levi Cartan covering for `J = ∅`; the other premises (openness of `K0`, the target's basis `B`
with its basis-member clauses, the finite Cartan covering of `G` and the other Levi coverings)
are not needed. No constant-term existence, coefficient bound, temperedness, exponent estimate
or asymptotic statement is assumed.

## Source and how uniformity is obtained

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques (d'après
Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333 (literature id
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`; PDF page = printed − 234).

- Proposition I.4.3 (printed p. 245): for `(v, v̌)` there is `t > 0` such that for all
  `m ∈ M̄_0^+`, `δ_P(m)^{−1/2} ⟨π(m)v, v̌⟩ = ⟨π_P(m) j_P(v), ǰ_P̄(v̌)⟩_P` with `P = P_{m,t}`.
- I.5 (printed pp. 245–246): the results of I.3 and I.4 (except I.4.4) remain valid for
  algebraic `B`-families of admissible representations. In the proof of the I.4.1 analogue
  (printed pp. 246–247) the only place where uniformity in the family enters is property (3):
  one compact open subgroup `U_c` of `U` kills all of `V^H ∩ Ker(j_P)`, obtained from finite
  generation over the Noetherian `B`.
- The proofs of VI.2.3 (printed p. 299) and VI.3.1 (printed p. 303) use, "d'après I.5 et la
  Proposition I.4.3", one `t` for the whole family `χ ↦ E^G_P sp_χ ψ`.

The implemented proof obtains this uniformity directly, without constructing `B`-families: on
the dominant lattice of the actual standard parabolic, the threshold of Casselman's argument
depends only on a good compact open subgroup `K₂` and on an upper bound `d` for `dim V^{K₂}`.
This has two parts. The abstract module `StablePairingDimensionThreshold` replaces the
Noetherian finite generation of I.5 (3) by the Fitting decomposition of the compression of the
strict element on the finite-dimensional `V^{K₂}`. Its commutation and factorization hypotheses
are conditions on the compressions of the given representation, so by themselves they are not
uniform. In `StandardCasselmanDimensionThreshold` these hypotheses are derived from group-level
facts: the Iwahori factorization of `K₂`, the contraction by dominant lattice points, and
`ϖ^λ = ϖ^{λ − d z} g^d`. Those facts hold for every admissible representation with
`dim V^{K₂} ≤ d` at once, and that is what makes the threshold uniform. For the orbit this needs
exactly two algebraic-family facts, both supplied by published Library results:

1. **One compact open subgroup for the whole orbit.** All `f_ω` are bi-invariant under one
   compact open `H ≤ K` (`unitaryOrbitCoefficientMap_biInvariant`, wrapped here as
   `exists_rationalInducedOrbitCoefficientMap_biInvariant`), because the parameter family of
   `ψ` is a finite sum of smooth functions times fixed compact-picture vectors.
2. **One dimension for the whole orbit.** Every `ω` has the representative
   `R = π ⊗ χ`, `χ` a unitary unramified character (from `ω`'s orbit membership, as in the proof
   of `unitaryOrbitRepresentativeDiscreteSeriesOrbit_surjective`); restriction to `K` identifies
   `I_P^G(π ⊗ χ)` with one fixed compact picture of `π`
   (`unramifiedNormalizedInductionCompactEquiv`), so `dim I_P^G(π ⊗ χ)^{K₂}` is one number `d₀`
   independent of `ω`.

A threshold depending on `ω` is therefore never used: `t` is produced from `K₂` and `d₀` before
`ω` and `m` are introduced.

## Proof structure (helper modules)

- `StablePairingDimensionThreshold`: abstract dimension-controlled asymptotics
  (`IsStablePairing.asymptotics_of_finrank_le`); its commutation and factorization hypotheses
  concern the compressions of the given representation.
- `StandardCasselmanDimensionThreshold`: I.4.3 on the dominant lattice for the actual standard
  data with threshold `d Σ |⟨α, z⟩|` (`exists_dimension_threshold_standardCasselmanPairing`),
  uniform in the admissible representation because the operator hypotheses of the abstract
  lemma are derived there from group-level facts.
- `RationalMinimalLeviDimensionThreshold`: extension to every point of the closed chamber of
  `M_0(F)` via the minimal-Levi Cartan covering (`exists_region_dimension_threshold`).
- `RationalConstantTermRegionComparison`: identification with `standardConstantTerm hA'` for an
  arbitrary compatible split component and span induction
  (`exists_constantTerm_dimension_threshold`).

## This module

- `piRepresentation`, `isSmooth_piRepresentation`, `piProjection` (new auxiliary definitions):
  the representation `g ↦ (x ↦ (j ↦ ρ(g)(x j)))` on tuples of vectors, smooth for finite index
  types, with its projections as intertwining maps.
- `map_averageMap_pi_of_forall_eq`: a linear form constant on the `K`-orbit of a tuple takes the
  same value at the tuple of `K`-averages (`Jacquet.map_averageMap_of_forall_eq` for the tuple
  representation and `Compact.averageMap_commute` with the projections).
- `mem_span_fixedCoefficients_of_biInvariant`: a function in `A(π)` (`coefficientFunctionSpace`)
  that is bi-invariant under a compact open `K` lies in the span of the coefficients
  `x ↦ ℓ(π(x) v)` with `v` and `ℓ` both `K`-fixed. Write `f = Σ_j ℓ_j(π(·) v_j)`
  (`Submodule.mem_iSup_iff_exists_finsupp`), average the `v_j` using right invariance, then the
  `ℓ_j` using left invariance.
- `finrank_fixedVectors_eq_of_equiv_comp`: an equivalence between the restriction of `σ` to a
  subgroup `K` and a representation `τ` of `K` preserves the dimension of the `H`-fixed vectors
  for `H ≤ K` (Mathlib's `Representation.Equiv`).
- `rationalOrbitConstantTermThreshold`: from `SimultaneousStandardBasisAt` choose the basis
  `B₂` and split components of all standard Levis (as in the published
  `SimultaneousStandardBasisAt.exists_waldspurger_uniform_asymptotics`), standard cocharacters
  from the proved `standardCocharacter`. Take `H` from fact 1, `K₁ ∈ B₂` inside `H`, then `K₂`
  from `exists_constantTerm_dimension_threshold` (for `J = rootSet I'`, the target's `A`, `hA`,
  `ζ`), `d₀` the dimension of the `K₂`-fixed vectors of the compact picture of `π`, and `t` for
  `d₀`. Given `ω` and `m`, pass to the representative `R` (`rationalInducedOrbitCoefficientMap_representative`);
  `f_ω` lies in `A(I_P^G R)` (`rationalInducedCoefficientMap_mem_coefficientFunctionSpace`), is
  bi-`K₁`-invariant, hence in the span of `K₁`-fixed coefficients; `I_P^G R` is admissible
  (`normalizedInductionFunctor_obj_isAdmissible`) with `dim (I_P^G R)^{K₂} = d₀` (fact 2); the
  threshold statement for `t` concludes.

## Check

`lean_check` (Lake build of the five
modules over Library `ecb96e554fed652972a5c0308d69b041f6bc54e4`): 0 errors, 0 warnings; the
theorem has level parameters `u, uV` and axioms `propext`, `Classical.choice`, `Quot.sound`.

The Library also gives a [proof using minimal-Levi thresholds](RationalOrbitConstantTermThresholdMinimalLeviProof.md).
