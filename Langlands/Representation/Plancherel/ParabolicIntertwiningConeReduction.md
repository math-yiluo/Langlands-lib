# Convergence and domination on actual parabolic regions from the cone decay

Lean module: `Langlands.Representation.Plancherel.ParabolicIntertwiningConeReduction`, namespace
`Langlands.Plancherel`.

## Purpose and provenance

Provenance: internal. Waldspurger, *La formule de Plancherel pour les groupes p-adiques,
d'après Harish-Chandra* (2003), IV.1.1, printed pp. 277–281 (PDF pp. 43–47), proves that the
standard intertwining integral converges absolutely, locally uniformly, when the twisting
character lies far enough inside a cone. The proof combines moderate growth of coefficients,
the description of `(U ∩ U') \ U'` through `Ū ∩ U'`, integrability of negative powers of the
height there, and an estimate showing that on the cone the Levi component of the Iwasawa
decomposition of `n̄ ∈ Ū ∩ U'` makes `δ^{1/2} χ` decay faster than any given power of `‖n̄‖`.
This module names that last estimate, `ParabolicOppositeConeDecay`, and proves that it, together
with squared-modulus compatibility, admissibility and a common coefficient growth exponent,
gives one threshold `R` with

- full convergence (`domain … = ⊤`) of the actual standard integral at every character of the
  region `C R`, and
- local integrable domination of the compact integrands on `C R`
  (`CompactIntegralLocallyDominatedOn`).

These are exactly the per-representation conclusions of the remaining-inputs proposition for
`ConditionalParabolicIntertwiningStatement` (Worker 1615's `ConditionalParabolicIntertwiningInputs`,
a separate candidate). The cone decay is not proved here; for the regions of the host statement
it needs the relative root reflections. The proof is derived from Library results and is not
transcribed from the source.

## Setting and notation

The data are those of the host statement, as in the module `ParabolicOppositeQuotient`: a
nonarchimedean local field `F`; a smooth affine group `G` of finite type over `F` whose point
group `G(F)` is locally compact, nonarchimedean and Hausdorff; parabolic root presentations `r`,
`r'` of `p : P ⟶ G`, `p' : P' ⟶ G` with a common Levi (`hLevi`) and geometric radicals `hn`,
`hn'`; subgroups `Ppt`, `Upt`, `P'pt`, `U'pt` of `G(F)` identified with the actual points by
`hPpt`, `hUpt`, `hU'pt`; `Mpt = parabolicLeviPointSubgroup p l`; decompositions `h`, `h'`;
closedness `hU`, `hU'`, `hP`; a compact open `K` with `G(F) = Ppt K` (`hPK`); continuity `hr`
of the Levi projection; a compatible quotient measure `qν` on `(U ∩ U') \ U'` for regular
right-invariant Haar measures `μU'`, `μI` (`hqν`); `ν = parabolicLeviRationalNormCharacters r`.
`Ū(F) = parabolicOppositeRadicalPoints r`. For a closed representation `ρ₀` of `G`,
`‖g‖ = rationalMatrixNorm F ρ₀ g`. `C : ℝ → Set (unramifiedCharacters ν)` is any family of
character regions (for the host statement, `parabolicPointUnramifiedIntertwiningRegion`).

## Declarations

- `ParabolicOppositeConeDecay r h hU K ρ₀ C` (definition, a `Prop`; `U'pt` is an implicit
  argument): for every `d : ℕ` and `s : ℝ` there is `R : ℝ` such that for every section
  `σ : (U ∩ U') \ U' → U'pt` of the quotient map with values in `Ū(F)`, the predicate
  `IsLocallyUniformQuotientDecayOn h hU K ν U'pt σ ξ W (C R)` (module `CompactIntertwiningQuotientDecay`) holds with
  `ξ m = ‖m‖ ^ d` and `W q = ‖σ q‖ ^ (-s)`. Explicitly: near each `χ₀ ∈ C R` one constant bounds
  `‖δ(m)‖ ‖χ(m)‖ ‖m‖ ^ d` by a multiple of `‖σ q‖ ^ (-s)` for every factorization `σ q = p κ`,
  `m` the Levi projection of `p`.
- `exists_region_convergence_domination_of_coneDecay` (main theorem): with the data above, a
  closed representation `ρ₀` on a nonempty `Fin N`, squared-modulus compatibility `hsq`, an
  admissible representation `π` of `Mpt` with a common exponent `d` such that every coefficient
  satisfies `‖ℓ (π(m) v)‖ ≤ c ‖m‖ ^ d`, and `ParabolicOppositeConeDecay r h hU K ρ₀ C`, there is
  `R` such that
  - for every `χ ∈ C R`, `domain h hU U'pt (π.twist χ …) qν = ⊤`, and
  - for every unimodularity proof `hδ` of `Upt`,
    `CompactIntegralLocallyDominatedOn h hU hδ K hP hK hPK ν hν hr π U'pt qν (C R)`.

## Proof as implemented

1. Choose `t ∈ Fˣ` with `t ^ n → 0` (public `exists_unit_tendsto_pow_zero`) and let `hc` be the
   open-cell contraction data `parabolic_isOpenCellContraction` (module
   `ParabolicOppositeQuotient`).
2. `qν` is regular and right invariant (fields of `IsCompatible`), so
   `exists_integrable_quotientChart_symm_rationalMatrixNorm` gives `D` such that
   `q ↦ ‖c⁻¹ q‖ ^ (-s)` is `qν`-integrable for `s > D`, where `c = hc.quotientChart`.
3. Take `d` from the growth hypothesis and `R` from the cone decay at `(d, D + 1)`, and let
   `σ q = c⁻¹ q`. It is a section of the quotient map (`quotientChart_apply` and
   `apply_symm_apply`) with values in `Ū(F)`. So the decay predicate holds on `C R` with
   `ξ = ‖·‖ ^ d` (nonnegative because `‖·‖ ≥ 1`) and the integrable `W = ‖σ ·‖ ^ (-(D + 1))`.
4. Convergence: `scalarDomain_twist_eq_top_of_quotientDecay` (module
   `CompactIntertwiningQuotientDecay`) gives full scalar convergence of every twist on `C R`.
   The twist is admissible (public `SmoothRep.isAdmissible_twist_iff`), the Levi is closed
   (public `isClosed_parabolicLeviPointSubgroup`), and public `scalarDomain_eq_domain` with
   `hsq` identifies the scalar domain with the actual domain.
5. Domination: `compactIntegralLocallyDominatedOn_of_quotientDecay` with the same data.

## Scope

The cone decay, squared-modulus compatibility and the coefficient growth exponent are
hypotheses. The growth exponent follows from the published moderate-growth statements only
after transport from the Levi scheme to `Mpt`, which is not done here. The module proves no
rational continuation and does not complete the host theorem.
