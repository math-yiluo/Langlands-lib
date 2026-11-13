# Tate's spectral conductor formula from refinement and rank-one transport

Worker 4803 wrote this module (Task 4803).

## Statement

`SpectralConductor.SpectralConductorRankOneReductionStatement.{uF, uV}` says: for every
prime `p` and every `F : PadicField.{uF} p`,
1. if `Ramification.Padic.FiniteInertiaConductorRefinementStatement F A` holds for every
   finite-dimensional complex representation `A` of the local Weil group with carrier
   universe `max uF uV`, and
2. `SpectralConductor.CommonClosureRankOneConductorStatement F` holds,

then `ConductorExponent.SpectralConductorStatement.{uF, uV} F` holds. That is
Tate (3.4.5) and Deligne (5.5.2):
`ε(A ⊗ ω_s, ψ, μ) = ε(A, ψ, μ) · q_F^{-(a(A) + n(ψ) dim A) s}` for every supplied system,
genuine continuous `A`, finite-inertia presentation `P` with surjectivity, and `s ∈ ℂ`.
The first premise is one clause of the Library's
`InertiaSurjectivityPresentationAndConductorIndependenceStatement` (Task 5737 proves it).
The second is stated in module `SpectralConductorRankOneStatement`.
`spectralConductorRankOneReduction` proves the implication. It assumes neither premise
beyond the hypotheses.

## Implemented proof

Let `x` be the class of `A`.
1. Degree-zero generation (the Library's `commonClosureDegreeZeroGeneration`, made
   finite by `exists_finset_generators`) writes `x - dim A · 1` as an integral
   combination of finitely many `Ind_L(χ - χ')`.
2. `exists_presentingField` gives an actual finite Galois `M ⊇ P.extension` containing
   every inducing field `L` and presenting every `χ, χ'`.
3. Put `a(y) = conductorFunctional F M y · log q_F`.
   - `a(1) = 0` (`conductorFunctional_one`).
   - For each generator: `conductorFunctional_induce_eq`, `lClassSum_eq_characterConductor`
     (from premise 2 and `hε.1`) and `inductionFactor_mul_logCardinality` give
     `a(Ind_L(χ - χ')) = (a(χ̃) - a(χ̃')) log q_L`.
4. `mem_formulaSubgroup_of_span` (epsilon side) gives
   `ε(ω_s x) = ε(x) · exp(-s (a(x) + n(ψ) dim A log q_F))`.
5. `conductorFunctional_baseClass` and premise 1 (applied to `P`, `M`, `hsurj` and the
   surjectivity of `weilInertiaRestriction F M`) identify `a(x)/log q_F` with
   `P.artinConductor hsurj`. The degree of `x` is `dim A`, `log q_F` is the complex
   logarithm of `baseCardinality F` (`residueCardinality_base`), and
   `Complex.cpow_def_of_ne_zero` turns the exponential into
   `q_F^{-(a(A) + n(ψ) dim A) s}`.

## Sources

Tate, *Number theoretic background* (1979), (3.4.5), printed p. 15 (PDF p. 24 of the
Corvallis Part II volume), proved there from the rank-one case via inductivity in
degree zero. Deligne (1973), (5.5.2), printed p. 548 (PDF p. 48). Serre, *Local
Fields*, VI §2, Propositions 2 and 4, printed pp. 100–102, for the conductor of an
induced representation.
