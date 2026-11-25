# Isotypic local trace factorization on a cuspidal summand from one local occurrence

Module `Langlands.TraceFormula.IsotypicTrace.CuspidalOccurrenceReduction`. This is the
consumer-facing result of the reduction of
`GroupSchemeCuspidalIsotypicTraceFactorizationStatement` to one local occurrence. It proves clauses 0', 1 and 2 of
that statement for an irreducible cuspidal summand `P` and an irreducible admissible
representation `ρ` of `G(F_v)` that occurs in `P`, with that same `ρ`. The occurrence (clause 0
together with irreducibility and admissibility of `ρ`) is a hypothesis. It is the content of
a local occurrence statement (some irreducible admissible representation of `G(F_v)` occurs in
every irreducible cuspidal summand `P`), which is not proved here.

## Declarations

* `restrict_norm`, `restrict_continuous`: the restricted action is norm preserving with
  continuous orbits.
* `awayAction F G v π hπnorm hπcont P hPinv νH fw : P →L[ℂ] P`: the integral of `fw` over the
  away subgroup against the restricted action, defined as `0` when `fw` is not `νH`-integrable
  on the away subgroup. `awayAction_apply` gives its value in the integrable case.
  `awayAction_commute`: it commutes with `π (ofPlace y)`, because the away subgroup commutes
  with the image of `ofPlace`.
* `compression_split_eq`: for `fv ≠ 0`, `fw` right `G(F_v)`-invariant and `R` the integrated
  action of `g ↦ fv (g_v) * fw g`, the compression of `R` to `P` is `X ∘ awayAction … fw`,
  where `X` integrates `fv` against the local action. This is `integral_split_eq` combined
  with `compression_integratedIsometricAction`.
* `isotypicTraceFactorization_of_occurrence_generic`: the same three clauses for an arbitrary
  inner-product-preserving continuous action `π` of `G(𝔸_F)` on a Hilbert space `E`, an
  irreducible complete invariant `P ≤ E` and an occurrence `j₀`. The integrated action is
  given by any operator `R` with `R x = ∫ (fv (a_v) * fw a) • π a x ∂ν`. The twisted clause is
  stated for any automorphism `Θ` with `Θ ∘ ofPlace = ofPlace ∘ θv` and any injective `IP` on
  `P` with `IP ∘ π a = π (Θ a) ∘ IP`; the twisted compression is then
  `(P_P ∘ R ∘ ι_P) ∘ IP`. Proof: apply `isotypic_of_occurrence`, `exists_trace_factorization`
  and `exists_twisted_trace_factorization` to the restricted action on `P`. The splitting
  hypothesis is `exists_split`, irreducibility is `restrictAction_irreducible`, and the measure
  is normalized by `exists_awayHaar`. The functional `C` is the abstract functional applied to
  `awayAction … fw`. When `fv = 0` both sides of each identity vanish.
* `cuspidalIsotypicTraceFactorization_of_occurrence`: the cuspidal case. Here
  `E = fullAEL2CuspidalSubmodule`, `π = fullAEL2CuspidalBoundedRightAction` (inner preserving
  as a linear isometry equivalence, with continuous orbits by `fullAEL2CuspidalOrbitMap`), and
  `R = fullAEL2CuspidalIntegratedAction`. For the twisted clause,
  `IP = nestedRestrict S P I_Θ`. It is injective since `twistOperator` is norm preserving
  (`norm_twistOperator_apply`), and covariant by `twistOperator_quotientL2RightTranslate` and
  `nestedRestrict_covariant`. The compression `BP` of the target equals
  `(P_P ∘ R ∘ ι_P) ∘ IP` by `nested_compression_comp` and
  `fullAEL2CuspidalIntegratedAction_val`. The statement lists the hypotheses of the target
  statement for `P`, then `ρ`, `hρ`, irreducibility of `ρ` and the occurrence `j₀`. Its
  conclusion is clauses 0', 1 and 2 of the target, verbatim, for this `ρ`.
* `cuspidalIsotypicTraceFactorization_of_exists_occurrence`: from the existence of such an
  occurrence (with carrier in `Type u`), the full conclusion of
  `GroupSchemeCuspidalIsotypicTraceFactorizationStatement` for `P`, including clause 0.

A proof of that local occurrence statement therefore yields the target
statement by applying `cuspidalIsotypicTraceFactorization_of_exists_occurrence` to each
summand. That final step is not in this module, because the occurrence statement is not in
the Library.

Two theorems carry `set_option maxHeartbeats 1000000`, because elaborating the concrete
cuspidal Hilbert space is expensive.

## Sources and provenance

Derived content: this is the reduction carried out for this project. The route is the one in
the Markdown of the target statement (Getz–Hahn 2024, Theorem 3.10.2, printed p. 97, and
Proposition 5.3.8 and Theorem 5.3.9, printed p. 141; Folland 2015, Theorem 7.17, printed
p. 237; Flath 1979, Theorem 1, printed pp. 179–180). The tensor product decomposition is
replaced by a Hilbert sum of closures of occurrences of `ρ`, and Hilbert-space Schur is
replaced by the algebraic Schur lemma for admissible `ρ`. The type I and admissibility theorems
cited there are used only through the occurrence hypothesis.
