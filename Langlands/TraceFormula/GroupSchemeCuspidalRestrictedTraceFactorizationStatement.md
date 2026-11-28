# Restricted tensor product factorization of traces and twisted traces, with unit tails, on an irreducible cuspidal summand (statement)

Module `Langlands.TraceFormula.GroupSchemeCuspidalRestrictedTraceFactorizationStatement` contains
one proposition definition and no proof:

- `Langlands.TraceFormula.GroupSchemeCuspidalRestrictedTraceFactorizationStatement.{u}`.

Let `P` be an irreducible closed invariant subspace of the cuspidal space `S` of the positive
rational quotient of `G(𝔸_F)`, the space on which the Library's simple and twisted trace formula
statements for this quotient are stated. The Library statements
`GroupSchemeCuspidalLocalTraceFactorizationStatement` and
`GroupSchemeCuspidalMultiPlaceTraceFactorizationStatement` split the local characters at one
place, or at finitely many places and `∞`, off the traces on `P`, and leave an unknown
functional `C` of the remaining components. The present statement fixes an integral family of
compact open subgroups `U p` at all finite places and takes test functions whose component at
every finite place outside a finite set `Σ` is the indicator function `1_{U p}`. For these it
asserts that the trace on `P` is a positive constant times the product of the local characters at
`Σ` and the archimedean character. The twisted form asserts the same for `R(f) ∘ I_Θ` with
twisted local characters and a nonzero constant. It gives the local factors at all finite places
at once.

## Setting and notation from the Library

The group data, the cuspidal space, its action, the integrated operators, the twisting operator
and the archimedean conventions are those of `GroupSchemeCuspidalLocalTraceFactorizationStatement`
and `GroupSchemeCuspidalMultiPlaceTraceFactorizationStatement`, whose Markdown explains them in
full. In brief:

- `F : Type u` is a number field and `G` an affine group scheme over `Spec F`, locally of finite
  type, with `hPD : ParabolicDynamicStatement.{u}`, `hG : IsConnectedReductive G`, a central map
  `i : T.toGrp ⟶ G` (`hc : IsCentral i`) from a commutative group scheme `T` with injective
  character restriction `hi` of finite-index range, an isomorphism `e` of `T` with a split torus
  indexed by a finite type `I`, and right invariance of Haar measure on `normOneSubgroup F G`.
- `G(𝔸_F) = AdelicGroupPoints F G`. The subgroup `positiveRationalSubgroup F G T i` is generated
  by `G(F)` and the positive real points of the central torus. Its left quotient carries the
  measure `positiveRationalQuotientHaarMeasure F G T i`, written `μ_Q`.
  `S := fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc` is the closed cuspidal subspace of
  `L²(μ_Q)`, and `πc a := fullAEL2CuspidalBoundedRightAction … a` is right translation by
  `a ∈ G(𝔸_F)` on `S`.
- For a Haar measure `ν` on `G(𝔸_F)` and a `ν`-integrable `f`,
  `fullAEL2CuspidalIntegratedAction … ν f hf`, written `R_S(f)`, is `x ↦ ∫ f(a) • πc(a) x dν(a)`
  on `S`, and `haarQuotientL2IntegratedAction F G T i hi I e hc ν f hf`, written `R(f)`, is the
  same integral on all of `L²(μ_Q)`.
- For a topological group automorphism `Θ` of `G(𝔸_F)` preserving
  `positiveRationalSubgroup F G T i` (`hΘ`) whose induced homeomorphism of the quotient has an
  inverse preserving `μ_Q` (`hΘμ`), `twistOperator (positiveRationalSubgroup F G T i) Θ hΘ μ_Q hΘμ`,
  written `I_Θ`, is the operator `φ ↦ φ ∘ Θ⁻¹` on `L²(μ_Q)` (module
  `Langlands.TraceFormula.TwistedOrbital`). It satisfies `I_Θ R(g) = R(Θ g) I_Θ`.
- Finite places: `Langlands.Global.FinitePlace F`. For a finite place `v`,
  `G(F_v) = PlaceGroupPoints F G (.inr v)`, `atPlace F G (.inr v) g = g_v` is the local component
  and `ofPlace F G (.inr v)` inserts a local point at `v`, with all other components `1`.
- The archimedean group `G(F_∞) = G(F ⊗ ℝ) = InfiniteAdelicGroupPoints F G`, with its Borel
  σ-algebra. `AdelicGroupPoints.infinite F G g = g_∞` is the archimedean component and
  `AdelicGroupPoints.ofInfinite F G` inserts an archimedean point (module
  `Langlands.Global.AdelicGroupProduct`).
- Integral families: `AdelicGroupPoints.IsUniformlyIntegral F G K` (module
  `Langlands.Global.AdelicGroupLocalPoints`) says that for every regular function `a` on `G`, at
  almost every finite place `v`, the values of `a` on the subgroup `K (.inr v)` are integral.
  `AdelicGroupPoints.extendFinite F G K` (module `Langlands.Global.AdelicIwasawaAssembly`) extends
  a family of subgroups at the finite places by `⊤` at the archimedean places.
- Finite-place representations: `Langlands.fixedVectors ρ K` is the subspace of `K`-fixed
  vectors, `Langlands.IsSmooth` and `Langlands.IsAdmissible` are smoothness and admissibility
  (module `Langlands.Representation.Smooth.Definitions`), and `Representation.IsIrreducible` is
  Mathlib's algebraic irreducibility. For `f : SchwartzBruhat G(F_v)`,
  `Character.distribution μ ρ hρ f` is the trace of the finite-rank operator
  `ρ(f) = ∫ f(y) ρ(y) dμ(y)`, and `Langlands.BaseChange.twistedDistribution μ ρ hρ A f` (module
  `Langlands.BaseChange.TwistedCharacter.Basic`) is the trace of `ρ(f) ∘ A`.
- Archimedean representations: a homomorphism `σ : G(F_∞) →* (H →L[ℂ] H)` on a complex Hilbert
  space, with `Langlands.Archimedean.IsContinuousRepresentation` (joint continuity) and
  `Langlands.Archimedean.IsTopologicallyIrreducible`; unitarity is `‖σ g x‖ = ‖x‖`. For a Haar
  measure `μinf` on `G(F_∞)` and a `μinf`-integrable `finf`,
  `σ(finf) = Langlands.Analysis.integratedIsometricAction μinf σ hσnorm hσmeas finf hfinf` is the
  bounded operator `x ↦ ∫ finf(g) • σ(g) x dμinf(g)`.
- `IsTraceClass` and `operatorTrace` are the Library's trace-class predicate and trace
  (`Langlands.Analysis.OperatorIdeals`, `Langlands.Analysis.OperatorTrace`). The compression of
  `X` to a complete subspace `P` is `P.orthogonalProjectionOnto ∘L X ∘L P.subtypeL`.

## Statement

**Hypotheses.** Let the group data be as above, with the Borel, locally compact and totally
disconnected structures of `G(F_v)` at every finite place `v` (instance binders, as in the
multi-place statement). Let `U v : OpenSubgroup G(F_v)` be given at every finite place `v`, with

- (i) every `U v` compact;
- (ii) `IsUniformlyIntegral F G (extendFinite F G (fun v => (U v).toSubgroup))`;
- (iii) for every `g ∈ G(𝔸_F)`, `g_v ∈ U v` for all but finitely many finite places `v`.

Let `μp v` be Haar measures on `G(F_v)` with `μp v (U v) = 1` for all but finitely many `v`, let
`μinf` be a Haar measure on `G(F_∞)` and `ν` a Haar measure on `G(𝔸_F)`. Let `P : Submodule ℂ S`
with `[CompleteSpace P]`, `P ≠ ⊥`, `P` invariant under every `πc a`, and such that every closed
`πc`-invariant subspace `Q ≤ P` is `⊥` or `P`.

**Conclusion.** There exist

- for every finite place `p`, a complex vector space `V p : Type u`, a representation
  `ρ p : Representation ℂ G(F_p) (V p)` and `hρ p : IsAdmissible (ρ p)`;
- a complex Hilbert space `H : Type u`, a homomorphism `σ : G(F_∞) →* (H →L[ℂ] H)`, a proof
  `hσnorm` that every `σ g` preserves the norm and a proof `hσmeas` that every orbit map
  `g ↦ σ g x` is a.e. strongly measurable for `μinf`;
- a finite set `Ebad : Finset (FinitePlace F)`,

such that the following hold.

1. **Irreducibility at the finite places.** Every `ρ p` is irreducible.
2. **Realization at `p`.** For every finite `p` there is a linear map `j₀ : V p →ₗ[ℂ] S` with
   `j₀ ≠ 0`, `LinearMap.range j₀ ≤ P` and `j₀ (ρ p y x) = πc (ofPlace F G (.inr p) y) (j₀ x)`.
3. **Isotypy at `p`.** For every finite `p`, every `V' : Type u`, every smooth irreducible
   representation `ρ'` of `G(F_p)` on `V'` and every linear `j : V' →ₗ[ℂ] S` with `j ≠ 0`,
   `LinearMap.range j ≤ P` and `j (ρ' y x) = πc (ofPlace F G (.inr p) y) (j x)`, there is a linear
   equivalence `E : V' ≃ₗ[ℂ] V p` with `E (ρ' y x) = ρ p y (E x)`.
4. **Continuity at `∞`.** `IsContinuousRepresentation σ`.
5. **Irreducibility at `∞`.** `IsTopologicallyIrreducible σ`.
6. **Realization at `∞`.** There is a linear isometry `jinf : H →ₗᵢ[ℂ] S` with `jinf x ∈ P` for
   all `x` and `jinf (σ g x) = πc (ofInfinite F G g) (jinf x)`.
7. **Isotypy at `∞`.** For every complex Hilbert space `H' : Type u`, every jointly continuous,
   norm-preserving, topologically irreducible `σ' : G(F_∞) →* (H' →L[ℂ] H')` and every bounded
   linear `j : H' →L[ℂ] S` with `j ≠ 0`, `j x ∈ P` for all `x` and
   `j (σ' g x) = πc (ofInfinite F G g) (j x)`, there is a linear isometric equivalence
   `E : H' ≃ₗᵢ[ℂ] H` with `E (σ' g x) = σ g (E x)`.
8. **Fixed lines.** For every finite `p ∉ Ebad`, `μp p (U p) = 1` and
   `Module.finrank ℂ (fixedVectors (ρ p) (U p)) = 1`.
9. **Trace factorization with unit tails.** There is a real number `c > 0` with the following
   property. Let `places : Finset (FinitePlace F)` with `Ebad ⊆ places`, let `finf : G(F_∞) → ℂ`
   be `μinf`-integrable (`hfinf`) with `σf := σ(finf)` trace class, and let
   `fs p : SchwartzBruhat G(F_p)` for `p ∈ places`. Put

   `f g = finf (g_∞) * (∏_{p ∈ places} fs p (g_p)) * 1_{U^places}(g)`, where
   `U^places = {g ∈ G(𝔸_F) | g_v ∈ U v for every finite v ∉ places}`.

   If `f` is `ν`-integrable (`hf`) and the compression `RPf` of `R_S(f)` to `P` is trace class,
   then
   `operatorTrace RPf = c * operatorTrace σf * ∏_{p ∈ places} Character.distribution (μp p) (ρ p) (hρ p) (fs p)`.
10. **Twisted trace factorization with unit tails.** Let `Θ`, `hΘ`, `hΘμ` be as in the notation,
    let `θ v` be topological group automorphisms of `G(F_v)` for all finite places `v`, and
    `θinf` one of `G(F_∞)`, such that, for all `v`, `g` and `x`,
    - `atPlace F G (.inr v) (Θ g) = θ v (atPlace F G (.inr v) g)` and
      `Θ (ofPlace F G (.inr v) x) = ofPlace F G (.inr v) (θ v x)`;
    - `infinite F G (Θ g) = θinf (infinite F G g)` and
      `Θ (ofInfinite F G x) = ofInfinite F G (θinf x)`;
    - `θ v (U v) = U v` for all but finitely many `v` (written `θ v x ∈ U v ↔ x ∈ U v` for all
      `x`).

    If `I_Θ` maps `P` into `P` (for every `x ∈ P` there is `y ∈ P` with `y = I_Θ x` in `L²`),
    then there are
    - bijective linear maps `A p : V p →ₗ[ℂ] V p` with `A p (ρ p y x) = ρ p (θ p y) (A p x)`, for
      every finite `p`;
    - a bijective bounded operator `Ainf : H →L[ℂ] H` with `Ainf (σ g x) = σ (θinf g) (Ainf x)`;
    - a finite set `Ebad'` with `Ebad ⊆ Ebad'` such that, for every finite `p ∉ Ebad'`,
      `θ p (U p) = U p` and `A p x = x` for every `x ∈ fixedVectors (ρ p) (U p)`;
    - a complex number `c' ≠ 0` with the following property. Let `places ⊇ Ebad'`, `finf`,
      `hfinf`, `σf`, `fs` and `f` be as in clause 9, with `σf` trace class and `f`
      `ν`-integrable. Let `BP` be the compression to `P` of the compression to `S` of
      `R(f) ∘ I_Θ`, formed as in part 2 of `GroupSchemeCuspidalLocalTraceFactorizationStatement`.
      If `BP` is trace class, then
      `operatorTrace BP = c' * operatorTrace (σf ∘L Ainf) * ∏_{p ∈ places} BaseChange.twistedDistribution (μp p) (ρ p) (hρ p) (A p) (fs p)`.

The function `f` is the restricted tensor product
`finf ⊗ (⊗_{p ∈ places} fs p) ⊗ (⊗_{v ∉ places} 1_{U v})`: the infinite product of the
indicator functions `1_{U v}(g_v)`, `v ∉ places`, is written as the indicator function of the set
`U^places`.

## How it strengthens the Library statements

- Clauses 1–7 are clauses 1–7 of `GroupSchemeCuspidalMultiPlaceTraceFactorizationStatement`,
  asserted at every finite place at once instead of at the places of one finite set. If both
  statements hold, the local factors they give at a place are isomorphic by either isotypy clause.
- For a test function with unit tails outside `places ⊇ Ebad`, the function
  `fw = 1_{U^places}` is right invariant under `G(F_∞)` and every `G(F_p)`, `p ∈ places`, so
  clause 8 of the multi-place statement writes the trace as
  `tr σ(finf) · ∏_p Θ_{ρ p}(fs p) · C(fw)` with an unknown `C(fw)`. Clause 9 says that for these
  remainders the factor can be taken to be one constant `c > 0`, nonzero and independent of
  `places`. Clause 10 does the same for the twisted part of
  `GroupSchemeCuspidalLocalTraceFactorizationStatement`, at all places of `places` and at `∞`
  simultaneously, with the twisted archimedean character `operatorTrace (σ(finf) ∘ Ainf)`.
- The present statement says nothing about remainders `fw` that are not unit tails. So neither
  statement implies the other; they share the realization and isotypy clauses.

## Remarks on the formalization

- **The integrality hypotheses.** Fix generators `a_1, …, a_n` of the coordinate ring of `G`
  and let `G(𝒪_v)` be the set of points of `G(F_v)` at which all `a_i` are integral. Hypothesis
  (ii) says that `U v ⊆ G(𝒪_v)` for almost all `v`, and (iii) gives `G(𝒪_v) ⊆ U v` for almost
  all `v` (step 1 below), so together they give `U v = G(𝒪_v)` for almost all `v`.
  Hypothesis (ii) alone does not suffice: for `G = GL_2` it holds with `U v` the principal
  congruence subgroup of level `v` at every finite place. For a cuspidal `P` the local component
  at almost every `v` is an unramified principal series, whose space of fixed vectors under
  that subgroup has dimension `q_v + 1` (the functions on `ℙ¹(𝔽_{q_v})`). Clause 8 then fails at
  infinitely many places, and so does the identity of clause 9, since the operator of
  `1_{U v}` on that component has trace `q_v + 1`. At finitely many places `U v` is only
  required to be a compact open subgroup, and `μp v (U v)` is arbitrary.
- **`Ebad`.** `Ebad` depends on `P`. In the proof it consists of the places where `U v` is not a
  hyperspecial `G(𝒪_v)`, where `μp v (U v) ≠ 1`, and where the local component of `P` has no
  nonzero `U v`-fixed vector. For each finite `v ∉ Ebad`, clause 8 gives volume `1` and a
  one-dimensional fixed space, so the operator of `1_{U v}` has trace `1` on the local
  component. Both trace formulas require `Ebad ⊆ places`, so this applies at every finite
  place outside `places`.
- **The constant `c`.** In the proof, `c` is the ratio of `ν` to the product measure
  `μinf × ⊗'_v μp v` (step 1), so `c > 0`; it does not depend on `places` or on the test
  functions. The statement places `c` after `P` and does not assert that it is the same for
  all `P`. With `c = 0` clause 9 would only say that the traces vanish; the nonvanishing of `c`
  is what applications of the clause use.
- **The constant `c'`.** In the proof `c' = c · λ`, where `λ` is the scalar by which `I_Θ`
  restricted to `P` differs from the tensor product of the normalized local intertwiners
  (step 5); `λ ≠ 0`, and `|λ| = 1` when the local intertwiners are chosen unitary. Since `Ainf`
  may be rescaled, `c'` could be absorbed into `Ainf`; it is kept so that the normalization of
  the intertwiners and the global constant stay separate.
- **The twisted hypotheses.** The hypotheses on `Θ` are those of part 2 of
  `GroupSchemeCuspidalLocalTraceFactorizationStatement`, at every finite place and at `∞`. Since a
  point of `G(𝔸_F)` is determined by its local components, `Θ` is determined by the `θ v` and
  `θinf`; the insertion equations follow from the component equations and are stated for
  symmetry with the local statement. The condition `θ v (U v) = U v` for almost all `v` makes
  `Θ` compatible with the restricted product structure; it holds, for example, when `Θ` comes
  from an automorphism of an integral model of `G` over a ring of `S`-integers, such as a Galois
  automorphism of a Weil restriction.
- **The intertwiners.** `A p` intertwines `ρ p` with `ρ p ∘ θ p`, the direction forced by
  `I_Θ R(g) = R(Θ g) I_Θ`, and agrees with part 2 of the local statement. For `p ∉ Ebad'`,
  `A p` preserves the `U p`-fixed line because `θ p (U p) = U p`, and clause 10 normalizes it to
  be the identity there. Then the twisted local factor of `1_{U p}` is
  `μp p (U p) · tr (A p on the fixed line) = 1`, matching the unit tail. A bijective bounded
  operator on a Hilbert space has a bounded inverse (open mapping theorem), and
  `σf ∘L Ainf` is trace class when `σf` is, since trace-class operators form an ideal.
- **The archimedean test functions.** These are as in the multi-place statement: all
  `μinf`-integrable `finf` with `σ(finf)` trace class. This class contains every smooth
  compactly supported function on `G(F_∞)` (Harish-Chandra; the Markdown of the multi-place
  statement gives the argument and the page references). The Lean statement keeps
  "`σ(finf)` is trace class" as a hypothesis.
- **Compressions.** `P` is closed and invariant, so `R_S(f)` maps `P` into `P` and `RPf` is the
  restriction of `R_S(f)` to `P`. In the twisted case `I_Θ` maps `P` into `P ⊆ S` and `R(f)`
  preserves `S` and `P`, so `BP` is the restriction of `R(f) ∘ I_Θ` to `P`. For `f` as in
  clause 9, `f` is `ν`-integrable and `RPf` and `BP` are trace class whenever `finf` is
  integrable and `σ(finf)` is trace class (steps 4 and 5); the statement keeps both as
  hypotheses, as the Library's factorization statements do.
- **Instance binders and names.** The binders `[∀ v, MeasurableSpace G(F_v)]`, `[∀ v, BorelSpace …]`,
  `[∀ v, LocallyCompactSpace …]` and `[∀ v, TotallyDisconnectedSpace …]` range over all finite
  places, as in the multi-place statement, whose Markdown explains why they are true. As there,
  the Haar measures at the finite places are called `μp` and the finite set of places is called
  `places` in Lean.
- **`hσnorm`, `hσmeas`.** These are conclusions, needed as arguments of
  `integratedIsometricAction`, as in the multi-place statement.
- **Universes.** `V p`, `V'`, `H` and `H'` range over `Type u`, the universe of `F`.

## Why the statement is true

1. **Integral structure and measures.** Let `G(𝒪_v)` be as in the remarks. Suppose that
   `G(𝒪_v) ⊄ U v` for infinitely many `v`. Choose `k_v ∈ G(𝒪_v) \ U v` at these places and
   `k_v = 1` elsewhere. Every regular function is a polynomial in the `a_i` with coefficients in
   `F`, integral at almost all places, so this family has integral values at almost all places
   and glues to a point `g ∈ G(𝔸_F)` with `g_v = k_v` (the Library's `AdelicGroupPoints.glue`),
   contradicting (iii). With (ii), `U v = G(𝒪_v)` for almost all `v`. After inverting finitely
   many primes the `a_i` define a model of `G`, so `U v` is hyperspecial for almost all `v`
   (Getz–Hahn, Proposition 2.4.8), and `G(𝔸_F^∞)` is the restricted product of the `G(F_v)` with
   respect to the `U v` (Getz–Hahn, Proposition 2.4.10). Since `μp v (U v) = 1` for almost all
   `v`, the restricted product measure `⊗'_v μp v` is defined (Getz–Hahn, §5.6), and
   `ν = c · (μinf × ⊗'_v μp v)` for some `c > 0` by uniqueness of Haar measure.
2. **Restricted tensor product decomposition.** The right action on `P` is an irreducible unitary
   representation of `G(𝔸_F)`. The groups `G(F_∞)` and `G(F_v)` are of type I (Getz–Hahn,
   Theorem 3.10.2), so `P ≅ H_∞ ⊗̂ H^∞` with irreducible unitary factors (Folland,
   Theorem 7.17), and `P` is a Hilbert restricted tensor product
   `H_∞ ⊗̂ ⊗̂'_v H_v` of irreducible unitary representations `π_v`, with respect to unit vectors
   `ξ_v ∈ H_v^{U v}` for `v` outside a finite set (Flath, Theorem 4). On smooth vectors this is
   Flath's algebraic factorization (Flath, Theorems 2–3; Getz–Hahn, Theorems 5.7.1–5.7.2), in
   which the spherical Hecke algebras are commutative for almost all `v` and the fixed lines
   are one-dimensional (Getz–Hahn, Theorem 5.5.2 and Corollary 5.5.6). Take `σ = π_∞` and
   `ρ p` the smooth part of `π_p`; it is irreducible and admissible (Getz–Hahn, Proposition 5.3.8
   and Theorem 5.3.9). Let `Ebad` be the finite set of places of step 1 where `U v` is not a
   hyperspecial `G(𝒪_v)`, together with the places where `μp v (U v) ≠ 1` or where no `ξ_v` is
   chosen. Outside `Ebad` the `U v`-fixed vectors of `π_v`, which are smooth, form the line
   `ℂ ξ_v`. This gives clause 8.
3. **Realization and isotypy.** These are steps 3–5 of the Markdown of
   `GroupSchemeCuspidalMultiPlaceTraceFactorizationStatement`, applied at every place: with
   `P ≅ H_p ⊗̂ H'_p`, the maps `x ↦ x ⊗ η` give the realizations, Flath's observation that the
   restriction of `W_1 ⊗ W_2` to the first factor is `W_1`-isotypic (Flath, Theorem 1, end of the
   proof) gives isotypy at `p`, and Schur's lemma (Folland, Theorem 3.5) gives isotypy at `∞`.
4. **Untwisted trace.** Let `places ⊇ Ebad`. By steps 1 and 2, `R_S(f)` restricted to `P`
   corresponds to
   `c · σ(finf) ⊗ ⊗_{p ∈ places} π_p(fs p) ⊗ ⊗_{v ∉ places} π_v(1_{U v})`. For `v ∉ places`,
   `v ∉ Ebad`, so `π_v(1_{U v}) = μp v (U v) · e_v` is the orthogonal projection `e_v` onto
   `ℂ ξ_v`, and the tail is the rank-one projection onto `⊗_{v ∉ places} ξ_v`, of trace `1`. Each
   `π_p(fs p)` has finite rank with range in the smooth vectors, and its trace is
   `Character.distribution (μp p) (ρ p) (hρ p) (fs p)`. The trace of a tensor product of a
   trace-class operator with finite-rank operators is the product of the traces; this gives
   clause 9.
5. **Twisted trace.** Since `I_Θ` is unitary and `I_Θ R(g) = R(Θ g) I_Θ`, the image `I_Θ(P)` is a
   closed nonzero invariant subspace of `P`, hence `P`, and `I_Θ` restricted to `P` is a unitary
   intertwiner from `π_P` to `π_P ∘ Θ`. By the component equations, `π_P ∘ Θ` is the restricted
   tensor product of the `π_v ∘ θ_v` and `π_∞ ∘ θinf`, with respect to the same vectors `ξ_v` at
   the places where `θ v (U v) = U v`. By uniqueness of the factors (Flath, Theorem 4),
   `π_v ∘ θ_v ≅ π_v` and `π_∞ ∘ θinf ≅ π_∞`; choose unitary intertwiners `B_v` and `B_∞`. Let
   `Ebad'` be `Ebad` together with the finitely many `v` with `θ v (U v) ≠ U v`. For `v ∉ Ebad'`,
   `B_v` preserves the line `ℂ ξ_v`, and after multiplication by a unit scalar `B_v ξ_v = ξ_v`.
   Then the restricted tensor product `⊗_v B_v` is defined (Flath, §2 (1); Getz–Hahn, §5.6), and
   `(B_∞ ⊗ ⊗_v B_v)⁻¹ ∘ I_Θ|_P` commutes with `π_P`, so it is a scalar `λ ≠ 0` (Schur's lemma).
   Take `A p` the restriction of `B_p` to the smooth vectors (it preserves them, since `θ p` maps
   compact open subgroups to compact open subgroups) and `Ainf = B_∞`. Then `BP` corresponds to
   `c λ · (σ(finf) B_∞) ⊗ ⊗_{p ∈ places} (π_p(fs p) B_p) ⊗ ⊗_{v ∉ places} (e_v B_v)`. For
   `v ∉ places`, `B_v` is unitary with `B_v ξ_v = ξ_v`, so `B_v* ξ_v = ξ_v` and `e_v B_v = e_v`;
   the tail again has trace `1`. The trace of `π_p(fs p) B_p` equals the trace of its restriction
   to the smooth vectors, `twistedDistribution (μp p) (ρ p) (hρ p) (A p) (fs p)`. Multiplying the
   traces gives clause 10 with `c' = c λ`.

Step 5 is the argument of Henniart–Lemaire II.6.4 (printed p. 120) and Arthur–Clozel, Chapter 1,
§6.3 (printed p. 56), where the global operator `I_σ` on a `σ`-stable cuspidal representation is
a tensor product of local intertwiners. Henniart–Lemaire normalize the local intertwiners to be
the identity on the `K_{E_v}`-fixed vectors at almost all places, as clause 10 does, so that the
twisted trace of a test function with unit tails is a product of local twisted traces at
finitely many places (II.6.10, printed p. 126); Arthur–Clozel normalize them by Whittaker
functionals.

## Use and provenance

This is derived content, formulated for the Library. It packages Flath's restricted tensor
product decomposition of an irreducible unitary representation of `G(𝔸_F)`, the normalization of
the global twisting operator as a tensor product of local intertwiners fixing the spherical
vectors, and the multiplicativity of traces of tensor products, for an irreducible summand of the
cuspidal space of the positive rational quotient. The following are derived and not in the
sources in this form:

- the factorization is asserted only for test functions with unit tails outside a finite set
  containing `Ebad` (`Ebad'` in the twisted case), with the indicator function of `U^places`;
- `c` is the comparison constant between `ν` and `μinf × ⊗'_v μp v`, and `c'` is `c` times the
  scalar relating `I_Θ` to the tensor product of the normalized local intertwiners;
- the integrality of the family `U` is given by hypotheses (ii) and (iii) instead of a model of
  `G`;
- the finite-place factors are realized on smooth vectors with linear maps into `P`, the
  archimedean factor on a Hilbert space, and the archimedean test functions are all integrable
  functions with trace-class `σ(finf)`;
- the trace class of the compressions is a hypothesis.

Sources:

- D. Flath, *Decomposition of representations into tensor products*, Proc. Sympos. Pure Math.
  33, part 1 (1979), registered `flath-1979-tensor-products` (the registered file is the
  Corvallis Part I volume, PDF pp. 175–179).
  - Theorem 1 (printed p. 179) and the last sentence of its proof (printed p. 180): isotypy.
  - §2 (1), printed p. 181: maps `B_v : W_v → W_v` with `B_v x_v = x_v` for almost all `v`
    define `B = ⊗ B_v` on the restricted tensor product. Theorem 2 (printed p. 181): for a
    restricted product with commutative `H(G_v, K_v)` for almost all `v`, every admissible
    irreducible representation is factorizable, with factors determined up to isomorphism and
    `dim W_v^{K_v} = 1` for almost all `v`. Theorem 3 (printed p. 181): the same for `G(𝔸)`.
  - Theorem 4 (printed p. 182): a continuous irreducible unitary representation of `G(𝔸)` is a
    Hilbert restricted tensor product of irreducible unitary representations, almost all
    unramified, with factors unique up to isomorphism.
- J. R. Getz and H. Hahn, *An introduction to automorphic representations, with a view toward
  trace formulae*, GTM 300 (2024), registered `getz-hahn-2024-automorphic-representations`.
  - Proposition 2.4.8 and Proposition 2.4.10 (printed p. 61, PDF p. 78): hyperspecial integral
    points at almost all places, and the adelic points as a restricted product.
  - Theorem 3.10.2 (printed p. 97, PDF p. 113): points of affine algebraic groups over
    characteristic-zero local fields form type I groups.
  - Proposition 5.3.8 and Theorem 5.3.9 (printed p. 141, PDF p. 156): a unitary representation
    is irreducible if and only if its smooth vectors are, and irreducible unitary
    representations are admissible.
  - Theorem 5.5.2 (printed p. 147, PDF p. 162) and Corollary 5.5.6 (printed p. 148, PDF p. 163):
    the unramified Hecke algebra is commutative, and the fixed line of an irreducible admissible
    unramified representation is one-dimensional.
  - §5.6 (printed pp. 149–151, PDF pp. 164–166): restricted tensor products, the tensor product
    `⊗_v B_v` of maps fixing the chosen vectors (printed p. 149), and the restricted product
    Haar measure and idempotents (5.12)–(5.14) (printed pp. 150–151).
  - Theorem 5.7.1 (Flath) and Theorem 5.7.2 (printed pp. 152–153, PDF pp. 167–168).
- G. B. Folland, *A course in abstract harmonic analysis*, 2nd ed. (2015), registered
  `folland-2015-abstract-harmonic-analysis-second`: Theorem 3.5, Schur's lemma (printed p. 77,
  PDF p. 90); Theorem 7.17 (printed p. 237, PDF p. 250), irreducible representations of a
  product with a type I factor are outer tensor products.
- J. Arthur and L. Clozel, *Simple algebras, base change, and the advanced theory of the trace
  formula*, Annals of Math. Studies 120 (1989), registered `arthur-clozel-1989-base-change`
  (PDF page = printed page + 14). Chapter 1, §6.3, printed pp. 54–57: in the proof of
  Theorem 6.2 the global intertwining operator `I_σ` of a `σ`-stable cuspidal `Π` is written as
  a tensor product `⊗_v I_{σ,v}` of normalized local intertwining operators (printed p. 56), and
  the comparison of traces gives an identity between a local character and a constant times a
  local twisted trace (printed p. 57).
- G. Henniart and B. Lemaire, *Changement de base et induction automorphe pour GL_n en
  caractéristique non nulle*, Mém. SMF 124 (2011), registered
  `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61` (PDF page =
  printed page + 8).
  - II.6.4 (printed p. 120): for a `σ`-stable cuspidal `Π ≅ ⊗̂_v Π̂_v`, the operator induced by
    `I_σ` is a tensor product of local isomorphisms `A_{Π_v}`, which is the identity on the
    `K_{E_v}`-fixed vectors at almost all places, and
    `tr(Π(φ) ∘ A_Π) = ∏_v tr(Π_v(φ_v) ∘ A_{Π_v})`.
  - II.6.10 (printed pp. 125–126): with test functions bi-invariant under `K_{E_v}` outside a
    finite set `S`, `tr(Π_v(φ_v) ∘ A_{Π_v}) = tr(Π_v(φ_v))` for `v ∉ S`, and the global twisted
    trace is a product over `S` times a remaining factor.
  - II.6.13 (printed pp. 129–130): the resulting comparison at a single place, with a constant
    `c` shown to be nonzero (printed p. 130).

## Intended use

In a comparison of a simple trace formula with its twisted form on the cuspidal spectrum of the
positive rational quotient, the spectral sides are sums over irreducible summands `P`. After the
summands are separated by their Hecke eigencharacters outside a finite set, clauses 9 and 10 write
the trace of each surviving summand as a nonzero constant times a product of local characters,
respectively twisted characters, at the remaining finite places and at `∞`. The nonvanishing of
the constants is what lets a comparison of global traces be reduced to an identity of local
characters at one place. The isotypy clauses identify the local factors with local components
obtained by other means, for instance by the Library's
`GeneralLinearCuspidalLocalComponentTraceStatement` and
`WeilGeneralLinearCuspidalLocalTwistedTraceStatement`.
