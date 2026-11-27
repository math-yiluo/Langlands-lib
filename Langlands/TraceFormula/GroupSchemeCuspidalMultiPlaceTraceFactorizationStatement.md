# Trace factorization over a finite set of finite places and the archimedean component on an irreducible cuspidal summand (statement)

Module `Langlands.TraceFormula.GroupSchemeCuspidalMultiPlaceTraceFactorizationStatement` contains
one proposition definition and no proof:

- `Langlands.TraceFormula.GroupSchemeCuspidalMultiPlaceTraceFactorizationStatement.{u}`.

It uses the data, model and notation of the Library statement
`Langlands.TraceFormula.GroupSchemeCuspidalIsotypicTraceFactorizationStatement` (module of the
same name). That statement splits one finite place `v` off the traces on an irreducible closed
invariant subspace `P` of the group-scheme cuspidal space: it gives an irreducible admissible
representation `ρ_v` of `G(F_v)` that occurs in `P`, makes `P` `ρ_v`-isotypic, and whose
character splits off the traces of test functions `f_v ⊗ f^v`. The present statement splits off
a finite set `Σ` of finite places (the Lean variable `places`) and the archimedean component
at the same time. It gives a local factor at each `p ∈ Σ` and at `∞`, each realized in `P` and
determined by `P` up to isomorphism. It also gives one functional `C` of the remaining places such
that the trace of every product test function on `P` is the product of the local characters and
`C`.

## Setting and notation from the Library

The group data, `S`, `πc` and the integrated action are those of
`GroupSchemeCuspidalIsotypicTraceFactorizationStatement` and of
`GroupSchemeCuspidalLocalTraceFactorizationStatement`, whose Markdown explains them in full. In
brief:

- `F : Type u` is a number field and `G` an affine group scheme over `Spec F`, locally of finite
  type, with `hPD : ParabolicDynamicStatement.{u}`, `hG : IsConnectedReductive G`, a central map
  `i : T.toGrp ⟶ G` from a commutative group scheme `T` with injective character restriction
  `hi` of finite-index range, an isomorphism `e` of `T` with a split torus indexed by a finite
  type `I`, `hc : IsCentral i`, and right invariance of Haar measure on `normOneSubgroup F G`.
- `G(𝔸_F) = AdelicGroupPoints F G`. `S := fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc` is
  the closed cuspidal subspace of `L²` of the quotient of `G(𝔸_F)` by
  `positiveRationalSubgroup F G T i`. `πc a := fullAEL2CuspidalBoundedRightAction … a` is right
  translation by `a ∈ G(𝔸_F)` on `S`. `fullAEL2CuspidalIntegratedAction … ν f hf` (written
  `R_S(f)`) is the integrated action on `S` of a `ν`-integrable `f`.
- Finite places: `Langlands.Global.FinitePlace F`. For a finite place `v`,
  `G(F_v) = PlaceGroupPoints F G (.inr v)`, `atPlace F G (.inr v) g = g_v` is the local component
  and `ofPlace F G (.inr v)` inserts a point at `v` (identity elsewhere).
- The archimedean group: `G(F_∞) = G(F ⊗ ℝ) = InfiniteAdelicGroupPoints F G`, the points over the
  Library's `InfiniteAdeleRing F`, with its topology, its Borel σ-algebra
  (`InfiniteAdelicGroupPoints.measurableSpace`, module `Langlands.Global.InfiniteAdelicModularCharacter`)
  and its group structure. `AdelicGroupPoints.infinite F G g = g_∞` is the archimedean component
  and `AdelicGroupPoints.ofInfinite F G` inserts an archimedean point with finite component `1`
  (module `Langlands.Global.AdelicGroupProduct`).
- Finite-place representations: `Langlands.IsSmooth`, `Langlands.IsAdmissible` (module
  `Langlands.Representation.Smooth.Definitions`), Mathlib's algebraic
  `Representation.IsIrreducible`, and the distribution character
  `Character.distribution μ ρ hρ f`, the trace of the finite-rank operator
  `ρ(f) = ∫ f(y) ρ(y) dμ(y)` for `f : SchwartzBruhat G(F_v)`.
- Archimedean representations: a representation of `G(F_∞)` on a complex Hilbert space `H` is a
  group homomorphism `σ : G(F_∞) →* (H →L[ℂ] H)`. `Langlands.Archimedean.IsContinuousRepresentation σ`
  says that `(g, x) ↦ σ g x` is jointly continuous, and
  `Langlands.Archimedean.IsTopologicallyIrreducible σ` says that `H ≠ 0` and that `0` and `H` are
  the only closed `σ`-invariant subspaces (both in `Langlands.Representation.Archimedean.SmoothVectors`).
  Unitarity is the condition `‖σ g x‖ = ‖x‖`. Each `σ g` is invertible with inverse `σ g⁻¹`, so a
  norm-preserving `σ g` is unitary.
- The archimedean operator: for a Haar measure `μinf` on `G(F_∞)` and a `μinf`-integrable
  `finf`, `σ(finf) := Langlands.Analysis.integratedIsometricAction μinf σ hσnorm hσmeas finf hfinf`
  (module `Langlands.Representation.Unitary.IntegratedOperator`). It is the bounded operator
  `x ↦ ∫ finf(g) • σ(g) x dμinf(g)` (Bochner integral). Its arguments are the norm preservation
  `hσnorm`, the a.e. strong measurability `hσmeas` of the orbit maps `g ↦ σ g x`, and the
  integrability `hfinf`.
- `IsTraceClass` and `operatorTrace` are the Library's trace-class predicate and trace
  (`Langlands.Analysis.OperatorIdeals`). The compression of `X` to a complete subspace `P` is
  `P.orthogonalProjectionOnto ∘L X ∘L P.subtypeL`.

## Statement

For all group data as above, every finite set `places : Finset (FinitePlace F)`, every Haar
measure `μp p` on `G(F_p)` for `p ∈ places`, every Haar measure `μinf` on `G(F_∞)` and every Haar
measure `ν` on `G(𝔸_F)`, let `P : Submodule ℂ S` with `[CompleteSpace P]`, `P ≠ ⊥`, `P`
invariant under every `πc a`, and such that every closed subspace `Q ≤ P` invariant under every
`πc a` is `⊥` or `P`. The statement takes the Borel, locally compact and totally disconnected
structure of `G(F_v)` as instance binders for every finite place `v`, as the one-place statement
does at its place `v`. Then there exist:

- for each `p ∈ places`, a complex vector space `V p : Type u` with a representation
  `ρ p : Representation ℂ G(F_p) (V p)` and `hρ p : IsAdmissible (ρ p)`;
- a complex Hilbert space `H : Type u` with a homomorphism
  `σ : G(F_∞) →* (H →L[ℂ] H)`, a proof `hσnorm` that every `σ g` preserves the norm, and a proof
  `hσmeas` that every orbit map `g ↦ σ g x` is a.e. strongly measurable for `μinf`,

such that the following hold.

1. **Irreducibility at the finite places.** Every `ρ p` is irreducible.
2. **Realization at `p ∈ places`.** There is a linear map `j₀ : V p →ₗ[ℂ] S` with `j₀ ≠ 0`,
   `LinearMap.range j₀ ≤ P` and `j₀ (ρ p y x) = πc (ofPlace F G (.inr p) y) (j₀ x)`.
3. **Isotypy at `p ∈ places`.** For every `V' : Type u`, every representation `ρ'` of `G(F_p)`
   on `V'` with `IsSmooth ρ'` and `ρ'.IsIrreducible`, and every linear `j : V' →ₗ[ℂ] S` with
   `j ≠ 0`, `LinearMap.range j ≤ P` and `j (ρ' y x) = πc (ofPlace F G (.inr p) y) (j x)`, there is
   a linear equivalence `E : V' ≃ₗ[ℂ] V p` with `E (ρ' y x) = ρ p y (E x)`.
4. **Continuity at `∞`.** `IsContinuousRepresentation σ`.
5. **Irreducibility at `∞`.** `IsTopologicallyIrreducible σ`.
6. **Realization at `∞`.** There is a linear isometry `jinf : H →ₗᵢ[ℂ] S` with `jinf x ∈ P` for
   all `x` and `jinf (σ g x) = πc (ofInfinite F G g) (jinf x)`.
7. **Isotypy at `∞`.** For every complex Hilbert space `H' : Type u`, every
   `σ' : G(F_∞) →* (H' →L[ℂ] H')` that is jointly continuous, norm-preserving and topologically
   irreducible, and every bounded linear `j : H' →L[ℂ] S` with `j ≠ 0`, `j x ∈ P` for all `x` and
   `j (σ' g x) = πc (ofInfinite F G g) (j x)`, there is a linear isometric equivalence
   `E : H' ≃ₗᵢ[ℂ] H` with `E (σ' g x) = σ g (E x)`: `σ'` is unitarily equivalent to `σ`.
8. **Trace factorization.** There is one functional `C : (G(𝔸_F) → ℂ) → ℂ` with the following
   property. Let `finf : G(F_∞) → ℂ` be `μinf`-integrable (`hfinf`) with
   `σf := σ(finf)` trace class. Let `fs p : SchwartzBruhat G(F_p)` for `p ∈ places`, and let
   `fw : G(𝔸_F) → ℂ` satisfy `fw (g * ofInfinite F G y) = fw g` and
   `fw (g * ofPlace F G (.inr p) x) = fw g` for all `p ∈ places`. If
   `f g = finf (g_∞) * (∏_{p ∈ places} fs p (g_p)) * fw g` is `ν`-integrable (`hf`) and the
   compression `RPf` of `R_S(f)` to `P` is trace class, then
   `operatorTrace RPf = operatorTrace σf * (∏_{p ∈ places} Character.distribution (μp p) (ρ p) (hρ p) (fs p)) * C fw`.

### The archimedean test functions and character

The archimedean test-function class of clause 8 is the set of all `μinf`-integrable functions
`finf` on `G(F_∞)` for which `σ(finf)` is trace class. The archimedean character is
`Θ_σ(finf) = operatorTrace σ(finf) = tr σ(finf)`. This class contains every smooth compactly
supported function on `G(F_∞)`:

- such a function is continuous with compact support, hence integrable for every Haar measure;
- `σ(finf)` is then trace class, by Harish-Chandra's admissibility theorem and the trace-class
  lemma for Wallach's space `𝒮(G)` (step 7 of "Why the statement is true").

So clause 8 applies to every compactly supported archimedean test function that is smooth for
some smooth structure on `G(F_∞)` with the given topology, whenever `σ(finf)` is trace class.
Examples are the smooth compactly supported functions for the Library's atlas
`Langlands.Global.InfiniteAdelicGroupPoints.reductiveChartedSpace F G hG`. When `G(F_∞)` is
identified with `GL_n(F' ⊗ ℝ) = InfiniteAdelicGL F' n` by a topological group isomorphism `Φ`,
the functions `κ ∘ Φ` for `κ : ArchimedeanGL.SmoothCompactKernel F' n` are further examples. For
the Lie group structure of `G(F_∞)`, the trace-class condition holds automatically, by
Harish-Chandra. No manifold structure or chart enters the Lean statement, so the statement is
made for every `G`, and no identification with `GL_n` is assumed. The Lean statement keeps
"`σ(finf)` is trace class" as a hypothesis; it does not assert Harish-Chandra's theorem.

### Remarks on the formalization

- **What is reused.** The hypotheses on `F, G, P` and the finite-place clauses 1–3 are those of
  `GroupSchemeCuspidalIsotypicTraceFactorizationStatement`, with `p ∈ places` in place of `v`.
  The compression `RPf` is formed exactly as in part 1 there. Clauses 2–3 for `places = {v}` are
  clauses 0 and 0' of that statement. If both statements hold, the two local factors at `v` are
  isomorphic by either isotypy clause.
- **Quantifiers.** `C` does not depend on `finf` or on the `fs p`. The local factors do not
  depend on any test function.
- **Instance binders at every finite place.** The binders
  `[∀ v, MeasurableSpace (PlaceGroupPoints F G (.inr v))]`, `[∀ v, BorelSpace …]`,
  `[∀ v, LocallyCompactSpace …]` and `[∀ v, TotallyDisconnectedSpace …]` range over all finite
  places, not only over `places`. Lean's type class resolution cannot use an instance family
  indexed by the elements of a `Finset`, because the index is not determined by the type
  `PlaceGroupPoints F G (.inr v)`. The binders are true at every finite place: the points of an
  affine group of finite type over a non-archimedean local field form a locally compact, totally
  disconnected group, and `BorelSpace` fixes the σ-algebra to be the Borel one.
- **`hσnorm` and `hσmeas`.** These are conclusions, needed as arguments of
  `integratedIsometricAction`. Measurability of the orbit maps follows from clause 4, because
  `G(F_∞)` is second countable (`InfiniteAdelicGroupPoints.secondCountableTopology`, module
  `Langlands.Global.AdelicGroupPolish`).
- **Isotypy at `∞` for bounded maps.** In clause 7 the map `j` is only bounded, not isometric.
  Clause 7 compares `σ` with representations in the same class as `σ` (jointly continuous,
  unitary, topologically irreducible) and gives unitary equivalence.
- **Universes.** `V p`, `V'`, `H` and `H'` range over `Type u`, the universe of `F`.

## Why the statement is true

The argument is the one in the Markdown of `GroupSchemeCuspidalIsotypicTraceFactorizationStatement`
and `GroupSchemeCuspidalLocalTraceFactorizationStatement`, applied to several factors at once,
plus Schur's lemma at `∞`.

1. **Product decomposition.** Write `Σ = places`. Multiplication of the inserted points is an
   isomorphism of topological groups
   `G(F_∞) × ∏_{p ∈ Σ} G(F_p) × G(𝔸_F^{Σ,∞}) ≅ G(𝔸_F)`. Here `G(𝔸_F^{Σ,∞})` is the subgroup of
   points with trivial components at `∞` and at `Σ`, and the inserted factors commute. Hence
   `ν = c · (μinf × ∏_p μp p × ν')` for a fixed Haar measure `ν'` on `G(𝔸_F^{Σ,∞})` and some
   `c > 0`. The invariance of `fw` means that `fw` depends only on the component in
   `G(𝔸_F^{Σ,∞})`; write `fw'` for its restriction to that group. Under the isomorphism, `f`
   becomes `(x, y, z) ↦ k(x, y) · fw'(z)` with `k(x, y) = finf(x) · ∏_{p ∈ Σ} fs p (y_p)`. There
   are two cases.
   - (a) `finf = 0` `μinf`-almost everywhere, or `fs p = 0` `μp p`-almost everywhere for some
     `p ∈ Σ`. Then `f = 0` `ν`-almost everywhere.
   - (b) Otherwise `k ≠ 0` on a set of positive `μinf × ∏_p μp p`-measure. Suppose `f` is
     `ν`-integrable. By Fubini's theorem, for almost every `(x, y)` the slice
     `z ↦ k(x, y) · fw'(z)` is `ν'`-integrable. Choose such an `(x, y)` with `k(x, y) ≠ 0` and
     divide by `k(x, y)`: `fw'` is `ν'`-integrable.

   Nonvanishing almost everywhere, not pointwise, is what case (b) needs. For `G = G_m` over `ℚ`,
   `Σ = ∅`, `finf` the indicator function of `{1}` in `ℝ^×` and `fw = 1`, the function `f` is `0`
   almost everywhere, hence integrable. But `fw'` is a nonzero constant on the finite idèles,
   a group of infinite Haar measure, so it is not integrable.
2. **Tensor decomposition.** The right action on `P` is an irreducible unitary representation of
   `G(𝔸_F)`, by the closed-subspace hypothesis. `G(F_∞) = (Res_{F/ℚ} G)(ℝ)` and each `G(F_p)`
   are the points of affine algebraic groups over characteristic-zero local fields, so they are
   of type I (Getz–Hahn, Theorem 3.10.2). Folland's Theorem 7.17, applied once for each factor,
   gives a unitary isomorphism `P ≅ H_∞ ⊗̂ ⊗̂_{p ∈ Σ} H_p ⊗̂ H'`. This isomorphism carries the
   action of the inserted factors to `σ_∞ ⊗ ⊗_p π_p ⊗ π'`, with irreducible unitary
   representations `σ_∞` of `G(F_∞)`, `π_p` of `G(F_p)` and `π'` of `G(𝔸_F^{Σ,∞})`. Take
   `σ = σ_∞`. For each `p`, take `ρ p` to be the representation on the smooth vectors of `π_p`.
   It is irreducible and admissible (Getz–Hahn, Proposition 5.3.8 and Theorem 5.3.9).
3. **Realization.** With unit vectors in the other factors, `x ↦ x ⊗ ξ` gives the maps of
   clauses 2 and 6. The archimedean one is isometric.
4. **Isotypy at `p`.** This is step 3 of the one-place argument, with `H_p` as first factor and
   the completed tensor product of the other factors as second factor.
5. **Isotypy at `∞`.** Let `j` be as in clause 7. Its kernel is a closed `σ'`-invariant subspace
   different from `H'`, hence `0`. Contracting `U ∘ j` with a suitable vector of the other factors
   gives a nonzero bounded intertwiner `A : H' → H_∞` from `σ'` to `σ`. Then `A*A` commutes with
   `σ'`, so `A*A = c I` with `c > 0` (Schur's lemma, Folland, Theorem 3.5). Then `c^{-1/2} A` is an
   isometric intertwiner, and its range is closed, invariant and nonzero, hence all of `H_∞`.
6. **Trace.** Define `C fw = c · tr π'(fw')` when `fw'` is `ν'`-integrable and `π'(fw')` is
   trace class, and `C fw = 0` otherwise. It depends neither on `finf` nor on the `fs p`. Each
   `π_p(fs p)` has finite rank, its range lies in the smooth vectors, and its trace is
   `Character.distribution (μp p) (ρ p) (hρ p) (fs p)`. Suppose that `f` is `ν`-integrable and
   that `σ(finf)` and the compression of `R_S(f)` to `P` are trace class.
   - In case (a) of step 1, `R_S(f) = 0`, so the left side of clause 8 is `0`. The integrated
     operator of the almost-everywhere zero local function is `0`: either `σ(finf) = 0`, or
     `π_p(fs p) = 0` and its character is `0`. So the right side is `0` too.
   - In case (b), `fw'` is `ν'`-integrable, and by step 1 the compression corresponds to
     `c · σ(finf) ⊗ ⊗_p π_p(fs p) ⊗ π'(fw')`. If `σ(finf) = 0` or some `π_p(fs p) = 0`, both
     sides are `0`. Otherwise choose a nonzero matrix coefficient of `σ(finf)` and of each
     `π_p(fs p)`. Multiplying the compression on both sides by operators that are rank one in the
     factors at `∞` and at `Σ` and the identity in the last factor gives a nonzero rank-one
     operator tensored with `π'(fw')`. This product is trace class, because trace-class operators
     form a two-sided ideal, so `π'(fw')` is trace class. The trace of a tensor product of
     trace-class operators is the product of the traces, which gives clause 8.
7. **Smooth archimedean test functions.** `G(F_∞)` is the group of real points of the connected
   reductive `ℝ`-group `Res_{F/ℚ} G`. Through a faithful representation with self-adjoint image
   it is a real reductive group in the sense of Wallach, §2.1.1 (printed p. 42). An irreducible
   unitary representation of such a group is admissible (Harish-Chandra; Wallach,
   Theorem 3.4.10). Its `(𝔤, K)`-module is irreducible (Wallach, Theorem 3.4.11, same page), so
   it is finitely generated. For an admissible, finitely generated Hilbert representation `π`,
   `π(f)` is trace class for every `f` in Wallach's space `𝒮(G)` of rapidly decreasing
   functions (Wallach, Lemma 8.1.1 and §8.1.2). `𝒮(G)` is defined in Wallach, §7.1.2 (printed
   p. 230), by the seminorms of §7.1.1 with weights `a = ‖·‖` and `b = 1`. It is not
   Harish-Chandra's Schwartz space `𝒞(G)` of the same section, whose weights are
   `a = 1 + log ‖·‖` and `b = Ξ`. The smooth compactly supported functions lie in `𝒮(G)`
   (Wallach, Theorem 7.1.1 (1), printed p. 227). This is why the archimedean class of clause 8
   contains every smooth compactly supported function. The Lean statement does not use step 7.

Steps 4 and 5 are the analytic form of Flath's observation that the restriction of an
irreducible `W_1 ⊗ W_2` to the first factor is `W_1`-isotypic (last sentence of the proof of
Flath 1979, Theorem 1, printed p. 180).

## Use and provenance

This is derived content, formulated for the Library. It extends the one-place factorization of
`GroupSchemeCuspidalIsotypicTraceFactorizationStatement` to a finite set of finite places and the
archimedean component simultaneously. It is the local part of the factorization of an
irreducible automorphic representation into a restricted tensor product, with the trace
identities used in the spectral side of a simple trace formula. Sources:

- J. R. Getz and H. Hahn, *An introduction to automorphic representations*, GTM 300 (2024),
  registered `getz-hahn-2024-automorphic-representations`. Theorem 3.10.2 (printed p. 97, PDF
  p. 113): the points of an affine algebraic group over a characteristic-zero local field form a
  type I group. Proposition 5.3.8 and Theorem 5.3.9 (printed p. 141, PDF p. 156): over a
  non-archimedean local field, a unitary representation of a reductive group is irreducible if
  and only if its smooth vectors are, and irreducible unitary representations are admissible.
- G. B. Folland, *A course in abstract harmonic analysis*, 2nd ed. (2015), registered
  `folland-2015-abstract-harmonic-analysis-second`. Theorem 7.17 (printed p. 237, PDF p. 250):
  if `G_1` or `G_2` is of type I, every irreducible unitary representation of `G_1 × G_2` is
  equivalent to an outer tensor product `π_1 ⊗ π_2`. Theorem 3.5, Schur's lemma (printed p. 77,
  PDF p. 90).
- D. Flath, *Decomposition of representations into tensor products*, Proc. Sympos. Pure Math.
  33, part 1 (1979), registered `flath-1979-tensor-products`. Theorem 1 (printed p. 179): for
  locally compact totally disconnected `G_1`, `G_2`, an admissible irreducible representation of
  `G_1 × G_2` is `W_1 ⊗ W_2` with admissible irreducible `W_i`, whose classes are determined. The
  last sentence of its proof (printed p. 180) gives the isotypy argument.
- N. R. Wallach, *Real reductive groups I* (1988), registered `wallach-1988-real-reductive-groups-i`.
  Theorem 3.4.10 (printed p. 85, PDF p. 105): an irreducible unitary representation of a real
  reductive group is admissible. Theorem 7.1.1 (1) (printed p. 227, PDF p. 247): the smooth
  compactly supported functions lie in each space `𝒞_{a,b}(G)`. §7.1.2 (printed p. 230, PDF
  p. 250): the space `𝒮(G)` of rapidly decreasing functions, the case `a = ‖·‖`, `b = 1`.
  Lemma 8.1.1 (printed p. 290, PDF p. 310) and §8.1.2 (printed p. 292, PDF p. 312): for an
  admissible, finitely generated Hilbert representation `π`, `π(f)` is trace class for `f` in
  `𝒮(G)`, and `Θ_π(f) = tr π(f)` is its distribution character.

Differences from the sources, all of which keep the content:

- finitely many places and `∞` are split off, not all places;
- the finite-place factors are realized on smooth vectors, and their maps into `P` are only
  linear;
- the archimedean factor is kept as a unitary representation on a Hilbert space;
- the archimedean test functions are all integrable functions with trace-class `σ(finf)`, a
  class that contains the smooth compactly supported ones;
- trace class of the compression to `P` is a hypothesis, as in the one-place statement.

## Intended use

In a comparison of trace formulas, the spectral side is expanded over irreducible summands `P`.
For test functions that factor over a finite set of places and `∞`, clause 8 writes the trace on
each `P` as a product of local characters at `Σ`, the archimedean character `tr σ(finf)` and a
factor `C` of the remaining places. The products of characters at the finite places can then be
separated with the Library's linear independence results for distribution characters
(`Langlands.Character.finiteFamilyLinearIndependence`, `Langlands.characterSeparation`). What
remains is an identity between archimedean characters. The isotypy clauses identify the local
factors with local components given by other means, as clause 0' of the one-place statement does
at one place.
