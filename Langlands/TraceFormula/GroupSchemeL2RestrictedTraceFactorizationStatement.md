# Restricted tensor product trace factorization on an irreducible summand of `L²([G])` (statement)

Module `Langlands.TraceFormula.GroupSchemeL2RestrictedTraceFactorizationStatement` contains one
proposition definition and no proof:

- `Langlands.TraceFormula.GroupSchemeL2RestrictedTraceFactorizationStatement`.

Let `P` be an irreducible closed invariant subspace of the canonical `L²([G])` of a connected
reductive group `G` over a number field. The statement describes `P` as a restricted tensor
product, in the form needed on the spectral side of a trace formula. It gives

- a local factor `ρ_p` of `P` at every finite place `p`;
- the archimedean factor `σ` of `P`;
- the Hecke characters of `P` at every finite place where the local factor has a fixed line, in
  particular at almost all finite places;
- the trace on `P` of every restricted tensor product test function that is unramified outside
  a finite set `S` of finite places containing a fixed finite set `Ebad`. This trace is a
  positive constant times the product of the local characters.

It is the analogue, for the whole canonical `L²` and for all places at once, of the Library
statement `GroupSchemeCuspidalMultiPlaceTraceFactorizationStatement`. That statement treats an
irreducible summand of the cuspidal space of a positive quotient and finitely many places.

## Setting and notation from the Library

- `F : Type` is a number field and `G : GroupScheme (Spec (CommRingCat.of F))` is affine and
  locally of finite type, with `hG : IsConnectedReductive G`. The canonical `L²` is defined for
  `F : Type`, so all spaces in the statement live in `Type`.
- `G(𝔸_F) = AdelicGroupPoints F G`. For a finite place `v` (`Langlands.Global.FinitePlace F`),
  `G(F_v) = PlaceGroupPoints F G (.inr v)`. `atPlace F G (.inr v) g = g_v` is the local
  component, a continuous homomorphism. `ofPlace F G (.inr v)` inserts a point of `G(F_v)` at
  `v`, with all other components `1` (module `Langlands.Global.AdelicLocalInclusion`).
- `G(F_∞) = G(F ⊗ ℝ) = InfiniteAdelicGroupPoints F G`, with its Borel σ-algebra
  (`InfiniteAdelicGroupPoints.measurableSpace`, module
  `Langlands.Global.InfiniteAdelicModularCharacter`). `infinite F G g = g_∞` is the archimedean
  component and `ofInfinite F G` inserts an archimedean point (module
  `Langlands.Global.AdelicGroupProduct`).
- The topology of `G(F_v)` is the Library's topology of local points. It makes `G(F_v)` a
  Hausdorff topological group (module `Langlands.Global.AdelicGroupLocalPoints`). Its Borel
  σ-algebra and its local compactness are Library instances
  (`PlaceGroupPoints.measurableSpace`, `PlaceGroupPoints.borelSpace`,
  `PlaceGroupPoints.locallyCompactSpace`, module `Langlands.Global.AdelicLocalCharacterNorm`).
  Total disconnectedness is an instance binder of the statement, see the remarks.
- `[G] = A_G G(F) \ G(𝔸_F)` carries the measure `RestrictionSplitCentre.canonicalMeasure F G`,
  and `L² = Lp ℂ 2 (canonicalMeasure F G)`.
  `R = RestrictionSplitCentre.canonicalL2RightAction F G centralSplitTorusCharacter hG` is the
  right regular representation of `G(𝔸_F)` on `L²` (module
  `Langlands.Global.AdelicRestrictionSplitCentreCanonical`; `centralSplitTorusCharacter` is the
  Library's proof of `CentralSplitTorusCharacterStatement`). In the Lean statement
  `Rloc v = R.comp (ofPlace F G (.inr v))`, written `R_v` below, is the action of `G(F_v)`
  on `L²`.
- `canonicalIntegratedAction F G hG f hf` (module
  `Langlands.TraceFormula.DivisionAlgebraSimpleTraceComparisonStatement`) is the operator
  `R(f) φ = ∫ f(g) R(g) φ dg` on `L²` for a function `f` that is integrable for
  `Measure.haar` on `G(𝔸_F)`. The compression of an operator `X` on `L²` to `P` is
  `P.orthogonalProjectionOnto ∘L X ∘L P.subtypeL`.
- `Langlands.Analysis.IsIrreducibleSubrepresentation R P` (module
  `Langlands.Representation.Unitary.DiscretePart`) says that `P` is closed, nonzero and
  `R`-invariant, and that `⊥` and `P` are its only closed `R`-invariant subspaces.
- `AdelicGroupPoints.IsUniformlyIntegral F G K` (module `Langlands.Global.AdelicGroupLocalPoints`)
  says that, for every regular function `a` on `G`, at almost every finite place `v` the
  values of `a` on the subgroup `K (.inr v)` are integral. `AdelicGroupPoints.extendFinite F G K`
  (module `Langlands.Global.AdelicIwasawaAssembly`) extends a family of subgroups at the finite
  places by `⊤` at the archimedean places.
- Smooth representations: `Langlands.fixedVectors ρ K` is the subspace of `K`-fixed vectors.
  `Langlands.IsSmooth` and `Langlands.IsAdmissible` are smoothness and admissibility (module
  `Langlands.Representation.Smooth.Definitions`). `Langlands.smoothVectors ρ` is the space of
  smooth vectors and `Langlands.smoothPart ρ` the representation on it, with
  `Langlands.isSmooth_smoothPart`. `Representation.IsIrreducible` is Mathlib's algebraic
  irreducibility. `Character.distribution μ ρ hρ f` is the trace of the finite-rank operator
  `ρ(f) = ∫ f(y) ρ(y) dμ(y)` for `f : SchwartzBruhat G(F_v)`.
- Hecke algebras: for a Haar measure `μ` and a compact open subgroup `U` of `G(F_v)`,
  `Hecke.HeckeAlgebra.Corner μ U hU` (module `Langlands.Representation.Hecke.Corner`) is the
  algebra of bi-`U`-invariant Schwartz–Bruhat functions with the convolution of `μ`. Its unit is
  `e_U = μ(U)⁻¹ 1_U`. Its `star` (module `Langlands.Representation.Hecke.UnimodularStar`) is
  `(star h)(g) = conj (h g⁻¹)`. For a smooth `ρ`, `Hecke.cornerAction μ ρ hρ U hU` (module
  `Langlands.Representation.Hecke.CornerAction`) is the algebra homomorphism by which `h` acts
  on the `U`-fixed vectors as `x ↦ ∫ h(g) ρ(g) x dμ(g)`.
- Archimedean representations, as in `GroupSchemeCuspidalMultiPlaceTraceFactorizationStatement`:
  a homomorphism `σ : G(F_∞) →* (H →L[ℂ] H)` on a complex Hilbert space.
  `Langlands.Archimedean.IsContinuousRepresentation σ` is joint continuity and
  `Langlands.Archimedean.IsTopologicallyIrreducible σ` is topological irreducibility (module
  `Langlands.Representation.Archimedean.SmoothVectors`). Unitarity is `‖σ g x‖ = ‖x‖`.
  `σ(finf) = Langlands.Analysis.integratedIsometricAction μinf σ hσnorm hσmeas finf hfinf`
  (module `Langlands.Representation.Unitary.IntegratedOperator`) is the bounded operator
  `x ↦ ∫ finf(g) • σ(g) x dμinf(g)`.
- `IsTraceClass` and `operatorTrace` are the Library's trace-class predicate and trace (modules
  `Langlands.Analysis.OperatorIdeals` and `Langlands.Analysis.OperatorTrace`).

## Statement

**Hypotheses.** Let `F`, `G`, `hG` be as above. Assume `TotallyDisconnectedSpace G(F_v)` for
every finite place `v` (instance binder). Let `U v ≤ G(F_v)` be open subgroups
(`OpenSubgroup`) at the finite places, compact (`hU v`), such that:

- (i) `IsUniformlyIntegral F G (extendFinite F G (fun v => (U v).toSubgroup))`;
- (ii) for every `g ∈ G(𝔸_F)`, `g_v ∈ U v` for all but finitely many finite places `v`.

Let `μp v` be Haar measures on `G(F_v)` with `μp v (U v) = 1` for all but finitely many `v`, and
let `μinf` be a Haar measure on `G(F_∞)`. Let `P : Submodule ℂ L²` with `[CompleteSpace P]` and
`IsIrreducibleSubrepresentation R P`.

**Conclusion.** There exist:

- for every finite place `p`, a complex vector space `V p : Type`, a representation
  `ρ p : Representation ℂ G(F_p) (V p)` and `hρ p : IsAdmissible (ρ p)`;
- a complex Hilbert space `H : Type`, a homomorphism `σ : G(F_∞) →* (H →L[ℂ] H)`, a proof
  `hσnorm` that every `σ g` preserves the norm and a proof `hσmeas` that every orbit map
  `g ↦ σ g x` is a.e. strongly measurable for `μinf`;
- a finite set `Ebad : Finset (FinitePlace F)`,

such that:

1. **Irreducibility at the finite places.** Every `ρ p` is irreducible.
2. **Realization at `p`.** For every finite `p` there is a linear map `j₀ : V p →ₗ[ℂ] L²` with
   `j₀ ≠ 0`, `LinearMap.range j₀ ≤ P` and `j₀ (ρ p y x) = R_p y (j₀ x)`.
3. **Isotypy at `p`.** For every finite `p`, every `V' : Type`, every representation `ρ'` of
   `G(F_p)` on `V'` with `IsSmooth ρ'` and `ρ'.IsIrreducible`, and every linear
   `j : V' →ₗ[ℂ] L²` with `j ≠ 0`, `LinearMap.range j ≤ P` and `j (ρ' y x) = R_p y (j x)`, there is
   a linear equivalence `E : V' ≃ₗ[ℂ] V p` with `E (ρ' y x) = ρ p y (E x)`.
4. **Continuity at `∞`.** `IsContinuousRepresentation σ`.
5. **Irreducibility at `∞`.** `IsTopologicallyIrreducible σ`.
6. **Realization at `∞`.** There is a linear isometry `jinf : H →ₗᵢ[ℂ] L²` with `jinf x ∈ P` for
   all `x` and `jinf (σ g x) = R (ofInfinite F G g) (jinf x)`.
7. **Isotypy at `∞`.** For every complex Hilbert space `H' : Type`, every
   `σ' : G(F_∞) →* (H' →L[ℂ] H')` that is jointly continuous, norm-preserving and topologically
   irreducible, and every bounded linear `j : H' →L[ℂ] L²` with `j ≠ 0`, `j x ∈ P` for all `x`
   and `j (σ' g x) = R (ofInfinite F G g) (j x)`, there is a linear isometric equivalence
   `E : H' ≃ₗᵢ[ℂ] H` with `E (σ' g x) = σ g (E x)`.
8. **Unramified places.** For every finite place `p ∉ Ebad`:
   - some `x ∈ fixedVectors (smoothPart R_p) (U p)` has `x ≠ 0` and underlying vector in `P`.
     Such a vector is a nonzero vector of `P` that is fixed by `U p` and smooth for `R_p`;
   - `Module.finrank ℂ (fixedVectors (ρ p) (U p)) = 1`.
9. **Hecke characters.** For every finite place `p` with
   `Module.finrank ℂ (fixedVectors (ρ p) (U p)) = 1`, there is a `ℂ`-algebra homomorphism
   `χ : Corner (μp p) (U p) (hU p) →ₐ[ℂ] ℂ` such that
   - (a) `cornerAction (μp p) (smoothPart R_p) _ (U p) (hU p) h x = χ h • x` for every `h` and
     every `x ∈ fixedVectors (smoothPart R_p) (U p)` whose underlying vector lies in `P`;
   - (b) `‖χ h‖ ≤ ∫ ‖h g‖ d(μp p)(g)` for every `h`;
   - (c) `χ (star h) = conj (χ h)` for every `h`;
   - (d) `cornerAction (μp p) (ρ p) (hρ p).1 (U p) (hU p) h x = χ h • x` for every `h` and every
     `x ∈ fixedVectors (ρ p) (U p)`.

   By clause 8 this applies at every `p ∉ Ebad`. It also applies at the places of `Ebad` where
   `ρ p` has a `U p`-fixed line.
10. **Trace factorization.** There is a real number `c > 0` with the following property. Let
   `S : Finset (FinitePlace F)` with `Ebad ⊆ S`. Let `finf : G(F_∞) → ℂ` be `μinf`-integrable
   (`hfinf`) with `σf := σ(finf)` trace class, and let `fs p : SchwartzBruhat G(F_p)` for every
   finite place `p` (only `p ∈ S` enters). Put `U^S = {y ∈ G(𝔸_F) | y_p ∈ U p for every finite
   p ∉ S}` and

   `f x = U^S.indicator (fun y => finf (y_∞) * ∏_{p ∈ S} fs p (y_p)) x`.

   If `f` is integrable for `Measure.haar` (`hf`) and the compression `RPf` of
   `canonicalIntegratedAction F G hG f hf` to `P` is trace class, then
   `operatorTrace RPf = c * operatorTrace σf * ∏_{p ∈ S} Character.distribution (μp p) (ρ p) (hρ p) (fs p)`.

The function `f` is the restricted tensor product
`f = finf ⊗ (⊗_{p ∈ S} fs p) ⊗ (⊗_{p ∉ S} 1_{U p})`. The infinite product of the indicator
functions `1_{U p}(y_p)`, `p ∉ S`, is written as the indicator function of the set `U^S`. In
the Lean statement, `y_∞` is `AdelicGroupPoints.infinite F G y` and `y_p` is
`atPlace F G (.inr p) y`.

## Remarks on the formalization

- **The integrality hypotheses.** Fix generators `a_1, …, a_n` of the coordinate ring of `G`,
  and let `G(𝒪_v)` be the set of points of `G(F_v)` at which all `a_i` are integral.
  Hypothesis (i) says that `U v ⊆ G(𝒪_v)` for almost all `v`. Hypothesis (ii) gives
  `G(𝒪_v) ⊆ U v` for almost all `v` (step 1 below). Together they say that `U v = G(𝒪_v)` for
  almost all `v`. Then `U v` is hyperspecial for almost all `v`. Clause 8 and the trace
  identity of clause 10 need this.
  - Hypothesis (i) alone does not suffice. It holds, for example, for `G = GL_2` with `U v` the
    principal congruence subgroup of level `v` at every finite place. Let `π` be a cuspidal
    representation, and `v` one of the almost all places where its component `π_v` is an
    unramified irreducible principal series. The space `π_v^{U v}` has dimension `q_v + 1`
    (the functions on `ℙ¹(𝔽_{q_v})`). It is an irreducible module of the corner algebra
    (Getz–Hahn, Proposition 5.3.4), so the corner algebra does not act on it by scalars.
    The equality `finrank = 1` of clause 8 then fails at infinitely many places, and the corner
    algebra has no character on the fixed vectors of `P` there. The trace identity of clause 10
    fails too, because `tr π_v(1_{U v}) = q_v + 1 ≠ 1`.
  - Hypothesis (ii) alone does suffice, but only through a further theorem. It gives
    `G(𝒪_v) ⊆ U v` for almost all `v`, and a compact subgroup containing a hyperspecial
    subgroup equals it, because hyperspecial subgroups have the largest volume among compact
    subgroups (Tits, 3.8.2). So (i) follows from (ii). Both are stated, (i) in the form of the
    Library's `IsUniformlyIntegral`.
  - At finitely many places, `U v` is only required to be a compact open subgroup, and
    `μp v (U v)` is arbitrary.
- **`Ebad`.** `Ebad` depends on `P`. It contains the places where `U v ≠ G(𝒪_v)`, where
  `G(𝒪_v)` is not hyperspecial, where `μp v (U v) ≠ 1`, or where the local component of `P` has
  no `U v`-fixed vector. Clause 10 is asserted only for `S ⊇ Ebad`. Outside `S` the test function
  is `1_{U v}`, and its trace on the local component is `1` for `v ∉ Ebad`.
- **The constant `c`.** In the proof, `c` is the ratio of `Measure.haar` on `G(𝔸_F)` to the
  product measure `μinf × ⊗'_v μp v` (step 5 below), so `c > 0`. It does not depend on `S`, on
  the test functions or on `P`. The statement asserts `c > 0`, and places `c` after `P`, so it
  does not assert that `c` is the same for all `P`. Positivity is what makes clause 10 nontrivial:
  with `c = 0` it would only say that the traces vanish.
- **The Hecke characters.** `χ` is chosen separately at every place `p` where `ρ p` has a
  `U p`-fixed line. Clause 9 is stated at all these places, not only outside `Ebad`, because a
  sum over many summands `P` meets unbounded sets `Ebad`. It needs no hyperspecial subgroup: it
  uses only the unitarity of the local factor and the unimodularity of `G(F_p)` (step 4 below).
  Clause 9 (a) is the analogue, for an arbitrary group `G` and the given subgroups `U p`, of
  `Langlands.Automorphic.DiscreteHeckeIsolation.HasSphericalHeckeCharacterOn`. That predicate is
  formulated for `GL_{r+1}` with the spherical Hecke algebra of `GL_{r+1}(𝒪_p)`. Here the
  algebra is the corner `Corner (μp p) (U p)` for the given Haar measure. The action is
  `Hecke.cornerAction` on the `U p`-fixed vectors of the smooth part of `R_p`, for the whole
  space `L²`. The vectors are then restricted to those lying in `P`. The same measure `μp p`
  is used in clause 9 and in the local characters of clause 10. Clauses 9 (b) and (c) are the
  uniform bound and the conjugation property for characters of `Corner (μp p) (U p)`. The bound
  `∫ ‖h‖ dμp p` does not depend on `P`, and `star h` serves for every `P`.
- **The archimedean test functions.** These are as in
  `GroupSchemeCuspidalMultiPlaceTraceFactorizationStatement`: all `μinf`-integrable `finf` with
  `σ(finf)` trace class. The archimedean character is `operatorTrace σ(finf)`. By
  Harish-Chandra's admissibility theorem and Wallach's trace-class lemma, this class contains
  every smooth compactly supported function on `G(F_∞)`; the Markdown of that statement gives
  the argument and the page references. The Lean statement keeps "`σ(finf)` is trace class" as
  a hypothesis.
- **Instance binder.** The statement binds `TotallyDisconnectedSpace G(F_v)` at every finite
  place, which `Character.distribution` needs. It is true: the topology of `G(F_v)` is the
  topology of evaluation of regular functions, so `G(F_v)` is homeomorphic to a subspace of a
  product of copies of the totally disconnected field `F_v`. `[CompleteSpace P]` follows from the closedness of `P`. It is bound because
  the orthogonal projection onto `P` needs it as an instance.
- **`hσnorm`, `hσmeas`.** These are conclusions, needed as arguments of
  `integratedIsometricAction`, as in the multi-place statement.
- **Compression.** `P` is closed and `R`-invariant, so `R(f)` maps `P` into `P`, and the
  compression `RPf` is the restriction of `R(f)` to `P`.
- **Integrability and trace class.** For `f` as in clause 10, `f` is integrable and `RPf` is
  trace class whenever `finf` is integrable and `σ(finf)` is trace class (step 5). The
  statement keeps both as hypotheses.

## Why the statement is true

1. **Integral structure.** Let `a_1, …, a_n` generate the coordinate ring of `G` over `F`, and
   let `G(𝒪_v)` be as in the remarks. Hypothesis (i) gives `U v ⊆ G(𝒪_v)` for almost all `v`.
   Suppose that `G(𝒪_v) ⊄ U v` for infinitely many `v`. Choose `k_v ∈ G(𝒪_v) \ U v` at these
   places, and `k_v = 1` at all other places. Every regular function is a polynomial in the
   `a_i` with coefficients in `F`, and these coefficients are integral at almost all places, so
   this family has integral values at almost all places. It therefore glues to a point
   `g ∈ G(𝔸_F)` with `g_v = k_v` (the Library's `AdelicGroupPoints.glue`). This contradicts
   (ii). So `U v = G(𝒪_v)` for `v` outside a finite set. After inverting finitely many primes,
   the `a_i` generate a Hopf algebra, that is, a model of `G` over a ring of `S`-integers whose
   integral points are `G(𝒪_v)`. Hence `U v` is hyperspecial for almost all `v` (Getz–Hahn,
   Proposition 2.4.8; Tits, 3.9.1). The adelic group is the restricted product of the `G(F_v)`
   with respect to these subgroups (Getz–Hahn, Proposition 2.4.10; changing finitely many
   subgroups does not change it). For `v` with `U v` hyperspecial, the corner algebra
   `C_c^∞(G(F_v) // U v)` is commutative (Getz–Hahn, Theorem 5.5.2), and an irreducible
   admissible representation `W` with `W^{U v} ≠ 0` has `dim W^{U v} = 1` (Getz–Hahn,
   Corollary 5.5.6).
2. **Tensor decomposition.** `R` is a strongly continuous unitary representation, because
   `canonicalMeasure` is right invariant, and `P` is an irreducible unitary representation of
   `G(𝔸_F)`.
   - The groups `G(F_∞) = (Res_{F/ℚ} G)(ℝ)` and `G(F_v)` are of type I (Getz–Hahn,
     Theorem 3.10.2). So `P ≅ H_∞ ⊗̂ H^∞` with irreducible unitary representations of `G(F_∞)`
     and of `G(𝔸_F^∞)` (Getz–Hahn, Theorem 6.6.1; Folland, Theorem 7.17).
   - `P` is the Hilbert restricted tensor product `⊗̂'_v π_v` of irreducible unitary
     representations `π_v`, almost all unramified (Flath, Theorem 4). On smooth vectors,
     `H^∞` is the algebraic restricted tensor product `⊗'_v W_v` of irreducible admissible
     representations `W_v` (Getz–Hahn, Theorems 6.6.2–6.6.3 and Theorem 5.7.1, Flath's
     theorem; the factorization over a product of two groups is Theorem 5.7.2). Here `W_v` is the smooth part of `π_v`, and the
     restricted product is taken with respect to vectors `ξ_v ∈ W_v^{U v}`, for `v` outside a
     finite set, with `dim W_v^{U v} = 1` there.
   - Take `σ = π_∞` on `H = H_∞`, and `ρ p = W_p`. Each `ρ p` is irreducible and admissible
     (Getz–Hahn, Proposition 5.3.8 and Theorem 5.3.9).
   - Let `Ebad` consist of the finitely many places of step 1 where `U v` is not a hyperspecial
     `G(𝒪_v)`, the places where `μp v (U v) ≠ 1`, and the places where no `ξ_v` is chosen.
3. **Realization and isotypy.** For a place `p`, write `P ≅ H_p ⊗̂ H'_p`, with `H'_p` the
   completed tensor product of the other factors.
   - **Realization.** With a unit vector `η ∈ H'_p`, the map `x ↦ x ⊗ η` restricted to `ρ p`
     gives `j₀`. At `∞`, the map `x ↦ x ⊗ η` is the isometry `jinf`.
   - **Isotypy at `p`.** Let `j` be as in clause 3. The image of `j` consists of vectors fixed
     by open subgroups of `G(F_p)`. For a compact open `K ≤ G(F_p)`, the `K`-fixed vectors of
     `H_p ⊗̂ H'_p` are `H_p^K ⊗ H'_p`, and `H_p^K` is finite dimensional by admissibility. So the
     smooth vectors of `R_p` in `P` form the algebraic tensor product `ρ p ⊗ H'_p`.
     Contracting `j` with a suitable linear functional on `H'_p` gives a nonzero intertwiner
     `V' → V p`. Its kernel and image are subrepresentations, so it is an isomorphism. This is
     Flath's observation that the restriction of `W_1 ⊗ W_2` to `G_1` is `W_1`-isotypic (last
     sentence of the proof of Flath, Theorem 1).
   - **Isotypy at `∞`.** The argument is Schur's lemma applied to `A*A` for the contracted
     bounded intertwiner `A : H' → H_∞` (Folland, Theorem 3.5). It is step 5 of the Markdown of
     `GroupSchemeCuspidalMultiPlaceTraceFactorizationStatement`.
4. **Unramified places and Hecke characters.** Write `P ≅ H_p ⊗̂ H'_p` as in step 3.
   - **Clause 8.** Let `p ∉ Ebad`. Then `W_p^{U p} = ℂ ξ_p` is a line, and `ρ p^{U p} = W_p^{U p}`
     because `U p`-fixed vectors are smooth. The `U p`-fixed vectors of `P` form
     `ℂ ξ_p ⊗̂ H'_p`, the range of `e_{U p} ⊗ 1`, which is nonzero. These vectors are fixed by
     the open subgroup `U p`, so they are smooth for `R_p`.
   - **Clause 9: the character.** Let `p` be any finite place with `ρ p^{U p}` a line, spanned
     by a unit vector `ξ_p ∈ W_p ⊆ H_p`. No hypothesis on `U p` beyond compact openness is used.
     The `U p`-fixed vectors of `P` form `ℂ ξ_p ⊗̂ H'_p`. For `h` in the corner algebra and a
     `U p`-fixed vector `x`, the corner action is `∫ h(g) R_p(g) x dμp p(g)`, which corresponds
     to `π_p(h) ⊗ 1`. Now `π_p(h) ξ_p ∈ W_p^{U p} = ℂ ξ_p`, so `π_p(h) ξ_p = χ(h) ξ_p` for a
     scalar `χ(h)`. This `χ` is an algebra homomorphism, and the unit `e_{U p}` maps to `1`.
     This gives (a), and (d) because `ρ p^{U p} = ℂ ξ_p`.
   - **Bound (b).** `π_p` is unitary, so `|χ(h)| = ‖π_p(h) ξ_p‖ ≤ ∫ |h| dμp p`.
   - **Conjugation (c).** `G(F_p)` is unimodular for every `p` (Getz–Hahn, Corollary 3.6.2), so
     `μp p` is invariant under inversion and `π_p(star h) = π_p(h)*`. Hence
     `χ(star h) = ⟨π_p(star h) ξ_p, ξ_p⟩ = ⟨ξ_p, π_p(h) ξ_p⟩ = conj χ(h)`.
5. **Trace.** `G(𝔸_F) = G(F_∞) × G(𝔸_F^∞)`, and `G(𝔸_F^∞)` is the restricted product of the
   `G(F_v)` with respect to the `U v`.
   - **The constant.** Since `μp v (U v) = 1` for almost all `v`, the restricted product measure
     `⊗'_v μp v` is defined: it gives `∏_v Ω_v` the measure `∏_v μp v (Ω_v)` when `Ω_v = U v`
     for almost all `v` (Getz–Hahn, §5.6). By uniqueness of Haar measure,
     `Measure.haar = c · (μinf × ⊗'_v μp v)` for some `c > 0`. This `c` does not depend on `S`,
     on the test functions or on `P`.
   - **The tensor product.** Let `S ⊇ Ebad`. Under the factorization, the operator `R(f)` on `P`
     corresponds to `c · σ(finf) ⊗ ⊗_{p ∈ S} π_p(fs p) ⊗ ⊗_{v ∉ S} π_v(1_{U v})`.
   - **The tail.** For `v ∉ S` we have `v ∉ Ebad`, so `π_v(1_{U v}) = μp v (U v) · e_v` is the
     orthogonal projection `e_v` onto `ℂ ξ_v`. The tail is therefore the rank-one projection
     onto `⊗_{v ∉ S} ξ_v`, of trace `1`.
   - **The places of `S`.** Each `fs p` is bi-invariant under a compact open subgroup `K_p`, so
     `π_p(fs p)` has finite rank, with range in the finite-dimensional space `W_p^{K_p}`. Its
     trace is `Character.distribution (μp p) (ρ p) (hρ p) (fs p)`. In particular `R(f)` on `P`
     is trace class when `σ(finf)` is, and `f` is integrable when `finf` is.
   - **The product.** The trace of a tensor product of a trace-class operator with finite-rank
     operators is the product of the traces. The trace is invariant under the unitary
     equivalence. This gives clause 10.

## Use and provenance

This is derived content, formulated for the Library. It packages Flath's factorization of an
irreducible unitary representation of `G(𝔸_F)` into a restricted tensor product, the unramified
Hecke algebra at almost all places, and the multiplicativity of traces of tensor products, for
irreducible summands of the canonical `L²([G])`. The following are derived and not in the
sources in this form:

- the trace identity is asserted only for `S ⊇ Ebad`, with the indicator function of `U^S`;
- `c` is the comparison constant of step 5 between `Measure.haar` and `μinf × ⊗'_v μp v`;
- the integrality of the family `U` is given by hypotheses (i) and (ii) instead of a model of
  `G`;
- the Hecke characters are given, with the bound and the conjugation property, at every place
  where the local factor has a fixed line (clause 9);
- the finite-place factors are realized on smooth vectors with linear maps into `P`, and the
  archimedean factor on a Hilbert space;
- the trace class of the compression is a hypothesis.

Sources:

- J. R. Getz and H. Hahn, *An introduction to automorphic representations, with a view toward
  trace formulae*, GTM 300 (2024), registered `getz-hahn-2024-automorphic-representations`.
  - Proposition 2.4.8 and Proposition 2.4.10 (printed p. 61, PDF p. 78): for a model of a
    reductive group, the integral points are hyperspecial at almost all places, and the adelic
    points are the restricted product with respect to them.
  - Corollary 3.6.2 (printed p. 88, PDF p. 104): if `G°` is reductive, `G(F_v)` is unimodular.
  - Theorem 3.10.2 (printed p. 97, PDF p. 113): the points of an affine algebraic group over a
    characteristic-zero local field form a type I group.
  - Proposition 5.3.4 (printed p. 140, PDF p. 155): a smooth representation is irreducible if
    and only if its spaces of fixed vectors are irreducible modules of the corner algebras.
  - Proposition 5.3.8 and Theorem 5.3.9 (printed p. 141, PDF p. 156): a unitary representation
    is irreducible if and only if its smooth vectors are, and irreducible unitary
    representations are admissible.
  - Definition 5.5.1 (printed p. 146, PDF p. 161), Theorem 5.5.2 (printed p. 147, PDF p. 162)
    and Corollary 5.5.6 (printed p. 148, PDF p. 163): the unramified Hecke algebra of a
    hyperspecial subgroup is commutative, and its fixed line in an irreducible admissible
    unramified representation is one-dimensional.
  - §5.6, (5.12)–(5.14) (printed pp. 150–151, PDF pp. 165–166): the restricted product, the
    product Haar measure normalized by `∫_{K_v} d_r g_v = 1` for almost all `v`, and the
    idempotents `e_{K_v}`.
  - Theorem 5.7.1 (Flath) and Theorem 5.7.2 (printed pp. 152–153, PDF pp. 167–168).
  - Theorems 6.6.1–6.6.3 (printed pp. 170–171, PDF pp. 184–185): an irreducible unitary
    representation of `G(𝔸_F)` is `π_∞ ⊗̂ π^∞`, with the description of its finite and smooth
    vectors.
- D. Flath, *Decomposition of representations into tensor products*, Proc. Sympos. Pure Math.
  33, part 1 (1979), registered `flath-1979-tensor-products`.
  - Theorem 1 (printed p. 179) and the last sentence of its proof (printed p. 180): isotypy.
  - §3 and Theorem 3 (printed p. 181): factorization of admissible irreducible representations
    of `G(𝔸)`, and commutativity of `H(G_v, K_v)` for almost all `v`.
  - §4 and Theorem 4 (printed p. 182): a continuous irreducible unitary representation of
    `G(𝔸)` is a Hilbert restricted tensor product of irreducible unitary representations,
    almost all unramified, unique up to isomorphism.

  The registered file is the Corvallis Part I volume, PDF pp. 175–178.
- G. B. Folland, *A course in abstract harmonic analysis*, 2nd ed. (2015), registered
  `folland-2015-abstract-harmonic-analysis-second`.
  - Theorem 3.5, Schur's lemma (printed p. 77, PDF p. 90).
  - Theorem 7.17 (printed p. 237, PDF p. 250): irreducible representations of a product with a
    type I factor are outer tensor products.
- J. Tits, *Reductive groups over local fields*, Proc. Sympos. Pure Math. 33, part 1 (1979),
  registered `tits-1979-reductive-groups-local-fields`.
  - 3.8.2 (printed p. 55, PDF p. 59): hyperspecial subgroups have maximal volume among compact
    subgroups.
  - 3.9.1 (printed p. 55, PDF p. 59): integral points are hyperspecial at almost all places.

## Intended use

In a comparison of trace formulas, the spectral side is a sum over irreducible summands `P`.
For restricted tensor product test functions unramified outside `S`, clause 10 writes each
summand as `c_P · tr σ_P(finf) · ∏_{p ∈ S} Θ_{ρ_P,p}(fs p)` once `S ⊇ Ebad_P`. Clause 9 gives
Hecke characters that satisfy the two hypotheses of the Library's
`Langlands.TraceFormula.boundedCharacterSeparation`
(`BoundedCharacterSeparationStatement`). The bound `∫ ‖h‖ dμp p` is uniform in `P`, and
`h' = star h` realizes the conjugates. So the summands with one system of Hecke eigenvalues can
be isolated. The isotypy clauses identify the local factors with components obtained by other
means.
