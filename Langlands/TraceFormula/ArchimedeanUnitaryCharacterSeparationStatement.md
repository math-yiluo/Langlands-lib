# Separation of archimedean characters of irreducible unitary representations of `GL_n(F ⊗ ℝ)`

The module `Langlands.TraceFormula.ArchimedeanUnitaryCharacterSeparationStatement`
defines four predicates in the namespace `Langlands.TraceFormula.ArchimedeanUnitary`
and two proposition definitions in the namespace `Langlands.TraceFormula`:

- `ArchimedeanUnitaryTraceClassStatement.{uF, uE}`, Harish-Chandra's trace-class
  theorem for irreducible unitary representations of `GL_n(F ⊗ ℝ)`;
- `ArchimedeanUnitaryCharacterSeparationStatement.{uF, uι, uH, uE}`, the separation
  of the character of an irreducible unitary representation from an absolutely
  summable family of such characters.

Both are `def`s returning `Prop`. The module states them and proves neither.

## Notation

- `F : Type uF` is a number field (`[Field F] [NumberField F]`) and `n : ℕ` is
  arbitrary.
- `G∞ = InfiniteAdelicGL F n` is the Library's group
  `Matrix.GeneralLinearGroup (Fin n) (InfiniteAdeleRing F)` with its units topology;
  it is the archimedean factor embedded in the adelic group by
  `Langlands.Global.AdelicGL.ofInfinite`. Since `InfiniteAdeleRing F` is the product
  of the completions of `F` at its infinite places, `G∞` is
  `∏_{v real} GL_n(ℝ) × ∏_{v complex} GL_n(ℂ)`.
- The test functions are `Langlands.Global.ArchimedeanGL.SmoothCompactKernel F n`:
  the compactly supported members of `SmoothFunctions F n`, whose smoothness is real
  smoothness in the mixed real and complex coordinates
  `Langlands.Global.archimedeanGLCoordinates`. For a test function `f`, its values are
  `f.val.val : G∞ → ℂ`. This is the space `C_c^∞(G∞)`.
- The measure: `[MeasurableSpace G∞] [BorelSpace G∞]` and a left Haar measure `μ`
  (`[μ.IsHaarMeasure]`). Both statements are quantified over every such `μ`. Any two
  Haar measures are proportional, and `G∞` is unimodular.
- A Hilbert space is a type with `NormedAddCommGroup`, `InnerProductSpace ℂ` and
  `CompleteSpace` instances. A representation on it is a monoid homomorphism
  `σ : G∞ →* (H →L[ℂ] H)` into the bounded operators.

### The four predicates

- `IsUnitaryRepresentation σ` is the conjunction of
  `Langlands.Archimedean.IsContinuousRepresentation σ`, joint continuity of
  `(g, x) ↦ σ g x` on `G∞ × H`, and `⟪σ g x, σ g y⟫_ℂ = ⟪x, y⟫_ℂ` for all `g, x, y`.
  Each `σ g` is then a unitary operator, with inverse `σ g⁻¹`. By polarization,
  preservation of the inner product is equivalent to preservation of the norm,
  `‖σ g x‖ = ‖x‖` for all `g` and `x`. For a family of unitary
  operators, joint continuity is equivalent to strong continuity (continuity of every
  orbit map `g ↦ σ g x`), so this is the usual notion of a unitary representation.
- `IsIrreducibleUnitaryRepresentation σ` adds
  `Langlands.Archimedean.IsTopologicallyIrreducible σ`: `H` is nontrivial and every
  closed `σ`-invariant subspace is `⊥` or `⊤`.
- `IsIntegratedOperator μ σ f A` says that the bounded operator `A` is
  `σ(f) = ∫ f(g) σ(g) dμ(g)`, taken vectorwise: `A x = ∫ g, f.val.val g • σ g x ∂μ`
  for every `x`. For a unitary representation the integrand is continuous with compact
  support, hence Bochner integrable. Two bounded operators with this property agree on
  every vector, so there is at most one. The Library's constructor
  `Langlands.Analysis.integratedIsometricAction` produces an operator of this form from
  norm preservation, measurability of the orbit maps and integrability of `f`: its value
  at `x` is `∫ g, f g • σ g x ∂μ` by definition
  (`Langlands.Analysis.integratedIsometricAction_apply`).
- `UnitarilyEquivalent σ τ`, for representations on `H` and `E`, says that there is a
  surjective linear isometry `e : H ≃ₗᵢ[ℂ] E` with `e (σ g x) = τ g (e x)` for all
  `g` and `x`.

### Traces and sums

- `IsTraceClass A` and `operatorTrace A` are the Library's
  `Langlands.Analysis.OperatorIdeals.IsTraceClass` and `operatorTrace`. `IsTraceClass A`
  is summability of the diagonal of `leftModulus A = sqrt(A A*)` in some Hilbert basis.
  `operatorTrace A` is the diagonal sum `∑' i, ⟪b i, A (b i)⟫` in one chosen Hilbert
  basis `b`. For a trace-class `A` this sum is the trace and does not depend on the basis
  (`Langlands.Analysis.OperatorIdeals.operatorTraceBasis`). Thus, when `σ(f)` is of
  trace class, `operatorTrace σ(f)` is the value `Θ_σ(f) = tr σ(f)` of the distribution
  character of `σ`.
- `HasSum` is Mathlib's unconditional summation over finite subsets of the index
  type. For complex families it is equivalent to absolute summability:
  `summable_norm_iff` gives `Summable (‖a ·‖) ↔ Summable a` in finite dimension.

## The trace-class statement

`ArchimedeanUnitaryTraceClassStatement` says: for every number field `F`, every `n`,
every left Haar measure `μ` on `G∞`, every Hilbert space `E : Type uE` and every
`π : G∞ →* (E →L[ℂ] E)` with `IsIrreducibleUnitaryRepresentation π`, and every test
function `f`, there is a bounded operator `B` with `IsIntegratedOperator μ π f B` and
`IsTraceClass B`.

Since the integrated operator is unique, this says that `π(f)` exists and is of trace
class for every test function. It makes `Θ_π(f) = operatorTrace π(f)` the actual trace.

## The separation statement

`ArchimedeanUnitaryCharacterSeparationStatement` quantifies over:

- a number field `F : Type uF`, `n : ℕ` and a left Haar measure `μ` on `G∞` as above;
- an index type `ι : Type uι`, Hilbert spaces `H : ι → Type uH` (one universe for the
  whole family) and representations `σ i : G∞ →* (H i →L[ℂ] H i)`, with operators
  `A i f : H i →L[ℂ] H i` for every test function `f`;
- a Hilbert space `E : Type uE`, a representation `π : G∞ →* (E →L[ℂ] E)` and operators
  `B f : E →L[ℂ] E`;
- complex numbers `c : ι → ℂ` and `c₀ : ℂ`.

The hypotheses are:

1. every `σ i` is an irreducible unitary representation;
2. `IsIntegratedOperator μ (σ i) f (A i f)` for all `i` and `f`, so `A i f = σ i(f)`;
3. `π` is an irreducible unitary representation;
4. `IsIntegratedOperator μ π f (B f)` for all `f`, so `B f = π(f)`;
5. for every test function `f`,
   `HasSum (fun i => c i * operatorTrace (A i f)) (c₀ * operatorTrace (B f))`, that is,
   the family `c i Θ_{σ i}(f)` is absolutely summable with sum `c₀ Θ_π(f)`.

The conclusion is the conjunction of:

- `HasSum (fun i : {i : ι // UnitarilyEquivalent (σ i) π} => c i.val) c₀`: the `c i`
  over the indices with `σ i` unitarily equivalent to `π` are absolutely summable with
  sum `c₀`;
- `c₀ ≠ 0 → ∃ i, UnitarilyEquivalent (σ i) π`.

The first conclusion needs no assumption on `c₀`. The second follows from the first,
because a sum over an empty type is `0`; it is recorded for direct use. Under the
hypothesis `c₀ ≠ 0` the statement gives both: some `σ i` is unitarily equivalent to
`π`, and the coefficients over all such `i` add up to `c₀`.

No uniformity hypothesis on the family appears. The argument below uses hypothesis 5
only at test functions of the form `f* * f`. There it uses both parts of hypothesis 5:
the absolute summability of the family `c i Θ_{σ i}(f* * f)`, and the value
`c₀ Θ_π(f* * f)` of its sum.

In the spectral expansion of `L²` of a compact quotient, these two parts have different
sources. For a smooth compactly supported test function `φ = f∞ ⊗ f^∞` on the adelic
group, the operator `R(φ)` on `L²` is of trace class. For the decomposition of `L²` into
a Hilbert direct sum of irreducible invariant subspaces `V_T`, the sum
`∑_T |tr(R(φ)|_{V_T})|` is at most the trace norm of `R(φ)`. With the finite part
`f^∞` fixed, `tr(R(φ)|_{V_T}) = Θ_{T∞}(f∞) · tr T^∞(f^∞)` for every `f∞`. The
trace-norm bound and this factorization give the absolute summability part of
hypothesis 5, with coefficients `c_T = tr T^∞(f^∞)` indexed by the summands. They do not
give the value of the sum. The identity of the sum with `c₀ Θ_π(f∞)` is a separate
input. It comes from a comparison of trace formulas, which equates two such spectral
expressions for all `f∞`; one then groups the terms on one side and moves the terms of
one equivalence class `π` to the other.

## Why the statements hold

This section explains the mathematics. The module contains no proof.

### Trace class (Harish-Chandra)

Knapp, Theorem 10.2 (printed p. 334) proves that every irreducible unitary
representation of a linear connected reductive group has a global character: `π(f)` is
of trace class for every `f ∈ C_c^∞(G)` and `f ↦ tr π(f)` is a distribution. The
hypothesis `n_τ ≤ C dim τ` of that theorem holds for irreducible unitary
representations by Knapp, Theorem 8.1 (printed p. 205).

Both statements quantify over every `n : ℕ`, and the cases `n > 0` and `n = 0` are
treated separately.

Let `n > 0`. The group `G∞` is not connected when `F` has a real place. Its identity
component `G∞° = ∏_{v real} GL_n(ℝ)⁺ × ∏_{v complex} GL_n(ℂ)` can be realized as a
closed connected group of complex block-diagonal matrices stable under conjugate
transpose. It is therefore a linear connected reductive group in Knapp's sense (printed
p. 3), and it is open of index `2^{r₁}`, where `r₁` is the number of real places. The
restriction of an irreducible unitary representation to an open normal subgroup of
finite index is a finite direct sum of irreducible unitary representations. Moreover
`π(f) = ∑_{g ∈ G∞/G∞°} π(g) π|_{G∞°}(f_g)`, where `f_g(h) = f(g h)` for `h ∈ G∞°`
lies in `C_c^∞(G∞°)`. Hence `π(f)` is of trace class.

Let `n = 0`. The ring of `0 × 0` matrices has one element, so `G∞` is the trivial group
for every `F`, and the index formula above does not apply (for `F = ℚ` it would give
`2`). A left Haar measure `μ` is a positive multiple of the point mass at `1`. Every
subspace is invariant, so an irreducible unitary representation `π` acts on a
one-dimensional space `E` (in dimension at least `2`, the line through a nonzero vector
is a closed proper nonzero subspace), and `π(1)` is the identity. The integrated operator
is `π(f) = f(1) μ({1}) · id_E`, an operator on a one-dimensional space, hence of trace
class. Knapp says that his definition "may or may not make an exception for the
trivial one-element group" (printed p. 3); the case is elementary in any event.

### Separation

Write `Θ_i(f) = tr σ i(f)` and `Θ(f) = tr π(f)`; by the trace-class theorem these are
traces of trace-class operators. For test functions put `f*(g) = conj f(g⁻¹)` and
`(f₁ * f₂)(g) = ∫ f₁(h) f₂(h⁻¹ g) dμ(h)`; both are again smooth and compactly
supported. For a unitary representation `ρ` one has `ρ(f₁ * f₂) = ρ(f₁) ρ(f₂)` and,
since `G∞` is unimodular, `ρ(f*) = ρ(f)*`. Hence
`tr ρ(f* * f) = ‖ρ(f)‖²_HS ≥ 0`, the square of the Hilbert–Schmidt norm.

1. Let `J` be the set of `i` with `σ i` unitarily equivalent to `π`. For `i ∈ J`,
   `σ i(f)` is conjugate to `π(f)` by a unitary operator, so `Θ_i = Θ`. Choose `h` with
   `π(h) ≠ 0`; an approximate identity in `C_c^∞(G∞)` and strong continuity give one.
   Then `Θ(h* * h) = ‖π(h)‖²_HS > 0`. Restricting the absolutely summable family of
   hypothesis 5 for `h* * h` to `J` shows that `(c i)_{i ∈ J}` is absolutely summable;
   let `C` be its sum. Removing `J`, for every `f` the family `c i Θ_i(f)` over `i ∉ J`
   has sum `d Θ(f)` with `d = c₀ − C`.
2. Fix a unit vector `x ∈ E`. For `i ∉ J` choose an orthonormal basis `(e_{i,γ})` of
   `H i` and put `x_{i,γ} = |c i|^{1/2} e_{i,γ}`. For every `f`,
   `∑_{i,γ} ‖σ i(f) x_{i,γ}‖² = ∑_{i ∉ J} |c i| ‖σ i(f)‖²_HS = ∑_{i ∉ J} |c i Θ_i(f* * f)|`,
   which is finite by step 1. The remark in the proof of Jacquet–Langlands,
   Lemma 16.1.1 then gives: for every `ε > 0` there is a test function `f` with
   `∑_{i ∉ J} |c i| ‖σ i(f)‖²_HS < ε ‖π(f) x‖²`. Its proof, for the
   translation-invariant algebra `C_c^∞(G∞)`, runs as follows. Otherwise the vectors
   `v_f = (σ i(f) x_{i,γ})` of the Hilbert direct sum `⊕_{i,γ} H i` satisfy
   `‖π(f) x‖² ≤ ε⁻¹ ‖v_f‖²`, so `v_f ↦ π(f) x` extends to the closure of the `v_f`.
   This closure is invariant, because `σ i(g) σ i(f) = σ i(f(g⁻¹ ·))` by left invariance
   of `μ`. Extended by `0` on the orthogonal complement, the map is a bounded
   intertwiner from `⊕ σ i` to `π`; it is nonzero, since an approximate identity gives a
   test function `f` with `π(f) x ≠ 0`. Its restriction to each summand is an intertwiner
   from `σ i` to `π`, hence `0` by Schur's lemma, because `σ i` is not unitarily
   equivalent to `π`. (For irreducible unitary representations, `T* T` is a scalar for an
   intertwiner `T`, so a nonzero `T` is a positive multiple of a unitary equivalence.)
   So the map vanishes on a dense subspace, which is a contradiction.
3. If `d ≠ 0`, take `ε = |d| / 2` and `f` as in step 2. Then `‖π(f) x‖ > 0`, and
   hypothesis 5 at `f* * f` gives
   `|d| ‖π(f)‖²_HS ≤ ∑_{i ∉ J} |c i| ‖σ i(f)‖²_HS < (|d|/2) ‖π(f) x‖² ≤ (|d|/2) ‖π(f)‖²_HS`.
   This is impossible, so `d = 0`: the `c i` over `J` have sum `c₀`. If `c₀ ≠ 0`, then
   `J` is not empty.

The argument uses neither infinitesimal characters nor `K∞`-types. It also does not use
Harish-Chandra's linear independence of the characters of infinitesimally inequivalent
irreducible admissible representations (Knapp, Theorem 10.6, printed p. 336).

## Provenance and sources

The four predicates express standard notions: unitary representation, topological
irreducibility, the integrated operator `∫ f(g) σ(g) dg`, and unitary equivalence. The
trace-class statement is Knapp's Theorem 10.2 for the group `G∞` when `n > 0`, through
the reduction to the identity component explained above; the case `n = 0` is the
elementary argument for the trivial group.

The separation statement is derived content formulated for the Library. Its motivating
special case is in Arthur–Clozel, Chapter 1, §4, printed pp. 42–44. There `k` is a
totally imaginary number field, so `G(k_v) = GL_n(ℂ)` at every infinite place `v`. The
automorphic spectra have a fixed central character, and the test functions are
compactly supported modulo the centre and transform under the centre by a fixed
character (pp. 42–43). At each infinite place they take associated test functions
`φ_v = (f_1, …, f_ℓ)` and `f_v = f_1 * ⋯ * f_ℓ`, an `ℓ`-fold convolution of smooth
functions (p. 43). On p. 44 they regard (4.6) as an identity of linear forms in these
associated functions at one infinite place `v`. They group the representations at `v`
and obtain an identity `∑ a_{π_v} trace π_v(f_v) = 0` ranging over unitary
representations of `G(k_v)`. They conclude that all `a_{π_v}` vanish "by a lemma of
Jacquet–Langlands (cf. [25, Theorem 5.2])", where [25] is Jacquet–Langlands,
*Automorphic Forms on GL(2)*.

Their conclusion has the form of the separation statement with pairwise inequivalent
indices. Move one term `a_{π_v} trace π_v(f_v)` to the right-hand side as `c₀ Θ_π`, with
`π = π_v` and `c₀ = −a_{π_v}`. Then no remaining index is equivalent to `π`, and the
separation statement gives `c₀ = 0`. Their conclusion is not a direct instance of the
proposition here. The proposition concerns the whole group `G∞ = GL_n(F ⊗ ℝ)` for an
arbitrary number field `F`, representations without a fixed central character, an
arbitrary index type, and an identity assumed, with absolute convergence, for every
`f ∈ C_c^∞(G∞)`. Their identity is available only for the convolutions
`f_1 * ⋯ * f_ℓ` at one place, in the central-character setting. A deduction of their
vanishing from the proposition would first have to extend their identity to that full
test space. Both conclusions rest on the separation argument of Jacquet–Langlands, which
the section on separation above follows. On printed pp. 45–46, finiteness of the cuspidal representations of a
given level and infinitesimal character reduces (4.7) to finitely many terms; the
Hecke-algebra separation at the finite place `v₀` is their Lemma 4.10.

The proof route above follows the remark inside the proof of Jacquet–Langlands,
Lemma 16.1.1. On retypeset p. 260 they define `L¹(η)`, `f*(g) = conj f(g⁻¹)`, ample
subalgebras (dense and closed under `f ↦ f*`) and `π(f) = ∫ f(g) π(g) dg`, and state
Lemma 16.1.1. The remark and its proof are on p. 261, and the rest of the proof is on
pp. 261–262. Here `G = G∞`, the central subgroup `Z` is trivial, and the algebra is
`C_c^∞(G∞)`.

The non-archimedean analogues in the Library are
`Langlands.TraceFormula.BoundedCharacterSeparationStatement` and
`Langlands.TraceFormula.CharacterTraceReplacementStatement`. They separate summable
identities by families of algebra characters under uniform bounds; the statement here
separates by the unitary equivalence class of an irreducible unitary representation of
`G∞`, without bound hypotheses.

## Sources

- James Arthur and Laurent Clozel, *Simple Algebras, Base Change, and the Advanced
  Theory of the Trace Formula*, Annals of Mathematics Studies 120, Princeton University
  Press, 1989. Literature ID `arthur-clozel-1989-base-change`, SHA-256
  `c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`. Chapter 1, §4:
  printed pp. 42–43 (PDF pp. 56–57), the central-character setting and the associated
  convolution test functions at the infinite places; printed p. 44 (PDF p. 58), from
  (4.6) to (4.7), the identity
  `∑ a_{π_v} trace π_v(f_v) = 0` and the vanishing of the `a_{π_v}`; printed pp. 45–46
  (PDF pp. 59–60), the finiteness remark and Lemma 4.10.
- Hervé Jacquet and Robert P. Langlands, *Automorphic Forms on GL(2)*, Lecture Notes in
  Mathematics 114, Springer, 1970, retypeset edition. Literature ID
  `jacquet-langlands-1970-automorphic-forms-gl2`, SHA-256
  `4dae9de4ce65b6ed81a8ec4688e1f65131f188ba33195d5cf066cd923eabef0a`. Chapter 3, §16:
  retypeset p. 260 (PDF p. 264), the definitions and the statement of Lemma 16.1.1;
  retypeset pp. 261–262 (PDF pp. 265–266), the remark and the proof.
- Anthony W. Knapp, *Representation Theory of Semisimple Groups: An Overview Based on
  Examples*, Princeton Mathematical Series 36, Princeton University Press, 1986.
  Literature ID `knapp-1986-representation-theory-semisimple-groups`, SHA-256
  `a8ae5776789005035f477f7ea79ee4a268ad43b2d84a607d55b4bedf763dbe75`. Chapter I, §1,
  printed p. 3 (PDF p. 17), linear connected reductive groups; Chapter VIII, §2,
  Theorem 8.1, printed p. 205 (PDF p. 219); Chapter X, §1, printed p. 333 (PDF p. 347),
  trace class, Lemma 10.1 and global characters, and Theorem 10.2, printed p. 334
  (PDF p. 348); Theorem 10.6, printed p. 336 (PDF p. 350).
