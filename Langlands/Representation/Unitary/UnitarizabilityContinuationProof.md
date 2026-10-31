# Proof: continuation of unitarizability along a connected parameter set

Author: Worker 1023. Submitted by Worker 246 for the proof task
`7071b052-61cb-4718-babc-684a3e41c288`. Worker 246 re-checked the Lean
file and the import audit below at Library commit `90334e87`.

This module proves

```lean
theorem Langlands.unitarizabilityContinuation :
    UnitarizabilityContinuationStatement.{uG, uV}
```

with independent universes `uG, uV` and no further hypotheses. The proposition
is the published statement in
`Langlands.Representation.Unitary.UnitarizabilityContinuationStatement`. The
setting is a topological group `G`, a complex vector space `V`, a family
`π : ℝ → Representation ℂ G V`, a preconnected `J : Set ℝ`, and an open
subgroup `K` of `G` with compact underlying set. Assume:

- the members `π s` with `s ∈ J` agree on `K`;
- they are admissible and irreducible;
- each has a nonzero invariant sesquilinear form;
- every scalar `ℓ (π s g v)` is continuous on `J`.

Then unitarizability of one `π s₀` with `s₀ ∈ J` implies unitarizability of
every `π s` with `s ∈ J`.

## Mathematical source

The statement is a derived formulation of the soft step in the proof of
Zelevinsky 1980, Proposition 1.11, printed p.175 (PDF p.12) (literature
`zelevinsky-1980-induced-ii`): "One can derive from these facts that all
`B_s` are positive hence all `π_s` are unitary." Zelevinsky gives no further
detail. The Lean proof is a complete argument by its author. It follows the route
recorded in the statement's Markdown, with three changes:

1. The projection onto fixed vectors is the Library's normalized Hecke
   indicator projection, defined with a Haar measure. Orbit averaging is not
   used.
2. The continuation is run on the set of parameters with a positive definite
   invariant matrix, not on signs of a chosen Hermitian form.
3. Signs are made consistent across fixed-vector spaces by normalizing at one
   fixed nonzero vector `w0`.

## Implemented proof

All helpers are in the namespace `Langlands.UnitarizabilityContinuation`.

### Matrix families (section `MatrixFamily`)

Let `n` be a finite index type and `A : G → Matrix n n ℂ`.

- `IsInvariantMatrix A B` means `(A g)ᴴ * B = B * A g⁻¹` for all `g`.
  Invariant matrices are closed under sums, scalar multiples, negation,
  subtraction and conjugate transpose (`IsInvariantMatrix.add`, `.smul`,
  `.neg`, `.sub`, `.conjTranspose`).
- `IsIrreducibleFamily A`: every subspace of `n → ℂ` stable under all
  `A g *ᵥ ·` is `⊥` or `⊤`.
- `quad H x` is the real part of `xᴴ H x`. `IsPos H` means that `H` is
  Hermitian and `quad H x > 0` for every `x ≠ 0`. `vec H` is the underlying
  function `n → n → ℂ`, used for the sup norm.

Schur's lemma for an irreducible family:

- `eq_zero_of_mulVec_eq_zero`: a nonzero invariant `B` has trivial kernel.
  The kernel is stable under all `A g`, because
  `B * A g = (A g⁻¹)ᴴ * B`, and `ker B = ⊤` would force `B = 0`.
- `exists_eq_smul_of_invariant`: if `H ≠ 0` and `B` are invariant, then
  `B = c • H` for some `c`. `H` is invertible by the previous item. Take an
  eigenvalue `c` of `H⁻¹ * B` (complex numbers are algebraically closed,
  `Module.End.exists_eigenvalue`). Then `B - c • H` is invariant and has a
  nonzero kernel vector, so it is zero.
- `exists_hermitian_invariant`: a nonzero invariant `B` gives a nonzero
  Hermitian invariant matrix, either `B + Bᴴ` or, if that is zero, `i • B`.
- `isPos_of_nonneg`: a nonzero Hermitian invariant `H` with `quad H ≥ 0` is
  positive definite. `H` is positive semidefinite (Mathlib's `PosSemidef`),
  so `xᴴ H x = 0` gives `H x = 0`, hence `x = 0` by
  `eq_zero_of_mulVec_eq_zero`.

Continuation. Now let `A : ℝ → G → Matrix n n ℂ` with each `s ↦ A s g`
continuous on `J`, each `A s` (`s ∈ J`) irreducible with a nonzero invariant
matrix, and `n` nonempty. Let `D` be the set of `s ∈ J` with a positive
definite invariant matrix for `A s`.

- `isInvariantMatrix_of_tendsto`, `isHermitian_of_tendsto`, `tendsto_quad`:
  invariance, the Hermitian property and `quad` pass to limits along
  sequences of parameters in `J` converging in `J`.
- `mem_of_mem_closure`: a parameter `t ∈ J` in the closure of `D` lies in
  `D`. Pick `τ k ∈ D` with `τ k → t` and positive definite invariant `H k`.
  Rescale them by positive reals to sup norm one. By compactness of the unit
  sphere (`isCompact_sphere`, `IsCompact.tendsto_subseq`) a subsequence
  converges to some `H'` of norm one. `H'` is nonzero, Hermitian, invariant
  for `A t`, and satisfies `quad H' ≥ 0`. It is positive definite by
  `isPos_of_nonneg`.
- `not_mem_closure_compl`: a parameter `t ∈ D` is not in the closure of
  `J \ D`. Suppose `τ k ∈ J \ D` with `τ k → t`. Each `A (τ k)` has a nonzero
  Hermitian invariant `H k`. By `isPos_of_nonneg`, applied to `H k` and to
  `-H k`, `H k` takes a negative value `quad (H k) (x k) < 0` and a positive
  value `quad (H k) (y k) > 0`. Normalize `H k`, `x k` and `y k` to norm one
  and pass to a convergent subsequence `(H', x', y')` in a product of unit
  spheres. Then `H'` is a nonzero Hermitian invariant matrix for `A t` with
  `quad H' x' ≤ 0 ≤ quad H' y'`. By Schur, `H' = c • H0` for the positive
  definite invariant `H0` at `t`. Since `H'` is Hermitian, `c` is real. Then
  `c · quad H0 x' ≤ 0 ≤ c · quad H0 y'` with `quad H0 x'`, `quad H0 y'` > 0,
  so `c = 0`. This contradicts `‖H'‖ = 1`.
- `exists_isPos_of_isPreconnected`: if `s₀ ∈ D`, then every `s ∈ J` lies in
  `D`. The closed sets `closure D` and `closure (J \ D)` cover `J` and, by the
  previous two items, do not meet inside `J`. Preconnectedness
  (`isPreconnected_iff_subset_of_disjoint_closed`) puts `J` in one of them,
  and `s₀ ∈ D` excludes `closure (J \ D)`.
- `matrix_ext_form`: two matrices with the same forms `xᴴ M y` are equal.

### Representations (sections `Irreducible` to `LocalScalar`)

- The existing `Langlands.Hecke.submodule_eq_bot_or_eq_top_of_isIrreducible`
  from [CornerDetermination](../Hecke/CornerDetermination.md) supplies the stable
  submodule dichotomy for an irreducible `Representation`.
  `exists_ne_zero_of_isIrreducible` shows that its carrier has a nonzero vector.
- `positiveFormSesq ip`: the sesquilinear map
  `V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ` of an `InvariantPositiveForm`. It is invariant
  (`positiveFormSesq_invariant`), and `positiveForm_re_pos` gives
  `0 < re ⟪v, v⟫` for `v ≠ 0`.
- `gram e b`: the Gram matrix `b (e i) (e j)` of a sesquilinear form `b` on
  a basis `e` of the `L`-fixed vectors `fixedVectors ρ L`. By `gram_form`,
  `b (Σ xᵢ eᵢ) (Σ yⱼ eⱼ) = xᴴ (gram e b) y`. `gram_isPos`: the Gram matrix of
  a positive form is positive definite.

The section `FixedSpace` fixes a Haar measure `μ`, a smooth `ρ`, and a
compact open subgroup `L`. `P = Hecke.fixedProjection μ ρ hρ L hL` is the
action of the normalized indicator of `L`, with values in the `L`-fixed
vectors. It is the identity on them (`Hecke.fixedProjection_fixed`). Let
`σ` be any representation on `V` agreeing with `ρ` on `L`.

- `dual_fixedProjection`: an `L`-invariant linear functional `f` satisfies
  `f (P v) = f v`. By `Hecke.integratedAction_dual`, `f (P v)` is the integral
  of `μ(L)⁻¹ 1_L(g) f (ρ g v) = μ(L)⁻¹ 1_L(g) f v`, which equals `f v`
  (`integral_indicator_const`).
- `form_fixedProjection_left/right`: for a `σ`-invariant sesquilinear `b`
  and an `L`-fixed `w`, `b (P v) w = b v w` and `b w (P v) = b w v`. Apply
  `dual_fixedProjection` to `v ↦ conj (b v w)` and to `b w`, which are
  `L`-invariant because `σ = ρ` on `L` and `w` is `ρ(L)`-fixed.
- `fixedMatrix μ hρ hL e σ g`: the matrix of `P σ(g)` restricted to `L`-fixed
  vectors, in the basis `e` (`fixedMatrix_mulVec`,
  `coe_fixedProjection_symm`).
- `gram_isInvariant`: for `σ`-invariant `b`, `gram e b` is an invariant
  matrix of `g ↦ fixedMatrix … σ g`. Both sides of the invariance equation,
  evaluated on fixed vectors `u, w`, equal `b (σ g u) w`, by the previous
  item and invariance of `b`. Then use `matrix_ext_form`.
- `fixedMatrix_isIrreducible`: if `σ` is irreducible, this matrix family is
  irreducible. For a stable subspace `U ∋ x ≠ 0`, the submodule
  `S = {v | ∀ g, coordinates of P σ(g) v lie in U}` is `σ`-stable and contains
  the fixed vector with coordinates `x`. Hence `S = ⊤`. Taking `g = 1` and
  fixed vectors shows `U = ⊤`.
- `gram_ne_zero`: if `σ` is irreducible, `b ≠ 0` is `σ`-invariant, and some
  `L`-fixed `w0 ≠ 0` exists, then `gram e b ≠ 0`. The right radical
  `{v | ∀ x, b x v = 0}` is a `σ`-stable submodule. It is not `⊤` since
  `b ≠ 0`, so it is `⊥` and some `x` has `b x w0 ≠ 0`. Then
  `b (P x) w0 = b x w0 ≠ 0`, and `P x`, `w0` are fixed vectors, so the Gram
  matrix is nonzero.

`exists_local_scalar` (section `LocalScalar`) brings these together for the
family `π`. Let `L ≤ K` be compact open, assume `fixedVectors (π s₀) L` is
finite-dimensional, and let `w0 ≠ 0` be `L`-fixed. Equip `G` with its Borel
σ-algebra and take `μ = haarMeasure L` (positive compact set `L`). With
`e = Module.finBasis`, the matrices `A t g = fixedMatrix μ hsm hL e (π t) g`
satisfy the hypotheses of `exists_isPos_of_isPreconnected`:

- the index type is nonempty because `w0 ≠ 0`;
- each `π t` agrees with `π s₀` on `L ≤ K`;
- `A t` is irreducible by `fixedMatrix_isIrreducible`;
- it has the nonzero invariant matrix `gram e b_t` by `gram_ne_zero` and
  `gram_isInvariant`;
- each entry of `A t g` is `ℓ (π t g (e j))` for the linear functional
  `ℓ = (i-th coordinate) ∘ P`, hence continuous on `J`;
- at `s₀` the Gram matrix of the given positive form is positive definite
  (`gram_isPos`).

So `A s` has a positive definite invariant `H`. By Schur,
`gram e b = c • H` with `c ≠ 0` (`gram e b ≠ 0`). The conclusion is that
`c⁻¹ b` is Hermitian and positive definite on the `L`-fixed vectors.

### Main theorem

Fix `s ∈ J`, a nonzero `π s`-invariant `b`, and a nonzero vector `w0`
(irreducibility of `π s₀`). Let `q x y = (b w0 w0)⁻¹ * b x y`. Given `x, y`,
let `L = K ⊓ H0 ⊓ H1 ⊓ H2`, where the open subgroups `H0, H1, H2` fix `w0, x,
y` (smoothness of `π s₀`). `L` is compact (closed in `K`), and `w0, x, y`
are `L`-fixed. Admissibility of `π s₀` gives finite dimension. So
`exists_local_scalar` gives `c` with `c * b w0 w0` real and positive,
`conj (c * b y x) = c * b x y`, and `re (c * b x x) > 0` if `x ≠ 0`. By
`inv_mul_eq_mul_ofReal`, `q x y = c * b x y / (c * b w0 w0)`, a positive real
multiple of `c * b x y`. So `q` is Hermitian on `x, y` and positive at `x`.
These identities hold for all `x, y`, so `q` is an `InvariantPositiveForm`
of `π s`: additivity and conjugate-linearity in the first argument come from
`b`, and invariance from invariance of `b`. The normalization at the one
vector `w0`, which is fixed by every `L` used, removes any sign or scalar
ambiguity between different subgroups `L`.

## Lean details

- No `sorry`, `admit`, new axioms or theorem-valued hypotheses occur.
- The proof uses the Library's Hecke projection
  (`Langlands.Hecke.fixedProjection`, `Hecke.fixedProjection_apply`,
  `Hecke.fixedProjection_fixed`, `Hecke.heckeAction_apply`,
  `Hecke.integratedAction_dual`, `Hecke.HeckeAlgebra.normalizedIndicator_apply`,
  `Hecke.HeckeAlgebra.compactOpen_complex_mass_ne_zero`) and Mathlib's
  Haar measure, finite-dimensional linear algebra, positive semidefinite
  matrices and compactness of spheres in finite-dimensional normed spaces.
  No local compactness or Hausdorff assumption is added: the Hecke API needs
  only a Haar measure, built from the positive compact set `L`.
- The helper names are public in the namespace
  `Langlands.UnitarizabilityContinuation`. They do not clash with Library
  names.

## Independence audit

Imports at submission: the statement module
`Langlands.Representation.Unitary.UnitarizabilityContinuationStatement`,
`Langlands.Representation.Hecke.ActionProjection`, and Mathlib.

The transitive closure of these imports at submission had 18 `Langlands`
modules including the statement module. The same 18 modules were found at
commits `a3027c81` and `90334e87`:

- `Group.GL.Basic`, `Group.GL.UpperUnipotent`;
- `HarmonicAnalysis.Basic`, `HarmonicAnalysis.AlgebraicIntegrand`,
  `HarmonicAnalysis.AlgebraicIntegral`;
- `Representation.Conductor.Congruence`, `Representation.RankinSelberg.Measures`;
- `Representation.Hecke.TestFunction`, `.Convolution`, `.NormalizedIndicator`,
  `.ActionIntegrand`, `.IntegratedAction`, `.IntegratedConvolution`,
  `.ActionProjection`;
- `Representation.Smooth.Definitions`, `Representation.Smooth.FixedVectors.Definitions`;
- `Representation.Unitary.Basic`, `Representation.Unitary.UnitarizabilityContinuationStatement`.

I searched all 18 modules. None declares or mentions any of the following:

- `SegmentSpecialEssentialSquareIntegrability`
- `SquareIntegrableLanglandsClassification`
- `GenericSegmentProductUniqueness`
- `OrderedMultisegmentSocleExistence`
- `MultisegmentSocleExhaustion`
- `SegmentSocleProductIrreducibility`
- `SegmentFullJacquetFormula`, `SegmentHeadJacquetFormula`,
  `SegmentSocleJacquetFormula`
- `SegmentSpecialJacquetExponentNormFormula`
- `TwoSupercuspidalAdjacentProductReducible`

None of them contains `Segment`, `Jacquet`, `Supercuspidal`,
`Classification`, `StrongHead`, `QuotientCoverage`, `OrderedConversion`,
`TemperedUniqueness`, `SquareIntegrab`, `Derivative` or `Exhaustion`. So no
module in the closure belongs to any task on the contract's independence
list:

- special-head/reverse-socle existence (`67279e36`) and
  segment-socle/reverse-head existence (`4ca79bbd`);
- analytic segment classification (`aca8805b`) and forward special
  square-integrability (`5eece9e8`);
- multisegment special-head exhaustion (`3bfb61fa`), ordered strong-head
  existence (`ebea9a8a`), quotient coverage (`20e4e1c6`) and ordered
  conversion (`8252833d`);
- tempered uniqueness (`52e97845`), the square-integrable Langlands
  classification (`1cb45da2`), square-integrable exhaustion (`cd8ab97c`) and
  regular exhaustion (`bf433f0a`);
- special-head product irreducibility (`8364e73f`) and adjacent socle
  commutation (`e3634665`);
- generic segment product uniqueness (`30341ae4`), ordered multisegment socle
  existence (`23189526`), multisegment socle exhaustion (`f3a69bc8`) and
  segment-socle product irreducibility (`2ae5cbe5`);
- the segment Jacquet formulas (`ed48ae06` and its proof successor,
  `55ad1e10`, `b95105c6`, `92aea10f`);
- adjacent reducibility (task `0988a3e0-a086-474d-b2d2-7e53902b43cb`).

Mathematical dependencies are general:

- linear algebra over `ℂ` (eigenvalues, positive semidefinite matrices);
- compactness of spheres and preconnectedness of `J`;
- Haar measure on a group with a compact open subgroup;
- the Hecke projection onto fixed vectors.

The proof uses no derivative formula (Ze80 §3.5, §9.6, BZ77), no segment
product irreducibility criterion (Ze80 4.2, 9.7), no analytic or
square-integrability result (Ze80 9.3), and no classification or exhaustion
theorem. It does not use the adjacent reducibility task or its target. That
task is downstream: it uses this theorem.

Integration reuses the existing stable-submodule dichotomy from
`Langlands.Representation.Hecke.CornerDetermination` and removes the duplicate
helper. The integrated import closure has 21 `Langlands` dependencies (excluding
this proof module): the 18 listed above and `Representation.Hecke.Corner`,
`Representation.Hecke.CornerAction`, and `Representation.Hecke.CornerDetermination`.
The three additional modules contain none of the excluded declarations or topic
names listed above. The final theorem and its hypotheses are unchanged.
