# The operators `M(w, λ) : H_P → H_{P'}` from unitarity on `A^2_P`

Module `Langlands.Global.AdelicImaginaryIntertwiningExistence` states and proves the
proposition `Langlands.Global.ImaginaryIntertwiningExistenceBridgeStatement`:

`IntertwiningImaginaryUnitarityStatement → InducedRestrictionMemLpStatement →
ImaginaryIntertwiningExistenceStatement`.

The three propositions are:

- `IntertwiningImaginaryUnitarityStatement`, published in module
  `Langlands.Global.AdelicIntertwiningImaginaryUnitarityStatement`. It is the
  unitarity of `M(w, λ)` on `A^2_P` for `λ ∈ i𝔞_P^*`, in Gram-matrix form
  (Lapid 2011, §2, p.312; Mœglin–Waldspurger IV.1.11 (b), IV.3.12, VI.2.1 (i)).
- `InducedRestrictionMemLpStatement`, in module
  `Langlands.Global.AdelicInducedRestrictionMemLpStatement`. It says that the
  restriction `(k, m) ↦ φ(mk)` of every `φ ∈ A^2_P` is square integrable for the
  measure `inducedL2Measure` that defines `H_P`.
- `ImaginaryIntertwiningExistenceStatement`, in module
  `Langlands.Global.AdelicSpectralTransformInputs`. It is one of the inputs of
  the reduction of `SpectralTransformStatement`. It asserts that a family of
  continuous linear operators `Mop x : H_P → H_{P'}` exists, for `λ = i e(x)`,
  satisfying `IsImaginaryIntertwiningOperator`. That predicate says that
  `Mop x` maps the class of `v ∈ A^2_P` to the class of the value at `i e(x)`
  of every finite expansion `∑ q, coeff q λ • ψ q` of `M(w, λ) v`. Mathematically
  this is Arthur 2005, Theorem 7.2 (a), on the imaginary axis.

The bridge is a theorem about these three Library propositions. It claims
nothing about whether its premises hold; their proofs are separate tasks.

## Provenance

The bridge is internal to the Library: it connects the published unitarity
statement with the input `ImaginaryIntertwiningExistenceStatement` of the
reduction of the spectral transform (task `Langlands.Global.SpectralTransformStatement`,
Arthur 2005 Theorem 7.2 (b), Getz–Hahn (10.22)–(10.24)). Lapid 2011, p.312
says: "`M(w, λ)` is unitary, hence holomorphic, and therefore extends to a
unitary operator on `Ind_{P(𝔸)}^{G(𝔸)} L²_disc(A_M M \ M(𝔸))`". Lapid and
Arthur obtain that unitary extension from the continuation on a dense
inducing subspace. The bridge proves less. It gives, for each `x`, a bounded
complex-linear map `Mop x : H_P → H_{P'}` that satisfies
`IsImaginaryIntertwiningOperator`: `Mop x` sends the class of `v` to the
class of `∑ q, coeff q (i e(x)) • ψ q` for every admissible finite expansion
of `M(w, λ) v` that is supplied. The construction (step 6 below) uses the
relation `Rel x` of pairs of classes coming from such expansions. `Mop x` is
an isometry on the closure of the span of `{h | ∃ h', (h, h') ∈ Rel x}` and
zero on the orthogonal complement of that closure. The bridge does not prove
that this closure is all of `H_P`. That would need admissible expansions for a
spanning set of classes dense in `H_P`, and neither premise supplies them.
The premise `InducedRestrictionMemLpStatement` is needed because the Gram
identity controls only the inner products `(·,·)_P`, which are integrals over
`K × M(F) \ M(𝔸)` of `β(y(m)) δ_P(m)⁻¹ φ(mk) conj(ψ(mk))`. It does not by
itself put the restrictions into `L²`.

## Declarations

### Meromorphy (section `Meromorphic`)

- `isMeromorphicOn_inter`: a meromorphic function on `ℂⁿ` with domain of
  holomorphy `U` (`IsMeromorphicOn`) is meromorphic with domain of holomorphy
  `U ∩ V` for every open dense `V`. `U ∩ V` is open and dense, holomorphy
  restricts, and the local quotient representations `g • f = h` on `U ∩ W`
  restrict to `U ∩ V ∩ W`.
- `isMeromorphicInCoordinatesOn_inter_of`: if `f` is meromorphic in
  coordinates with domain `U` and some `g` is meromorphic in coordinates with
  domain `V`, then `f` is meromorphic in coordinates with domain `U ∩ V`. In
  every chart `e`, `e⁻¹' V` is open and dense because `g ∘ e` is meromorphic
  with that domain.
- `isMeromorphicInCoordinatesOn_zero_of`: the zero function is meromorphic in
  coordinates on every domain of holomorphy `V` of some meromorphic `g`. The
  local quotient is `1 • 0 = 0` on `W = ℂⁿ`.
- `exists_domain_of_isMeromorphicInCoordinatesOn`: for finitely many
  coefficients `c q`, all meromorphic in coordinates with domain `DM`, there is
  a domain `D ⊇ DM` on which they are all meromorphic and such that
  intersecting with `D` preserves meromorphy in coordinates. Take `D = DM` if
  the family is nonempty, by the previous lemma applied to `c 0`, and `D` the
  whole space if it is empty.

### Coordinates (section `Coordinates`)

- `exists_transported_coordinates`: let `e : ℝⁿ ≃ X^*(P) ⊗ ℝ` and
  `e' : ℝⁿ ≃ X^*(P') ⊗ ℝ` be coordinates, `L : X^*(P) ⊗ ℝ → X^*(P') ⊗ ℝ`
  linear, and `β'` a continuous, compactly supported, nonnegative weight with
  `∫ β' = 1`. Suppose `τ = e'⁻¹ ∘ L ∘ e` preserves Lebesgue measure. Then
  `e'' = L ∘ e` is again a linear isomorphism `ℝⁿ ≃ X^*(P') ⊗ ℝ`. There is a
  weight `β''` with the same four properties such that
  `β''(y_{e''}(H)) = β'(y_{e'}(H))` for every `H ∈ Hom(X^*(P'), ℝ)`, where
  `y_e(H) = parameterCoordinates F P' e H`. Proof:
  - `τ` is surjective (`surjective_of_measurePreserving_linearMap`), hence
    bijective, so `e'' = e' ∘ τ` (that is, `e'' x = e'(τ x) = L(e x)`) is an
    isomorphism;
  - the coordinates are related by `y_{e'}(H) = ρ(y_{e''}(H))`, where `ρ` is
    the transpose of the matrix of `τ⁻¹` (`linearForm_comp_single_eq_transpose`);
  - put `β'' = β' ∘ ρ`. Then `|det ρ| = |det τ|⁻¹ = 1`
    (`abs_det_eq_one_of_measurePreserving`, `det_toLin'_transpose_toMatrix'`),
    so `∫ β'' = ∫ β' = 1` (`integral_comp_linearMap_of_abs_det_eq_one`), and
    `β''` has compact support because `ρ` is a homeomorphism.

The helper lemmas cited here are in module
`Langlands.Analysis.MeasurePreservingLinearCoordinates`.

### The bridge

`ImaginaryIntertwiningExistenceBridgeStatement` is the implication displayed
above. Its proof `imaginaryIntertwiningExistenceBridge` runs as follows, for
the data of `ImaginaryIntertwiningExistenceStatement`.

1. The coordinate change `x ↦ e'⁻¹(w(e x))` is linear and preserves Lebesgue
   measure, so `n = n'` (`eq_of_measurePreserving_linearMap`).
   `exists_transported_coordinates`, with `L = w = realWeylParameter l cw π'`,
   gives coordinates `e'' = w ∘ e` and a weight `β''`. This is the coordinate
   compatibility `e'' x = w (e x)` that the unitarity statement requires.
   `inducedInnerProduct` for `(e'', β'')` and for `(e', β')` agree, because
   their integrands agree pointwise.
2. The unitarity statement needs `P'` to be a parabolic subgroup with rational
   Levi subgroup `l'`. Both facts come from the presentation `r'`
   (`r'.isCompatible.parabolic`, `r'.isCompatible.levi`).
3. Restrictions of elements of `A^2_{P'}` are in `L²` by the premise
   `InducedRestrictionMemLpStatement`, applied on the `P'` side.
4. For each `x ∈ ℝⁿ` let `Rel x ⊆ H_P × H_{P'}` be the set of pairs `(h, h')`
   such that, for some `v ∈ A^2_P` and some expansion
   `M(w, λ) v = ∑ q, coeff q λ • ψ q` as in `IsImaginaryIntertwiningOperator`
   (with `ψ q ∈ A^2_{P'}`, and coefficients meromorphic in coordinates with a
   domain containing `i(X^*(P) ⊗ ℝ)`), `h` is a.e. equal to the restriction of
   `v` and `h'` is a.e. equal to the restriction of
   `∑ q, coeff q (i e(x)) • ψ q`.
5. Key step: for `(h_s, h'_s), (h_t, h'_t) ∈ Rel x`,
   `⟪h'_s, h'_t⟫ = ⟪h_s, h_t⟫`. The two expansions, for `v_s` and `v_t`, are put
   side by side in one family of `k = 2` vectors `![v_s, v_t]`. The common
   functions are `ψ2 = Fin.append ψ_s ψ_t`, and the coefficient rows are
   `Fin.append c_s 0` and `Fin.append 0 c_t`. The common domain is
   `D_s ∩ D_t` from `exists_domain_of_isMeromorphicInCoordinatesOn`. The zero
   coefficients are meromorphic there by
   `isMeromorphicInCoordinatesOn_zero_of`, and the side-by-side expansion
   agrees with the original ones (`Fin.sum_univ_add`). The unitarity statement,
   applied with `e''` and `β''`, gives coefficients `coeff'` and a domain
   `DM' ⊇ i(X^*(P) ⊗ ℝ)`. Let `λ₀ = i e(x)`; it lies in
   `D_s ∩ D_t ∩ DM'`. Then:
   - by the agreement on `D_s ∩ D_t ∩ DM'`, `h'_s` equals
     `∑ i, coeff' 0 i λ₀ • [ψ2 i]` in `L²` and `h'_t` equals
     `∑ i, coeff' 1 i λ₀ • [ψ2 i]` (`Lp.ext`, `sum_smul_toLp_mem_inducedHilbertSpace`);
   - `⟪[ψ2 i], [ψ2 i']⟫ = (ψ2 i', ψ2 i)_{P'}` and
     `⟪h_s, h_t⟫ = (v_t, v_s)_P` (`inner_eq_inducedInnerProduct`, module
     `Langlands.Global.AdelicInducedL2Inner`);
   - expanding `⟪h'_s, h'_t⟫` by sesquilinearity gives the Gram sum of the
     unitarity statement for `(j, j') = (1, 0)`, which equals `(v_t, v_s)_P`.
6. `exists_continuousLinearMap_of_inner_eq` (module
   `Langlands.Analysis.InnerProductGraphExtension`) gives, for each `x`, a
   continuous linear operator `Mop x : H_P → H_{P'}` with `Mop x h = h'` for
   every `(h, h') ∈ Rel x`. It applies because `H_P` and `H_{P'}` are closed
   subspaces of `L²` spaces, hence complete. By step 5 the span of the relation
   is the graph of an isometry defined on the span of the first projection
   `{h | ∃ h', (h, h') ∈ Rel x}`. The operator extends this isometry to the
   closure of that span and composes the extension with the orthogonal
   projection onto the closure. The proof does not identify the closure with
   `H_P`.
7. `IsImaginaryIntertwiningOperator` holds. Given `v`, an expansion, a class
   `h ∈ H_P` a.e. equal to the restriction of `v`, and `x`, the class of
   `∑ q, coeff q (i e(x)) • ψ q` lies in `H_{P'}` and is a.e. equal to its
   restriction (`sum_smul_toLp_mem_inducedHilbertSpace`). The pair of the two
   classes lies in `Rel x`, so `Mop x h` is that class.

The proof is a direct Lean proof with `maxHeartbeats 1000000`. Its axioms
are `propext`, `Classical.choice` and `Quot.sound`.
