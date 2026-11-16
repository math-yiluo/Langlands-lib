# Column periods as torus integrals

Module `Langlands.Global.RankinSelberg.WhittakerExpansionCore.ColumnTorus`, namespace
`Langlands.Global.RankinSelbergGlobal.Unfolding`. A helper module for half (E) of the
Whittaker expansion (see `Interface`). It is internal to this proof, not taken from the
literature. It links two descriptions of the period along one unipotent column that are
already in the Library:

* the normalized integral over the chosen fundamental domain of `V_(j+1)(F)` in
  `V_(j+1)(𝔸)`, used by the projection coefficients (`ProjectionColumns`,
  `ProjectionExpansion`);
* the torus integral `torusIntegral` over `(𝔸/F)^(r+1)` of the library column Fourier
  framework (`Automorphic.CuspidalWhittaker.Columns`, `QuotientTorus`).

Here `V_(j+1) = columnUnipotent F r j` (for `j < r`) is the group of matrices `1 + X` where `X`
has entries only in rows `0, …, j` of column `j + 1`. `colPoint c` is the adelic point of
`1 + colMatrix j c`, and `colVec` gives back the column vector of a point of `V_(j+1)(𝔸)`.

## Column points

* `colPoint_add`: `colPoint (c + d) = colPoint c * colPoint d`.
* `colMatrix_truncVec`, `colPoint_truncVec`: a column point only depends on the coordinates
  `0, …, j` (`truncVec (j + 1)` sets the others to `0`).
* `colPoint_colVec`: `colPoint (colVec m) = m` for `m ∈ V_(j+1)(𝔸)`.
* `colVec_colPoint`: `colVec (colPoint c) = truncVec (j + 1) c`.
* `truncVec_colVec`: `colVec m` is already truncated.
* `adelicEquiv_colPoint`, `colPoint_eq_symm_colUnit`: in matrix coordinates `colPoint c` is the
  column unit `colUnit (colIdx j hj) c` of the torus framework.
* `continuous_colPoint`: `colPoint` is continuous.

## Characters

For `a ∈ F^Idx`, `pairingCharacter a y = ψ₀(Σ_i a_i y_i)` is the library character of
`𝔸^Idx` that is trivial on `F^Idx`.

* `pairingCharacter_truncVec`: `pairingCharacter a (truncVec m y) =
  pairingCharacter (truncVec m a) y`.
* `pairingCharacter_ratVec`: a character is `1` at rational vectors.
* `torusIntegral_pairingCharacter` (with `CompactSpace (AdeleQuotient F)`): for `a ≠ 0`,
  `torusIntegral Idx (pairingCharacter a) = 0`. Proof: pick `i` with `a_i ≠ 0` and `x₀` with
  `ψ₀(x₀) ≠ 1` (`exists_adelicCharacter_ne_one`). Translating by `t = Pi.single i (a_i⁻¹ x₀)`
  multiplies the character by `ψ₀(x₀)` and leaves the torus integral unchanged
  (`torusIntegral_add_right`). So `I ψ₀(x₀) = I`, hence `I = 0`.

## The bridge

* `truncHom r j`: `truncVec (j + 1)` as an additive endomorphism of `𝔸^(r+1)`. It is
  continuous (`continuous_truncHom`) and maps rational vectors to rational vectors
  (`preservesRational_truncHom`), so it descends to a continuous map `τ` of the torus
  (`torusMap`).
* `normalized_setIntegral_column_eq_torusIntegral hj h hc hper`: let `j < r` and
  `h : GL_(r+1)(𝔸) → ℂ`, and let `y ↦ h(colPoint y)` be continuous (`hc`) and
  `F^(r+1)`-periodic (`IsPeriodic`, `hper`). No continuity of `h` itself is needed. Write `ν` for the Haar measure of `V_(j+1)(𝔸)` and `E` for the chosen
  fundamental domain. Then

  `ν(E)⁻¹ • ∫_E h(m) dν(m) = torusIntegral (Fin (r+1)) (y ↦ h(colPoint y))`.

### Proof of the bridge

1. The quotient `V_(j+1)(F) \ V_(j+1)(𝔸)` is compact (`compactSpace_columnRationalQuotient`),
   so `0 < ν(E) < ∞` (`haar_fundamentalDomain_ne_zero`, `haar_fundamentalDomain_ne_top`). Also
   the Haar measure is right invariant
   (`haar_isMulRightInvariant_of_compactRationalQuotient`).
2. Let `κ(m) = [colVec m]` in the torus `(𝔸/F)^(r+1)`. On the space `C(T)` of continuous
   functions on the torus define two continuous linear functionals:
   `L₁(p) = ∫_E p(κ m) dν(m)`, which has norm at most `ν(E)`, and
   `L₂(p) = ∫_T p(τ t) dt`, which has norm at most `1` because the torus Haar measure is a
   probability measure. Let `D = L₁ − ν(E) L₂`.
3. `D` vanishes on every torus character `χ_a` (`torusCharacterMap`):
   * `χ_a(κ m) = pairingCharacter a (colVec m)` and
     `χ_a(τ t) = pairingCharacter (truncVec (j+1) a) (lift t)`.
   * If `truncVec (j + 1) a = 0`, both characters are `1`, so `L₁ = ν(E) = ν(E) L₂`.
   * Otherwise `L₂(χ_a) = 0` by `torusIntegral_pairingCharacter`. Also
     `m ↦ pairingCharacter a (colVec m)` is a character of `V_(j+1)(𝔸)` (`colVec_mul`),
     trivial on rational points (`colVec_rational`, `pairingCharacter_ratVec`), and not
     identically `1`: at `m₀ = colPoint (Pi.single i (a_i⁻¹ x₀))` with `i ≤ j`, `a_i ≠ 0`,
     its value is `ψ₀(x₀) ≠ 1`. Hence `L₁(χ_a) = 0` by the library orthogonality
     `LeftCosetSpace.Semidirect.setIntegral_fundamentalDomain_character_eq_zero`.
4. So the span of the characters lies in the closed subspace `ker D`, and the closure of that
   span is all of `C(T)` (`span_torusCharacterMap_closure_eq_top`). Hence `D = 0`.
5. Apply `D = 0` to `P = (y ↦ h(colPoint y)) ∘ lift`, which is continuous on the torus because
   the function is periodic and continuous (`IsPeriodic.continuous_lift`).
   Then `P(κ m) = h(colPoint (colVec m)) = h(m)` (`colPoint_colVec`). Also
   `P(τ t) = h(colPoint (truncVec (j+1) (lift t))) = h(colPoint (lift t))`
   (`colPoint_truncVec`). So `∫_E h dν = ν(E) · torusIntegral (y ↦ h(colPoint y))`. Dividing by
   `ν(E) ≠ 0` gives the claim.
