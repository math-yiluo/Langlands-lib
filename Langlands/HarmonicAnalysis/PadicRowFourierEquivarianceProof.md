# P-adic row Fourier equivariance under general linear substitutions

Author: Worker 234.

The theorem
`Langlands.HarmonicAnalysis.padicRowFourierEquivariance`
proves exactly the published proposition
`Langlands.HarmonicAnalysis.PadicRowFourierEquivarianceStatement.{uF} F T d`
for every prime `p` with `[Fact p.Prime]`, every `F : PadicField.{uF} p`, every
supplied `T : F.TopologicalData`, and every `d : ℕ`, including `d = 0`. The
statement module and all modules it imports are unchanged.

For every unitary additive character `ψ`, every supplied scalar additive Haar
measure `ν`, every `g : Langlands.GeneralLinear d F.Carrier` and every
Schwartz–Bruhat function `Φ` on rows, the theorem proves two things. First, a
Schwartz–Bruhat function `Φg` with `Φg x = Φ (x ᵥ* g)` exists. Second, every
Schwartz–Bruhat function with that pointwise property satisfies, for every row
`y`,

```text
rowFourierIntegral ψ ν d Φg y =
  ((T.normalizedAbs (det g) : ℂ)⁻¹) *
    rowFourierIntegral ψ ν d Φ (y ᵥ* ((g⁻¹).val)ᵀ).
```

The proof adds no hypothesis. It uses no self-duality, Fourier closure or
inversion, integrability, or scalar or determinant Haar scaling assumption. It
derives the scaling laws from published Library theorems.

## Implemented proof

The change of variables is proved once for a general field and then
specialized. The section `General` works over a field `K` with a topological
ring structure, its Borel measurable structure, and a second-countable
topology. It also fixes a monoid-with-zero map `χ : K →*₀ ℝ≥0` and a supplied
`ν : AdditiveHaarMeasure K` with `SigmaFinite ν.measure`. Its only scaling
hypothesis is the scalar law

```text
hχ : ∀ a ≠ 0, ν.measure.map (fun x => a * x) = (χ a)⁻¹ • ν.measure.
```

1. **Row pairing.** `rowPairing_vecMul` proves
   `rowPairing (z ᵥ* A) y = rowPairing z (y ᵥ* Aᵀ)` for every square matrix
   `A`. The pairing is the dot product `∑ i, z i * y i`. Mathlib's
   `vecMul_transpose` rewrites `y ᵥ* Aᵀ` as `A *ᵥ y`, and `dotProduct_mulVec`
   gives `z ⬝ᵥ (A *ᵥ y) = (z ᵥ* A) ⬝ᵥ y`. The pairing stays bilinear, so the
   inverse transpose introduces neither a minus sign nor a complex
   conjugation.

2. **Determinant change of variables on rows.** `rowMeasure_map_vecMul` proves
   `(rowMeasure ν d).map (fun x => x ᵥ* g) = (χ (det g))⁻¹ • rowMeasure ν d`.
   By definition, `rowMeasure ν d` is `Measure.pi` of `ν.measure` in every
   coordinate. The published `productMeasure_map_matrix`, in
   `PadicRectangularHaarScalingProof`, gives the column-action version
   `(Measure.pi _).map (toLin' M) = (χ (det M))⁻¹ • Measure.pi _` for every `M`
   with nonzero determinant. It requires `SigmaFinite` and the additive
   left invariance supplied by the Haar instance of `ν.measure`. The proof
   applies it to `M = gᵀ`. Here `det gᵀ = det g` (`det_transpose`) is nonzero
   because `g` is a unit. The map `toLin' gᵀ` sends `x` to `gᵀ *ᵥ x`, which
   `mulVec_transpose` identifies with `x ᵥ* g`. So the column result becomes
   the right row action, with the same determinant factor.

3. **Fourier change of variables.** `rowFourierIntegral_vecMul` proves, for an
   arbitrary function `Φ : (Fin d → K) → ℂ`,

   ```text
   rowFourierIntegral ψ ν d (fun x => Φ (x ᵥ* g)) y =
     ((χ (det g) : ℂ))⁻¹ * rowFourierIntegral ψ ν d Φ (y ᵥ* ((g⁻¹).val)ᵀ).
   ```

   Put `h z = ψ.complex (rowPairing (z ᵥ* g⁻¹) y) * Φ z`. Since
   `(x ᵥ* g) ᵥ* g⁻¹ = x`, the left integrand is `h (x ᵥ* g)`. The map
   `x ↦ x ᵥ* g` is the published homeomorphism `rowHomeomorph g` in
   `RowSchwartzAction`. Hence it is a measurable embedding
   (`Homeomorph.measurableEmbedding`), and `MeasurableEmbedding.integral_map`
   rewrites the integral as `∫ h` against the pushforward measure. Step 2
   replaces the pushforward by `(χ (det g))⁻¹ • rowMeasure ν d`.
   `integral_smul_nnreal_measure` moves that nonnegative real scalar out of the
   Bochner integral, where it becomes multiplication by its complex coercion.
   Finally, step 1 with `A = g⁻¹` rewrites `h z` as
   `ψ.complex (rowPairing z (y ᵥ* (g⁻¹)ᵀ)) * Φ z`. This is the integrand of
   `rowFourierIntegral ψ ν d Φ` at `y ᵥ* (g⁻¹)ᵀ`. Neither the measurable
   embedding rule nor the scalar rule requires integrability, so the
   identity holds for every function. A non-integrable integrand gives zero on
   both sides.

4. **P-adic specialization.** `padicRowFourierEquivariance` installs exactly
   the statement's instances `T.topology`, `T.valuativeRel`, `T.localField`
   and the Borel measurable structure with its certificate. It also adds two
   published theorems about that same topology, `T.secondCountableTopology`
   and `T.sigmaCompactSpace` from `PadicScalarHaarScalingProof`. Second countability is needed
   by the general section. With σ-compactness, Mathlib infers
   `SigmaFinite ν.measure` from the Haar instance bundled in `ν`. None of
   these instances changes the topology or measurable structure in the
   statement.
   - *Existence of the pullback.* The witness is the published
     `rowTranslate g Φ`, the Schwartz–Bruhat pullback along `rowHomeomorph g`.
     `rowTranslate_apply` gives `rowTranslate g Φ x = Φ (x ᵥ* g)` by
     definition.
   - *Every pullback.* For any `Φg` with the pointwise property, function
     extensionality identifies its underlying function with
     `fun x => Φ (x ᵥ* g)`. The row Fourier integral depends only on that
     function, so `eq_rowTranslate_iff` is not needed.
   - *Scalar law.* For `a ≠ 0`, the published `padicScalarHaarScaling`,
     applied to `ν.measure` and the unit `Units.mk0 a ha`, gives
     `ν.measure.map (fun x => a * x) = (T.normalizedAbsHom a)⁻¹ • ν.measure`.
     This is `hχ` for `χ = T.normalizedAbsHom`. The general lemma then gives
     the target identity. The factor
     `(((T.normalizedAbsHom (det g) : ℝ≥0) : ℝ) : ℂ)⁻¹` agrees by definition
     with `((T.normalizedAbs (det g) : ℂ)⁻¹)`, because
     `T.normalizedAbsHom_coe` holds by `rfl`.

## Determinant normalization

The determinant factor is the residue-normalized absolute value of the
supplied realization, `T.normalizedAbs x = q ^ (-T.ord x)` for `x ≠ 0`, where
`q` is the residue cardinality. It enters only through
`padicScalarHaarScaling`, which proves the scalar law for this absolute value.
The product theorem then turns that law into the determinant law. No spectral
norm or unnormalized absolute value appears. The reciprocal arises because the
pushforward of the row measure under `x ↦ x ᵥ* g` is the row measure scaled
by `|det g|⁻¹`.

## Arbitrary Haar measure

The measure `ν` is any supplied `AdditiveHaarMeasure` on `F.Carrier`. Both row
Fourier integrals use the product of the same `ν`, and the proof never
compares `ν` with a self-dual or otherwise normalized measure. Scalar
multiplication of `ν` rescales both sides of the identity by the same factor,
but the proof does not use this.

## Dimension zero

No case split on `d` occurs. Every step holds uniformly in `d`. In particular,
`productMeasure_map_matrix` holds for every finite index type, including the
empty type `Fin 0`. For `d = 0`, the determinant of the empty matrix is `1`
and `T.normalizedAbs 1 = 1`, so the general argument specializes to the
identity described in the statement's Markdown.

## Relation to the source

The original identity is in Jacquet, Piatetski-Shapiro and Shalika,
*Rankin–Selberg Convolutions* (1983), §2.10, printed p.396 (one-based PDF page
31 of the registered `jpss-1983-rankin-selberg`), between (2.10.2) and
(2.10.3). In the source's notation it is

```text
(ρ(g)Φ)^ = |det g|^{-1} ρ(g^ι) Φ^ ,
```

with `ρ` the right translation `(ρ(g)Φ)(x) = Φ(xg)`, `^` the plus-sign Fourier
transform defined with a self-invariant Haar measure, and `g^ι` the inverse
transpose. The statement's Markdown locates these conventions in §0.3, printed
pp.375–378. Evaluating both sides at a row `y` gives the Lean identity. Its
left side is the row Fourier integral of `Φg = ρ(g)Φ` at `y`, and its right side
is `|det g|⁻¹` times the row Fourier integral of `Φ` at
`y ᵥ* ((g⁻¹).val)ᵀ = y g^ι`. The theorem is a derived specialization:

- it covers only fields given as `PadicField` realizations, not all
  nonarchimedean local fields;
- it allows an arbitrary Haar measure rather than the self-invariant one;
- it adds explicit existence of the Schwartz–Bruhat pullback;
- it includes `d = 0`.

The source uses the identity without giving a proof. The argument above is
the usual change of variables.

The statement's Markdown records a printing caveat: the p.396 scan appears to
put a duplicated Fourier hat on the final `Φ`. The change-of-variables formula
has a single Fourier transform of `Φ` there. That is what the Lean statement
asserts and this module proves. The proof does not depend on how the source
prints this detail, and this Markdown makes no further claim about the scan.

## Declarations

- `rowPairing_vecMul` — the row pairing identity of step 1.
- `rowMeasure_map_vecMul` — the determinant change of variables of step 2.
- `rowFourierIntegral_vecMul` — the general Fourier change of variables of
  step 3.
- `padicRowFourierEquivariance` — the target theorem.

The module imports `PadicRowFourierEquivarianceStatement`, `RowSchwartzAction`
and `PadicRectangularHaarScalingProof`, which provides `padicScalarHaarScaling`
through its own import. It uses no `sorry`, `admit` or new axiom. Its axioms are
`propext`, `Classical.choice` and `Quot.sound`.
