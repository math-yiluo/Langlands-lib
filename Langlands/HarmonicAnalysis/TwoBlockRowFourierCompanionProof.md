# Proof of the two-block row Fourier companion identity

Author: Worker 1181.

The theorem `Langlands.HarmonicAnalysis.twoBlockRowFourierCompanion` proves exactly the
published closed proposition
`Langlands.HarmonicAnalysis.TwoBlockRowFourierCompanionStatement.{uF}`. Its only
universe parameter is the field universe `uF`. The statement module and every module
it imports are unchanged. The proof uses only Lean's standard axioms `propext`,
`Classical.choice` and `Quot.sound`. It contains no `sorry` and adds no hypothesis.

The source is Jacquet, Piatetski-Shapiro and Shalika, *Rankin–Selberg Convolutions*
(1983), §4.8, printed p.415, equation (3). The source only says that (3) is "a simple
consequence of Fourier inversion" and gives no further argument. The route below is
this module's own. It proves the arbitrary-row form of the published statement, and
the printed identity is one instance of it (see the last section).

## What is proved

For every prime `p`, every `F : PadicField.{uF} p` with the structures installed by the
statement, every unitary additive character `ψ`, and every supplied additive Haar
measure `μ` with `IsSelfDual ψ μ`, take `a, b` with `0 < a` and `0 < b`, and set
`N = a + b`. The theorem then proves the following.

1. Every Schwartz–Bruhat `Φ` on `Fin N → F` has a Schwartz–Bruhat `Φhat` with
   `IsRowFourierPair ψ μ Φ Φhat`.
2. For every such pair, every `g`, and arbitrary `ξ : Fin b → F` and `η : Fin a → F`,
   both integrands of the statement are integrable and

   ```text
   |det g|⁻¹ · ∫_u ψ(-⟨u, ξ⟩) Φhat((u, η) · w_N ᵗg⁻¹) du
     = ∫_w ψ(⟨w, η ∘ rev⟩) Φ((w, ξ ∘ rev) · g) dw.
   ```

Here `(u, η)` is `twoBlockSwappedRow u η`, `(w, ξ ∘ rev)` is
`Fin.append w (ξ ∘ Fin.rev)`, `⟨x, y⟩ = rowPairing x y = ∑ i, x i * y i`, `w_N` is
`weylLong N`, and `|·|` is `F.canonicalTopologicalData.normalizedAbs`. The integrals
are Bochner integrals for `rowMeasure μ b` and `rowMeasure μ a`.

The hypotheses `0 < a` and `0 < b` are introduced but not used.

## Imported results

Every ingredient is a published Library theorem, imported by Lean name:

- `rowFourierCompatibility` (`RowFourierCompatibilityProof`). For each `d`,
  `IsSelfDual ψ μ` gives `RowFourierClosed ψ μ d` and `IsRowSelfDual ψ μ d`. The second
  is row Fourier inversion `f̂̂(y) = f(-y)`, together with integrability of the
  integrand of the second transform.
- `scalarFourierClosure` (`ScalarFourierClosureProof`). It gives
  `SigmaFinite μ.measure` from `IsSelfDual ψ μ`.
- `padicRowFourierEquivariance` (`PadicRowFourierEquivarianceProof`). For every `h`
  it gives the right translate `x ↦ Φ(x h)` as a Schwartz–Bruhat function, and the
  change of variables
  `rowFourierIntegral (Φ(· h)) y = |det h|⁻¹ · rowFourierIntegral Φ (y · ᵗh⁻¹)`.
- From `TwoBlockRowPartialFourierData`:
  - the block maps `join`, `first` and `second`, with `contiguousEquiv` and
    `join_contiguousEquiv`;
  - the Schwartz–Bruhat slices `slice e Φ v = (w ↦ Φ (join e w v))`;
  - the joined tensors `joinedTensor e α β`;
  - the finite expansion `exists_joinedTensor_expansion`;
  - `rowPairing_join`;
  - `schwartz_rowFourierIntegrand_integrable`, which says that `x ↦ ψ(⟨x, y⟩) f x` is
    integrable for every Schwartz–Bruhat `f`.
- The normalized-absolute-value lemmas `normalizedAbs_mul`, `normalizedAbs_one`,
  `normalizedAbs_nonneg` and `normalizedAbs_pos`
  (`Langlands.LocalField.Normalization.Proof`).
- The Weyl-element facts `weylLong_entry`, `weylLong_mul_self`,
  `inverseTranspose_weylLong` and `inverseTranspose_coe` (`Langlands.Group.GL.Maps`).
- Mathlib's product-measure lemmas for `Measure.pi`.

No two-block factor multiplicativity, Section 7 assembly, Section 9.3 result, or
dominant-rank analytic input is imported.

## Helper lemmas

The helpers are in the namespace
`Langlands.HarmonicAnalysis.TwoBlockRowFourierCompanion`.

### Measure lemmas

These hold for any measurable space `K`, any `e : Fin b ⊕ Fin a ≃ Fin N`, and any
supplied `μ` with `SigmaFinite μ.measure`.

- `joinMeasurableEquiv e` is the measurable equivalence
  `(Fin b → K) × (Fin a → K) ≃ᵐ (Fin N → K)`. It is
  `MeasurableEquiv.sumPiEquivProdPi` inverted, followed by
  `MeasurableEquiv.piCongrLeft` along `e`. `joinMeasurableEquiv_apply` identifies it
  with `(u, v) ↦ join e u v`.
- `measurePreserving_joinMeasurableEquiv` proves that this map carries
  `(rowMeasure μ b).prod (rowMeasure μ a)` to `rowMeasure μ N`. It composes Mathlib's
  `measurePreserving_sumPiEquivProdPi_symm` and `measurePreserving_piCongrLeft`.
- `integral_comp_rev` proves `∫ f (w ∘ rev) = ∫ f v` for `rowMeasure μ d`. Reversing
  coordinates preserves the product measure by `measurePreserving_arrowCongr'` with
  `Fin.revPerm`.

### Product formula and pairing identities

- `rowFourierIntegral_joinedTensor_join`: at a joined point, the full-row Fourier
  integral of a joined tensor is the product of the two block Fourier integrals:

  ```text
  rowFourierIntegral ψ μ N (joinedTensor e α β) (join e u η)
    = rowFourierIntegral ψ μ b α u · rowFourierIntegral ψ μ a β η.
  ```

  The proof pulls the integral back along `joinMeasurableEquiv e`. It then splits the
  pairing with `rowPairing_join` and the character with `AddChar.map_add_eq_mul`. The
  integrand becomes a product of a function of `u` and a function of `v`, and
  Mathlib's `integral_prod_mul` gives the product of integrals. That lemma has no
  integrability hypothesis.
- `rowPairing_neg_right` proves `⟨x, -y⟩ = -⟨x, y⟩`.
- `rowPairing_comp_rev` proves `⟨x ∘ rev, y⟩ = ⟨x, y ∘ rev⟩`, by reindexing the sum
  along `Fin.revPerm`.

### Core partial inversion

`integral_join_rowFourierPair` is the core identity. It holds over any field `K` with
the topological, measurable, locally compact, Hausdorff and totally disconnected
structure. Its hypotheses are:

- `IsRowSelfDual ψ μ b`;
- a block placement `e : Fin b ⊕ Fin a ≃ Fin N`;
- a full-row pair `IsRowFourierPair ψ μ Ψ Ψhat`.

For all `ξ : Fin b → K` and `η : Fin a → K` it proves

```text
∫_u ψ(-⟨u, ξ⟩) Ψhat(join e u η) d(rowMeasure μ b)
  = ∫_v ψ(⟨v, η⟩) Ψ(join e ξ v) d(rowMeasure μ a).
```

This is Fourier inversion in the `b` block. The proof never exchanges two
non-compact integrals. It works as follows.

1. `exists_joinedTensor_expansion` writes `Ψ = ∑_{j < M} joinedTensor e α_j β_j`,
   with `α_j` Schwartz–Bruhat on `Fin b → K` and `β_j` on `Fin a → K`.
2. Hence `Ψhat(join e u η) = ∑_j α̂_j(u) · β̂_j(η)`. The Fourier integral of the finite
   sum is the sum of the integrals by `integral_finsetSum`, since each summand is
   integrable by `schwartz_rowFourierIntegrand_integrable`. Each summand then equals
   the product by `rowFourierIntegral_joinedTensor_join`.
3. On the left, rewrite `ψ(-⟨u, ξ⟩)` as `ψ(⟨u, -ξ⟩)`. The `u`-integral splits over the
   finite sum. Each term `u ↦ ψ(⟨u, -ξ⟩) α̂_j(u)` is integrable by the integrability
   half of `IsRowSelfDual ψ μ b`. So the left side is `∑_j α̂̂_j(-ξ) · β̂_j(η)`.
4. The inversion half of `IsRowSelfDual ψ μ b` gives `α̂̂_j(-ξ) = α_j(ξ)`, so the left
   side is `∑_j α_j(ξ) · β̂_j(η)`.
5. Undo the finite sum on the right. Each term `v ↦ α_j(ξ) ψ(⟨v, η⟩) β_j(v)` is
   integrable. Since `Ψ(join e ξ v) = ∑_j α_j(ξ) β_j(v)` by `first_join` and
   `second_join`, the right side is also `∑_j α_j(ξ) · β̂_j(η)`.

### Coordinate lemmas

- `twoBlockSwappedRow_eq_join` proves `twoBlockSwappedRow u v = join e u v` for
  `e = contiguousEquiv (Nat.add_comm b a) : Fin b ⊕ Fin a ≃ Fin (a + b)`. This `e`
  places the `b` block first.
- `twoBlockSwappedRow_comp_rev` proves
  `twoBlockSwappedRow ξ (w ∘ rev) ∘ rev = Fin.append w (ξ ∘ rev)`. It uses Mathlib's
  `Fin.append_rev` together with `Fin.cast_rev`.
- `vecMul_weylLong` proves `x · w_N = x ∘ rev`, from the entries `weylLong_entry` of
  the antidiagonal permutation matrix.

## Main theorem

The proof first installs the same topology, valuative relation, local-field
structure, Borel measurable space, `T2Space` and `TotallyDisconnectedSpace` as the
statement, with the same terms. It obtains `SigmaFinite μ.measure` from
`scalarFourierClosure`, and sets `hcompat d := rowFourierCompatibility ψ μ d hsd`.

**Conclusion 1** is `(hcompat (a + b)).1`.

For **conclusion 2**, fix `Φ`, `Φhat`, `g`, `ξ` and `η`. Let `W = weylLong (a + b)`,
let `e` be the placement above (`b` block first), and let `e' = contiguousEquiv rfl`
(`a` block first, so `join e' w v = Fin.append w v`).

1. **Translates.** `padicRowFourierEquivariance` with `W * g` gives the Schwartz–Bruhat
   function `Ψ` with `Ψ x = Φ(x · W g)`, together with its change of variables. With
   `g` it gives `Φg` with `Φg x = Φ(x g)`. Then `(hcompat (a + b)).1` gives `Ψhat` with
   `IsRowFourierPair ψ μ Ψ Ψhat`.
2. **Determinants.** `det W · det W = det (W W) = 1` by `weylLong_mul_self`.
   Multiplicativity and nonnegativity of `normalizedAbs` give `|det W| = 1`, so
   `|det (W g)| = |det g|`. This is nonzero because `det g ≠ 0`.
3. **Inverse transpose.** As matrices, `ᵗ(W g)⁻¹ = W · ᵗg⁻¹`. This holds because
   `inverseTranspose` is a group homomorphism and fixes `W`
   (`inverseTranspose_weylLong`).
4. **Left integrand.** By steps 1–3 and `IsRowFourierPair ψ μ Φ Φhat`, for every row
   `y`:

   ```text
   Ψhat(y) = |det g|⁻¹ · rowFourierIntegral Φ (y · W ᵗg⁻¹) = |det g|⁻¹ · Φhat(y · W ᵗg⁻¹).
   ```

   So the left integrand at `u` equals `|det g| · ψ(⟨u, -ξ⟩) · (slice e Ψhat η) u`.
   Here `twoBlockSwappedRow u η = join e u η`.
5. **Right integrand.** The right integrand at `w` equals
   `ψ(⟨w, η ∘ rev⟩) · (slice e' Φg (ξ ∘ rev)) w`.
6. **Integrability.** Both slices are Schwartz–Bruhat. So both integrands are
   integrable by `schwartz_rowFourierIntegrand_integrable`, the first multiplied by
   the constant `|det g|`.
7. **Equality.** The factor `|det g|⁻¹` cancels the constant `|det g|` from step 4. The
   left side becomes `∫_u ψ(-⟨u, ξ⟩) Ψhat(join e u η) du`. By
   `integral_join_rowFourierPair`, using `(hcompat b).2 : IsRowSelfDual ψ μ b`, this
   equals `∫_v ψ(⟨v, η⟩) Ψ(join e ξ v) dv`. The reversal `v = w ∘ rev`
   (`integral_comp_rev`) turns it into
   `∫_w ψ(⟨w ∘ rev, η⟩) Ψ(join e ξ (w ∘ rev)) dw`. Pointwise:
   - `⟨w ∘ rev, η⟩ = ⟨w, η ∘ rev⟩` (`rowPairing_comp_rev`);
   - `Ψ(join e ξ (w ∘ rev)) = Φ((ξ, w ∘ rev) · W · g)` (`Matrix.vecMul_vecMul`);
   - `(ξ, w ∘ rev) · W = (ξ, w ∘ rev) ∘ rev = (w, ξ ∘ rev)` (`vecMul_weylLong`,
     `twoBlockSwappedRow_comp_rev`).

   So the integrand is the right integrand of the statement.

Every integrability fact used comes from Schwartz–Bruhat integrability or from
`IsRowSelfDual`, which `rowFourierCompatibility` derives from `IsSelfDual ψ μ`. No
integrability, Fourier closure, inversion, sigma-finiteness or measure-scaling
premise is added. The measure is the supplied `μ` throughout, and it is never chosen
or rescaled.

## Arbitrary rows and the printed specialization

The theorem is proved for all fixed rows `ξ ∈ F^b` and `η ∈ F^a`, as the statement
quantifies. Nothing above depends on a particular choice:

- the inversion in step 7 is applied at the point `-ξ` of the `b` block;
- the second block is held at `η` throughout;
- the two reversals `ξ ↦ ξ ∘ rev` and `η ↦ η ∘ rev` come from `vecMul_weylLong` and
  `rowPairing_comp_rev`.

This is how the proof establishes the arbitrary-row extension.

The printed (4.8.3) is the instance `ξ = ζ_{t₂}` (first basis row of length `b = t₂`)
and `η = η_{t₁}` (last basis row of length `a = t₁`). Then `ξ ∘ rev = η_{t₂}` and
`η ∘ rev = ζ_{t₁}`. With these rows the two sides are the source's
`(w_r ᵗg⁻¹ Φ̂)*[ζ_{t₂}, η_{t₁}] |det g|⁻¹` and `(gΦ)~[ζ_{t₁}, η_{t₂}]`, as explained in
the statement's Markdown. That case therefore needs no separate argument.

The registered original `jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`, printed p.415
(one-based PDF page 50), was inspected visually for the source's justification of
(3).
