# Genericity of the smooth contragredient

Author: Worker 51.

This module proves the unchanged published proposition
`Langlands.GenericContragredientStatement.{uF,uV}` from
`Langlands.Representation.Whittaker.GenericDualStatement`. Its closing theorem is

```lean
theorem Langlands.genericContragredient :
    GenericContragredientStatement.{uF,uV}
```

For every prime, every actual p-adic field with its canonical norm topology,
every positive rank `n + 1`, and every irreducible admissible complex
representation `rho` having a nonzero Whittaker functional for the specified
continuous nontrivial unitary additive character `psi`, it provides both:

- An actual complex linear equivalence `E : V ≃ₗ[ℂ] SmoothDual rho` satisfying
  `E (rho ((g⁻¹)ᵀ) v) = smoothContragredient rho g (E v)`.
- A nonzero linear functional on that smooth dual with the explicit
  upper-unitriangular adjacent-entry covariance for `psi⁻¹`.

The field universe `uF` and carrier universe `uV` are independent. The carrier
has no added topology or finite-dimensionality hypothesis. Rank one is included.
`SmoothDual rho` and its action are the Library's actual smooth part of the
algebraic dual and smooth contragredient.

## Implemented proof

The proof introduces the quantified field, representation, character and
hypotheses, installing the supplied primality fact and canonical normed-field
structure locally. The published theorem
`Langlands.gelfandKazhdanContragredient` applies to admissibility and
irreducibility alone and supplies `E` and its inverse-transpose equivariance
identity `hE`. No equivalence or character equality is assumed by the closing
theorem.

For the first conclusion, the proof uses `E` itself. The target bundles the
transpose of the inverse matrix with `Matrix.GeneralLinearGroup.mkOfDetNeZero`,
whereas `hE` uses `GeneralLinear.inverseTranspose`. Their underlying matrices
are definitionally equal. `Units.ext` identifies the two group elements, after
which `hE` is exactly the target equation. This preserves the ordinary
inverse-transpose formula in the unchanged statement.

For the second conclusion, choose the given nonzero functional `ell` and use
the published construction
`Langlands.Whittaker.explicitSmoothDualFunctional rho E ell`. Its value at
`v : SmoothDual rho` is

`ell (rho (weylLong (n + 1) F.Carrier) (E.symm v))`.

`explicitSmoothDualFunctional_ne_zero` proves its nonvanishing from that of
`ell`. `explicitSmoothDualFunctional_covariance` applies to `hE` and the
original explicit upper-unitriangular covariance. It uses the reflected
unipotent matrix `w (g⁻¹)ᵀ w`, whose adjacent entries are the negatives of
those of `g` in reverse order. Reindexing the finite product gives precisely
the target product of `psi⁻¹`. The empty product covers rank one. These two
transport lemmas prove the functional conclusion without a multiplicity-one
input. The continuity, nontriviality and unitarity hypotheses remain exactly
as stated; the transport calculation itself does not need them.

## Provenance and published inputs

This proof is an internal assembly of two published results, imported by Lean
module and declaration name:

- `Langlands.Representation.Smooth.Contragredient.GelfandKazhdanProof`
  supplies `Langlands.gelfandKazhdanContragredient`, which proves the
  unconditional realization statement with independent universes.
- `Langlands.Representation.Whittaker.GenericDualTransport` supplies the
  explicit functional and its nonvanishing and covariance lemmas.

The interpretation of the target is Jacquet, Piatetski-Shapiro and Shalika,
*Rankin-Selberg Convolutions* (1983), Section 2.1, printed pages 385–386,
especially equation (4) and the following irreducible paragraph on page 386.
The registered original is `jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The original passages and formulas were read during this task. The
Weyl-translated functional is the functional form of that displayed
Whittaker-model transform. The source attributes the contragredient
equivalence to Gelfand–Kazhdan; here that step is supplied by the published
theorem, whose companion explains the Bernstein–Zelevinsky (1976),
Theorem 7.3 character proof. This module adds no new literature theorem or
distribution argument.

The Gelfand–Kazhdan prerequisite, by Worker 249 and Worker 51, is independently
accepted and published: candidate `31571ec8-f1e7-40bb-8ff2-37cfb530ee48`,
machine receipt `dd272eec-9f3d-495f-b32c-f014b45ef469`, independent review
`e303b17f-ea1b-40d2-8f12-e55e8cc7e169` by Reviewer 3943, and Library publication
`4021bb1d1ec99e65990e08addda3ade7caa73058`. The exact Library and workspace
Lean/Markdown hashes were compared before reuse. The functional-transport
module was previously accepted and published as candidate
`18fc6585-3195-4da5-96df-52744fc430ec`.

## Compilation, exact-target validation and release status

The module is checked in the project's pinned environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` against Library
`355c05239d7704a3ed5d72bad864cb1d542b647a`. Local check
`6ffad4d1-d6fe-4eee-bf6b-cdf9e0bd79a9` compiled the module with zero errors and
zero warnings. Inspection of `Langlands.genericContragredient` reported a
theorem with exactly the universe parameters `uF` and `uV` and only the standard
axioms `propext`, `Classical.choice` and `Quot.sound`. Its complete type is the
unapplied target proposition; the inspected type fingerprint is
`f50f3abc161a935f2af359a11e97659341ffa713675b65ad558617268f31297d`.

The theorem's type is the complete unapplied
`GenericContragredientStatement.{uF,uV}`. Its statement pair and imported pairs
remain unchanged. Official validation of this contribution must check the Lake
build, exact target, unchanged statement and frozen inputs.

At submission time, this pair has not received official machine validation,
independent semantic acceptance or Library publication. Those are separate
requirements; successful local compilation alone establishes none of them.
