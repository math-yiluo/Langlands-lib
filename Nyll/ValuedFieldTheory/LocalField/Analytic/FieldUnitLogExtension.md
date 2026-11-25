# Extending a principal-unit logarithm to all field units

Module `Nyll.ValuedFieldTheory.LocalField.Analytic.FieldUnitLogExtension`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `K` be a complete discretely valued field with finite residue field (the library's `CompleteDVF`), and suppose `Kˣ` is identified, through a uniformizer, with the product of the residue roots of unity, the first principal units `U¹`, and `ℤ`. The file extends a homomorphism `φ : U¹ → A` into an additive group to all of `Kˣ`, by killing the roots of unity and giving the uniformizer a prescribed value `c`. It then chooses `c` so that a given unit, in practice `p`, has logarithm zero; killing the uniformizer itself is not the right normalization.

## Main definitions

- `fieldUnitDecompositionLogHomWithUniformizerValue F φ c`: the homomorphism on the factors `(ζ, u, πᵐ) ↦ φ(u) + m c`, with evaluation lemmas on each factor (`_root`, `_principal`, `_uniformizer`).
- `fieldUnitLogHomWithUniformizerValue F d φ c`: the same homomorphism transported to `Kˣ` along a decomposition isomorphism `d`.
- `uniformizerLogValueKilling F d φ a`: for `K` of characteristic zero and `A = K`, the value `c = −φ(u_a)/m_a`, where `a` decomposes with principal part `u_a` and uniformizer exponent `m_a`.

## Main results

- `fieldUnitLogHomWithUniformizerValue_apply_of_decomposition_eq`, `_eq_of_principal_decomposition`, `_eq_of_completeDVF_principal`: for any `d`, the extension takes the value `φ(u) + m c` at `d(ζ, u, πᵐ)`, hence `φ(u)` at `d(1, u, 1)`; the last says that, for the decomposition attached to a uniformizer `π`, the extension agrees with `φ` on the image of `U¹` in `Kˣ`.
- `continuous_fieldUnitDecompositionLogHomWithUniformizerValue`, `continuous_fieldUnitLogHomWithUniformizerValue`: if `φ` is continuous, so is the extension, on the factors and, for a decomposition that is a topological isomorphism, on `Kˣ`.
- `fieldUnitLogHomWithUniformizerValue_uniformizerLogValueKilling`: with `c = uniformizerLogValueKilling F d φ a`, the extension sends `a` to `0`, provided the uniformizer exponent of `a` is nonzero.

## Points to watch

- The homomorphism on `Kˣ` is relative to a chosen decomposition `d : factors ≃* Kˣ`, passed as an argument (the homomorphism on the factors does not involve `d`); continuity on `Kˣ` needs `d` to be a topological isomorphism.
- The codomain is written `Multiplicative A`, so "sends `a` to `0`" appears as `= 1`.
- The nonzero-exponent hypothesis is separate from the definition of `uniformizerLogValueKilling`, which is defined for every `a`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/Analytic/FieldUnitLogExtension.lean`: the Lean file is the source byte for byte (SHA-256 `724bc1963881d37664ad3485c9415a4f413161face77fc97c1e8f13605d20ed2`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
