# Galois action on a unique extension of a valuation ring

Module `Nyll.ValuedFieldTheory.Valuation.UniqueRing`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L/K` be a field extension, `V` a valuation subring of `K` and `W` a valuation subring of `L` extending it, in the sense of Mathlib's `Valuation.HasExtension` for the valuations attached to `V` and `W`. The file shows that `K`-automorphisms of `L` move extensions of `V` to extensions of `V`, so that when `W` is the only extension it is stable under every `σ ∈ Aut_K(L)`, and `σ` then acts on `W` and on its residue field. It also builds the canonical maps `V → W` and between residue fields.

## Main definitions and results

- `algEquiv_smul_valuationSubring_hasExtension`: for `σ : L ≃ₐ[K] L`, the translate `σ • W` again extends `V`.
- `algEquiv_smul_valuationSubring_eq_of_unique_extension`: if every valuation subring of `L` extending `V` equals `W`, then `σ • W = W`; `algEquiv_mem_valuationSubring_iff_of_unique_extension` is the elementwise form `σ x ∈ W ↔ x ∈ W`.
- `valuationSubringEquivOfUniqueExtension` and `residueFieldEquivOfUniqueExtension`: under uniqueness, the ring automorphism of `W` given by `σ`, and the induced automorphism of the residue field of `W`; `residueFieldEquivOfUniqueExtension_residue` computes it on residues.
- `valuationSubringMapOfHasExtension`: the ring map `V →+* W` restricting `algebraMap K L`; `valuationSubringMapOfHasExtension_isLocalHom` shows it is local, and `residueFieldMapOfHasExtension` is the induced map of residue fields.
- `residueFieldEquivOfUniqueExtension_algebraMap`: the induced residue automorphism fixes the image of the residue field of `V`.
- `minpoly_residue_eq_of_minpoly_eq_of_unique_extension`: if `L/K` is normal, `W` is the unique extension, and `x, y ∈ W` have the same minimal polynomial over `K`, then their residues have the same minimal polynomial over the residue field of `V`.

## Proofs

The translate `σ • W` has the same pullback to `K` as `W`, because `σ` fixes `K`; an earlier criterion characterizing extensions by their pullback then applies. For the minimal polynomials, normality gives `σ` with `σ y = x`, and the induced residue automorphism is an automorphism over the residue field of `V` carrying the residue of `y` to that of `x`.

## Points to watch

- Uniqueness of the extension is not proved here: it is the hypothesis `huniq` (every `W'` extending `V` equals `W`), carried by every result after the first except `valuationSubringMapOfHasExtension`, `valuationSubringMapOfHasExtension_isLocalHom` and `residueFieldMapOfHasExtension`, which need only that `W` extends `V` (`hW`).
- Neither `V` nor `W` is assumed discrete or of rank one, and `L/K` need not be algebraic, except that the last result needs `L/K` normal.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/UniqueRing.lean`: the Lean file is the source byte for byte (SHA-256 `83f882f9741c4b759385cfeb788fdefd929deb23163992036eda27e9b986b528`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
