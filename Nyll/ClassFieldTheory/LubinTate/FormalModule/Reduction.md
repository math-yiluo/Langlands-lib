# Reduction of the Lubin–Tate intertwining defect

Module `Nyll.ClassFieldTheory.LubinTate.FormalModule.Reduction`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let e and ē be Lubin–Tate series for π over the valuation ring of a local field K with residue field of q elements, and H a series in finitely many variables with prescribed linear term. Modulo the maximal ideal, e and ē become X^q, so both sides of e(H) = H(ē(Xᵢ)ᵢ) reduce to H̄^q. Hence every defect coefficient is divisible by π when π is a uniformizer.

## Main results

In `LubinTate.SameUniformizer`:

- `mvPowerSeries_expand_natCard`: over a finite field with q elements and in finitely many variables, replacing every variable by its q-th power equals raising the series to the q-th power.
- `map_inVariable`: ē(Xᵢ) reduces to Xᵢ^q.
- `map_subst_lubinTateSeries`: e(H) reduces to H̄^q.
- `map_subst_inVariables`: H(ē(Xᵢ)ᵢ) reduces to H̄(X₁^q, …).
- `map_defect_eq_zero`: the defect reduces to zero.
- `uniformizer_dvd_coeff_defect`: for a uniformizer π, π divides every defect coefficient.

## Proofs

The finite-field statement writes q = p^n and uses Mathlib's iterated Frobenius on expanded power series.

## Watch for

- Only the last result needs π to be a uniformizer.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/FormalModule/Reduction.lean`: the Lean file is the source byte for byte (SHA-256 `e83ca68eba5f017deac35b5da989d3a8778f42bc9cd057f7ddf84bde01a550fc`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
