# Finite ramification groups by residue characteristic

Module `Nyll.ValuedFieldTheory.Ramification.HilbertRamification.FiniteRamificationPrimary`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a field extension `L/K` and a valuation subring `A` of `L`, the file determines a finite ramification group `R` (of the valuation-subring theory) according to the characteristic of the residue field of `A`.

- `ramificationGroup_isPGroup_of_residueChar`: if `R` is finite and the residue field has characteristic `p` prime, `R` is a `p`-group.
- `ramificationGroup_eq_bot_of_residueCharZero`: if `R` is finite and the residue field has characteristic zero, `R` is trivial.

Both rest on `ramificationGroup_eq_one_of_pow_eq_one_of_residue_natCast_ne_zero`, from another file: an element of `R` killed by an integer `m` that is nonzero in the residue field is trivial. For the `p`-group statement the order of `σ` is written `p^a·m` with `p ∤ m`, and the lemma is applied to `σ^(p^a)`; in characteristic zero it is applied to the order itself.

Only finiteness of `R` is assumed; the file's comment notes that no Henselian, discreteness, perfectness or finite-residue-field hypothesis is used.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/HilbertRamification/FiniteRamificationPrimary.lean`: the Lean file is the source byte for byte (SHA-256 `b5939961bc92e743beee2e9719de8741dba418ab5ff11f8681aa96ee9397ba5b`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
