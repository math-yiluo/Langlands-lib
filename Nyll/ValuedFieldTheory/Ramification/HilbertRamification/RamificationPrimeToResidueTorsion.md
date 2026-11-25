# The ramification group has no torsion prime to the residue characteristic

Module `Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RamificationPrimeToResidueTorsion`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a field extension L/K and a valuation subring A of L, the library's ramification group R is the group of automorphisms in the inertia group satisfying the principal-unit condition. The file shows that R has no nontrivial elements of order prime to the residue characteristic.

`ramificationGroup_eq_one_of_pow_eq_one_of_residue_natCast_ne_zero`: if σ is in R, σⁿ = 1, and n is nonzero in the residue field of A, then σ = 1.

Proof: suppose σ moves x, and put y = σ(x) − x. Each quotient σⁱ(y)/y is a principal unit, so it reduces to 1. Their sum over 0 ≤ i < n telescopes to (σⁿ(x) − x)/y = 0. Reducing the sum then gives n = 0 in the residue field, a contradiction.

Watch for: R is the library's own group, defined by the principal-unit condition. The statement needs no discreteness, no Henselian hypothesis and no finiteness of L/K.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/HilbertRamification/RamificationPrimeToResidueTorsion.lean`: the Lean file is the source byte for byte (SHA-256 `4944016f9925c856b1a136d97fe41f907af4dd488f2bc8fe0ac204e46a049fda`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
