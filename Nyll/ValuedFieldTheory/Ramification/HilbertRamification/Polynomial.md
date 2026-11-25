# Polynomial evaluation preserves congruences

Module `Nyll.ValuedFieldTheory.Ramification.HilbertRamification.Polynomial`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

A single lemma of commutative algebra, used by the library's theory of ramification numbers.

`polynomial_eval₂_sub_mem_of_sub_mem`: let f : R →+* S be a map of commutative rings, I an ideal of S, and x, y elements of S with x − y ∈ I. Then for every polynomial P over R, the difference `P.eval₂ f x − P.eval₂ f y` lies in I.

The proof is by induction on P: sums are handled by closure of I under addition, and a monomial a·Xⁿ by the divisibility of xⁿ − yⁿ by x − y.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/HilbertRamification/Polynomial.lean`: the Lean file is the source byte for byte (SHA-256 `8e2e006b58b6e893be6a0cc24b6bb80c6e4f29092ff1a101b1c1c8c4633b4bc8`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
