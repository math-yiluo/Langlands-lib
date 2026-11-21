# Intertwining of characters

Source: C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), §3.3, definition before (3.3.2), printed p. 104 (PDF p. 116), and the character normalizer in (3.3.17), printed p. 112 (PDF p. 124).

`characterIntertwining χ₁ χ₂` is the set of `g` in the ambient group such that `χ₁(g h g⁻¹) = χ₂(h)` for every `h` in `H₂` whose conjugate lies in `H₁`. This tests exactly the intersection `g⁻¹ H₁ g ∩ H₂`, with the conjugation on the first character. In particular, `characterSelfIntertwining χ` uses the same character for both arguments.

`characterNormalizer χ` adds the domain-normalization condition to self-intertwining. Under that condition the test is on the entire domain, so it is exactly invariance of the character under conjugation. Both definitions use group homomorphisms into `ℂˣ` and make sense for any ambient group.
