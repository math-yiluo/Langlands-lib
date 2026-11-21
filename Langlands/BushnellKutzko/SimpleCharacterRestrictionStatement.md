# Restriction, twisting and nonemptiness of simple characters (U3)

Source: C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), (3.2.4)–(3.2.5), printed p. 99 (PDF p. 111), (3.3.18) and (3.3.21), printed pp. 112 and 114 (PDF pp. 124 and 126). The high-index extension of notation is on printed p. 99.

`SimpleCharacterRestrictionStatement` is the following conjunction for every simple `[𝔄,n,0,β]`, base additive character of the specified conductor, and defining sequence starting at `β`. Denote the simple character set at index `m` by `C_m`; its domain is `H^{m+1}`. All indices are natural and the field and vector space universes are independent. `simpleCharacterRestriction` uses precomposition by the inclusion of the deeper subgroup.

1. For `⌊n/2⌋≤m≤n−1`, the character domain is `U^{m+1}(𝔄)` and `C_m` is the singleton whose character has values `ψ_β`.
2. In the nonscalar case, put `r=−k₀` and `d=⌊r/2⌋`. For `m≤d` and `m≤n−1`, the image under restriction is `C_d`. For every `θ∈C_m`, its fibre is exactly the set of `θχ` with `χ∈X`. Here `X` is represented by characters of `H^{m+1}` trivial on `H^{d+1}` and factoring through the relative determinant on `H^{m+1}∩B_β^×`. The triviality expresses descent to the quotient by `H^{d+1}`; the relative-unit product of (3.1.15)(i) identifies its characters with those of `U^{m+1}(𝔅_β)/U^{d+1}(𝔅_β)`, where the determinant condition is exactly the same one. The formulation uses the inflated characters so that no choice of quotient model or proof of (3.1.15) is needed in the statement.
3. At a simple critical approximation `γ` (so `r<n`), for `⌊r/2⌋≤m≤r−1` the two domains agree and there is a bijection of the simple character sets given by multiplication by `ψ_{β−γ}^{−1}`. The equation on the whole domain specifies this bijection for every character and every allowed defining sequence on each side.
4. For `m<n−1`, restriction maps `C_m` onto `C_{m+1}`.
5. For `m≤n−1`, `C_m` is nonempty.

These are statement targets, not proofs of surjectivity, nonemptiness or any of the other clauses.
