# Transfer of simple characters within one endomorphism algebra (U8)

Source: C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), existence and uniqueness assertion in Theorem (3.6.1), printed p. 127 (PDF p. 139); the relative chain period is from (1.2.4), printed p. 25 (PDF p. 37).

`SimpleCharacterTransferStatement` starts with simple strata `[𝔄_i,n_i,m_i,β]` for two hereditary orders in the same `A=End_F(V)`, with the same actual element `β`. It quantifies over `m_i≥0`, every defining sequence for each input, and the character parameter `ψ_F` with the specified conductor. Field and vector space universes are independent.

In the notation `E=F[β]` and `𝔅_i=𝔄_i∩End_E(V)`, the period `e_i=e(𝔅_i|𝔬_E)` is computed as `e(𝔄_i|𝔬_F) / e(E|F)`. This is exact by the published relative period identity (`subfieldOrder`, BK93 (1.2.4)); the denominator in that ratio is the published `elementRamificationIndex`. The displayed normalized depths `m_i / e_i` then use natural floor division.

When the normalized depths coincide, each `θ₁∈C(𝔄₁,m₁,β)` has a unique `θ₂∈C(𝔄₂,m₂,β)` with identical character values on the entire intersection `H^{m₁+1}(β,𝔄₁) ∩ H^{m₂+1}(β,𝔄₂)`. Only this existence and uniqueness clause is stated here, not the additional equivalences in (3.6.1) nor transfer between different underlying vector spaces.
