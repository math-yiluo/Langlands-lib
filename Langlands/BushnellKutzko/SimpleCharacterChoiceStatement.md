# Independence and twisting of simple character sets (U4)

Source: C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), Corollary (3.3.20), printed p. 113 with proof on pp. 113–114 (PDF pp. 125–126). The common-domain comparison also uses (3.1.9), printed p. 91 (PDF p. 103).

`SimpleCharacterChoiceStatement` quantifies over a nonarchimedean local field and a finite-dimensional vector space at independent universes, a base additive character of the specified conductor, and every simple `[𝔄,n,0,β]`. It states:

1. For `0≤m≤n−1`, any two defining sequences starting at `β` give equal subgroups `H^{m+1}` and the same set `C(𝔄,m,β)` after identifying those domains.
2. Write `r=−k₀(β,𝔄)` and let `[𝔄,n,ℓ,β′]` be simple and equivalent to `[𝔄,n,ℓ,β]` for `0≤ℓ<r`. The congruence `β′−β∈𝔓^{−ℓ}` expresses equivalence at the common depth. For `⌊ℓ/2⌋≤m<r` within `0≤m≤n−1`, both character domains coincide and `C(𝔄,m,β′)=C(𝔄,m,β)·ψ_{β′−β}` for any defining sequences. The `r` bounds use `∞` for scalar `β`.

`characterSetTwist` compares values on the whole target domain; twisting by the constant `1` in the first clause is ordinary transport. The two clauses assert domain equality rather than assuming it. They are a proposition definition, not a proof.
