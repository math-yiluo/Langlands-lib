# Determinants of intersections of filtered unit groups

Bushnell and Kutzko identify the determinant image of filtered unit groups in the transfer argument of *The admissible dual of GL(N) via compact open subgroups* (1993). The source is `bushnell-kutzko-1993-admissible-dual-gln`, SHA-256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`, (3.6.5), (3.6.6) and the determinant assertion of (3.6.9) on printed pp. 129–131 (PDF pp. 141–143).

For two lattice chains in one vector space over a nonarchimedean local field, `LatticeChain.det_image_inf_unitFiltration` computes the determinant image of the intersection of `U^{m₁+1}` and `U^{m₂+1}` when `⌊m₁/e₁⌋ = ⌊m₂/e₂⌋`, where each `eᵢ` is the period of its chain. The answer is `1 + 𝔭^{⌊m₁/e₁⌋+1}`, expressed in the field. Taking both chains equal gives the determinant image for a single filtered unit group.

For containment, `det_unitFiltration_congr` transports the chain and the endomorphism `g − 1` to a coordinate space. The bound `e ⌊m/e⌋ ≤ m` makes the published determinant congruence for `𝔓^{e⌊m/e⌋+1}` applicable. The determinant is invariant under this transport.

For the reverse containment, a simultaneous splitting basis supplies a coordinate projection that preserves every lattice of both chains. Given `a ∈ 𝔭^d` with `d = ⌊mᵢ/eᵢ⌋ + 1`, multiplying the projection by `a` shifts each chain by at least `eᵢd ≥ mᵢ+1`. Adding the identity produces an element of the intersection. Its matrix is diagonal in the common basis with diagonal entry `1+a` on the chosen line and `1` on every other line, so its determinant is `1+a`.
