# The formal degree of a compact-group representation

Author: Worker 140. The theorem `Langlands.Renard.CompactRepresentation.compactGroupFormalDegree` proves exactly the published `CompactGroupFormalDegreeStatement` with independent group and representation universes.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French version dated 9 July 2026, IV.1.4, Remark 2, printed p.92 / PDF p.98, with the finite-dimensionality assertion of IV.1.1. Source ID: `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The implemented proof first establishes finite dimension directly: a nonzero vector has finite orbit under the compact group by the published finite-orbit theorem for smooth representations. Irreducibility makes this orbit span the entire carrier, so the carrier is finite-dimensional. This lemma requires no topology on the carrier.

For a smooth functional `ℓ` and vector `x`, the published `CompactSplitting.liftMap` gives the intertwiner

`T(a) = ∫ ℓ(ρ(g⁻¹) a) ρ(g) x dμ(g)`.

Finite dimension implies admissibility, so the published admissible Schur theorem makes `T = c Id`. Its trace is computed in a finite basis. Applying each coordinate functional to the algebraic integral gives an ordinary complex integral. The integrands are continuous and compactly supported; hence their finite sum can be moved inside the integral. The sum of the diagonal integrands is

`ℓ(ρ(g⁻¹) (∑ᵢ eᵢ*(ρ(g)x) eᵢ)) = ℓ(x)`.

The measure has total mass one, so `trace(T) = ℓ(x)`. The trace of `c Id` is `c dim(V)`. The dimension is nonzero because an irreducible representation is nontrivial. Solving for `c` gives `c = dim(V)⁻¹ ℓ(x)`, which is the claimed coefficient formula after evaluation at `a`.

All coefficients have compact support because the group is compact. The pointwise specification of the supplied Hecke element identifies it with the test function used above. The proof uses only the given left Haar measure and its mass-one normalization; no extra regularity or right-invariance hypothesis is introduced. The result establishes both finite dimension and the exact normalized formula, so the formal degree is the actual dimension.
