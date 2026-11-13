# KP Corollary 11.7.6: the three Kottwitz quotients

`Langlands.Geometry.Building.Kottwitz.QuotientStatement` states Corollary 11.7.6 of Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), printed p. 434 (PDF p. 465). The November 2024 corrections do not alter it. This is a Prop-valued statement awaiting proof.

For every nonarchimedean local field `F`, every connected reductive `F`-group `G` and every Library datum `d : ZeroSubgroupDatum i j`, put `N = d.zeroSubgroup = G(F)^0`, `H = characterValuationKernel (ValuativeRel.valuation F) G = G(F)^1`, `K = UnramifiedClosure F`, `E = SeparableClosure F`, `I = Gal(E/K)`, `Γ = Gal(K/F)` and `A = π₁(G)_I`. Here the displayed identifications of `N` and `H` with the notation of KP refer to the existing subgroup definitions, not assumptions of their Kottwitz characterizations.

The statement concludes that `N` is normal and `N ≤ H`, and asserts the three group isomorphisms

- `G(F)/G(F)^0 ≃ A^Γ`;
- `G(F)^1/G(F)^0 ≃ (A_tor)^Γ`;
- `G(F)/G(F)^1 ≃ A^Γ/(A_tor)^Γ`.

Each isomorphism has a formula on every quotient representative: the first takes `[g]` to `κ_G(g)`; the second takes `[h]` to the same value in the invariant torsion subgroup; and the third takes `[g]` to the class of `κ_G(g)` modulo invariant torsion. Thus these are the maps induced by the actual constructed `reductiveKottwitzRational`, rather than unspecified abstract isomorphisms. The denominator of the second quotient is `N.subgroupOf H`, the intersection viewed inside `H`; the separately asserted inclusion identifies it with all of `N`.

Lean writes additive lattice groups multiplicatively at the homomorphism and group-quotient interfaces. The target torsion subgroup is `fundamentalInvariantTorsion`, the torsion of `A^Γ`, equivalently `(A_tor)^Γ`. The third target is the quotient of the invariant group by this subgroup. It makes no identification with `(A/A_tor)^Γ`.

Normality of `H` follows by definition from its character kernels, and all target subgroups are normal since the target is commutative. Normality of `N` is a conclusion. The statement has no supplied Kottwitz map, kernel identity, surjectivity or subgroup normality hypothesis. It treats equal and mixed characteristic without split, quasi-split, tame, rank or residue-characteristic restrictions. The source's `dim(f) ≤ 1` assumption holds because the residue field of `F` is finite.
