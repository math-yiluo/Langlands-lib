# KP Lemma 11.5.2: the character-valuation kernel

`Langlands.Geometry.Building.Kottwitz.CharacterKernelStatement` states Lemma 11.5.2 of Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), printed pp. 430–431 (PDF pp. 461–462). The November 2024 corrections leave this lemma unchanged. This is a Prop-valued statement awaiting proof.

For every nonarchimedean local field `F` and every connected reductive `F`-group `G`, let `K = UnramifiedClosure F`, `E = SeparableClosure F`, `I = Gal(E/K)`, `Γ = Gal(K/F)` and `A = π₁(G)_I`. The statement is the subgroup equality

`characterValuationKernel (ValuativeRel.valuation F) G = κ_G⁻¹((A_tor)^Γ)`.

The left side is exactly the Library's `G(F)^1` of KP Definition 2.6.15. The canonical valuation representing the given valuative relation is used, so the condition on every rational character is that its value is `1`, equivalently that its additive valuation is zero. The right side uses the actual constructed `reductiveKottwitzRational`, with codomain `A^Γ`. `fundamentalInvariantTorsion` is the torsion subgroup of `A^Γ`; finite order in that subgroup is equivalent to finite order in `A`, so this is precisely `(A_tor)^Γ`.

The statement has no chosen zero-subgroup datum, Kottwitz map or kernel identity as an input. It allows all local fields, equal and mixed characteristic, with no split, quasi-split, tame, rank or residue-characteristic restriction. It concerns `G(F)^1`; the different group `G(F)^0` is the subject of the companion Proposition 11.5.4 statement.
