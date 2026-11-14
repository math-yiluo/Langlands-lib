# KP Proposition 11.6.1: the exact sequence for a K-chamber

`UnramifiedChamberExactSequenceStatement` states the surjectivity and kernel assertions of Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Proposition 11.6.1, printed p. 432 (PDF p. 463), on supplied canonical K-building data. It is a Prop-valued statement awaiting proof. The November 2024 corrections do not modify Proposition 11.6.1.

Let F be a nonarchimedean local field, G a connected reductive F-group, and K its actual maximal unramified extension. As in the Library's `ChamberStatement`, the supplied torus inclusion is defined over F and becomes maximal split over K. Supplied apartment data D, centralizer data C and their compatibility condition determine the canonical building B by `UnramifiedBuildingDescent.buildingData`. This statement does not assert the existence of those data and does not require Galois stability of D or of a chamber.

The helper `reductiveKottwitzOnBaseChange F G hG` transports the existing actual Kottwitz homomorphism κ_K along `baseChangeCoeffEquiv`, from the coefficient-point carrier to the rational-point carrier of G_K. Its target is the existing inertia coinvariant group A = π₁(G)_I, written multiplicatively.

For every chamber Cch of B, let P be its setwise stabilizer in G(K). The statement asserts that κ_K restricted to P surjects onto A. For every supplied `UnramifiedZeroDatum` E, it further asserts

E.zeroPoints ∩ B.pointwiseFixer(Cch) = ker(κ_K) ∩ P.

Here E.zeroPoints is the existing subgroup G(K)^0 of KP Definition 2.6.23(1), and the pointwise fixer is the Library's actual pointwise fixer in the same reduced building. This equality identifies the neutral chamber subgroup G(K)^0_Cch with the kernel of the restricted map; together with surjectivity, it expresses the exact sequence

1 → G(K)^0_Cch → G(K)_Cch → A → 1.

The source proves surjectivity using chamber transitivity of the simply connected derived group and triviality of its Kottwitz map. Its kernel assertion combines Proposition 11.5.4 with Proposition 7.6.4, which identifies G(K)^0_Cch with the intersection of G(K)^0 and the setwise chamber stabilizer. The statement records the latter kernel in the pointwise-fixer form used by the Library's connected parahoric-model statement. It does not assume a Kottwitz specification, kernel equality, transitivity, parahoric model, or rational surjectivity. Proving those inputs, or deriving the conclusion by another route, remains proof work.

Source: registered literature `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`, Proposition 11.6.1, printed p. 432 (PDF p. 463). The local-field and supplied-data scope is a restricted adaptation of the source's broader Henselian discretely valued setting. It supplies the K-chamber exactness input used in the proof of Corollary 11.7.5, but does not itself establish the rational corollary.
