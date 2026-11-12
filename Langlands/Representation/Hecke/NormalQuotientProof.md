# Proof of Renard III.2.10

`normalQuotientStatements` proves the published target
`Langlands.Hecke.Homomorphism.NormalQuotientStatements` for all universe
parameters `uP uG v`: Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, III.2.10, (III.2.10.1)–(III.2.10.2),
Proposition and Corollary, printed pp.80–82 / PDF pp.86–88, source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The proof is the conjunction of three theorems.

1. `normalQuotientHeckeStatement : NormalQuotientHeckeStatement`. After
   introducing the group, closed normal subgroup and Haar measures, it supplies
   - `pseudoFIsoF` (module `NormalQuotientPseudo`): `pseudoF ≅ F` for the
     quotient projection;
   - `rightModule_doubleCoset` (module `NormalQuotientBalance`): identity
     (III.2.10.1), `T·(e_K * l(p) e_K) = T * (e_{q(K)} * l(q p) e_{q(K)})`;
   - `coinvariantTensorIso` (module `NormalQuotientComparison`) as the natural
     isomorphism `α`, with `coinvariantTensorIso_hom_mk` (forward map
     `[w] ↦ e_{q(K)} ⊗ w` for `K`-fixed `w`) and
     `coinvariantTensorIso_inv_tmul` (inverse map `T ⊗ w ↦ T·[w]`).
2. `normalQuotientAdjunctionStatement` and
3. `normalQuotientInductionAdjunctionStatement`, imported unchanged from the
   published module `Langlands.Representation.Hecke.NormalQuotientAdjunctionProof`
   (Worker 150): the Proposition `j_N ⊣` quotient pullback and the Corollary
   for a closed subgroup.

The theorem uses only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.
