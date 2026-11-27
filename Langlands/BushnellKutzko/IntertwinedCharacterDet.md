# Characters of `U^{m+1}(𝔄)` intertwined by all of `G` factor through the determinant: proof

Source: C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact open
subgroups*, Annals of Math. Studies 129 (1993), `bushnell-kutzko-1993-admissible-dual-gln`,
Lemma (2.4.11), second assertion, printed pp. 72–73 (PDF pp. 84–85), proved in §2.5 on
printed p. 78 (PDF p. 90).

The theorem `Langlands.BushnellKutzko.intertwinedCharacterDet` proves
`IntertwinedCharacterDetStatement.{uF, uV}` (module
`Langlands.BushnellKutzko.IntertwinedCharacterDetStatement`) at all universe levels `uF`, `uV`,
with the statement's hypotheses unchanged: for a lattice chain `L` in a vector space `V` over a
nonarchimedean local field `F`, `m : ℕ`, and any group homomorphism
`χ : L.unitFiltration (m + 1) →* ℂˣ` with every `g : (Module.End F V)ˣ` in
`characterSelfIntertwining χ`, there is `φ : d.range →* ℂˣ` with `χ = φ.comp d.rangeRestrict`,
where `d` is `Units.map LinearMap.det` restricted to `L.unitFiltration (m + 1)`.

## Input

The proof uses one result, the theorem `Langlands.BushnellKutzko.intertwinedUnitCharacter`
(module `Langlands.BushnellKutzko.IntertwinedUnitCharacter`), which proves
`IntertwinedUnitCharacterStatement`. That proposition makes the same assertion for
`L.unitFiltration k` with `1 ≤ k`, for every group homomorphism `χ` intertwined by every unit of
`Module.End F V`, with a pointwise conclusion: there is `η` on the image of the determinant with
`χ g = η (det.rangeRestrict g)` for every `g`. Its proof eliminates off-diagonal entries with
transvections in the unit filtration subgroup and uses no continuity of `χ`; see the Markdown page
of that module. So the theorem here holds for every homomorphism `χ`, without the finite depth of
triviality that BK93's descent on p. 78 starts from.

## The proof

After introducing `F`, `V`, `L`, `m`, `χ` and the intertwining hypothesis `hI`, the proof
applies `intertwinedUnitCharacter` with `k = m + 1`, the inequality `1 ≤ m + 1` being
`Nat.succ_pos m`, to the same `χ` and `hI`. The determinant homomorphism of that statement at
`k = m + 1` is, by definition, the homomorphism `d` of the target, so this gives `η : d.range →* ℂˣ`
with `χ g = η (d.rangeRestrict g)` for every `g`. The extensionality lemma `MonoidHom.ext` turns
this pointwise identity into the equality `χ = η.comp d.rangeRestrict`, and `φ = η` is the
required homomorphism.

The theorem depends on the axioms `propext`, `Classical.choice` and `Quot.sound` only.
