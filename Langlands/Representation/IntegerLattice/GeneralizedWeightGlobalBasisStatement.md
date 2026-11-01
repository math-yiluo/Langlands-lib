# One global block basis for all actual integer-lattice actions

Statement prepared by Worker 709; source comparison and submission by
Worker 1195. This proposition supplies no proof. Its
actual construction is imported from the published
`Langlands.Representation.IntegerLattice.GeneralizedWeightBlock` module.

`Langlands.CommutingTupleGeneralizedWeightGlobalBasisStatement` quantifies
over every natural `d`, finite-dimensional complex `V : Type u`, and the
actual commuting invertible tuple `A`. For the entire actual block family
`W_c = generalizedWeightBlock A c`, it asserts the existence of

- local bases `b c` indexed by `Fin (Module.finrank ℂ W_c)`;
- an ambient basis `B` indexed by
  `Σ c : Fin d → ℂˣ, Fin (Module.finrank ℂ W_c)`.

Both bases precede all lattice-point quantifiers. Their five properties are:

1. `B ⟨c,j⟩ = (b c j : V)`, identifying the actual ambient basis vector
   with the embedded local basis vector.
2. Every normalized difference on `W_c` is strictly upper triangular in
   `b c`: its row `i`, column `j` vanishes when `j ≤ i`.
3. For every lattice point `n`, the matrix of the actual ambient action
   has zero row `⟨c,i⟩`, column `⟨c',j⟩` whenever `c ≠ c'`.
4. Within the same block, every entry with `j < i` vanishes for every `n`.
5. Its diagonal entry at `⟨c,i⟩` equals the complex value of
   `coordinateCharacter c n` for every `n`.

All ambient action entries use `B.repr` of the actual tuple representation applied
to an actual basis vector. No matrix equality for an unrelated action or
arbitrary chosen family of invariant spaces is substituted. The embedding
equation identifies local and ambient coordinates without a dependent
transport between different labels.

There is no supplied global basis, support enumeration, decomposition,
nilpotence or triangularization premise. The sigma index ranges over all
unit labels, and every zero block contributes an empty fiber.
Finite-dimensionality and the actual decomposition make the resulting
index finite during the proof; an extra `Fintype` hypothesis on the full
label type would wrongly restrict the assertion and is absent. The
rank-zero case has the one full-space block and identity action. For zero
`V` the total index is empty. The carrier universe is arbitrary.

The source is Renard, *Représentations des groupes réductifs p-adiques*,
9 July 2026, Appendix C.III, printed p.280 / PDF286, the initial choice
of one common basis in which every `U(n)` is block diagonal and has upper
triangular blocks with character diagonal. Registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
PDF285–286 were read directly for this draft. This is a derived concrete
coordinate formulation indexed by the actual intersections, rather than
the source's finite numbered list. It also records that the same local
bases make the normalized differences strictly upper triangular.

An intended proof can assemble the local bases with
`DirectSum.IsInternal.collectedBasis` using the separately owned actual
decomposition theorem, and compare same-block and different-block
coordinates. The all-integer local matrix properties still require proof,
for example from the finite binomial products. This paragraph is a proof
plan, not proof evidence.

The registered supplementary 2010 errata
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
were read at PDF18–19. The C.III correction changes only the later product
parentheses, already incorporated in 2026 PDF286.
