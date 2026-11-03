# Intrinsic uniformizer sections for every actual split torus

The theorem
`Langlands.GroupScheme.CocharacterUniformizer.splitTorusUniformizerSection.{u}`
proves exactly the published proposition
`Langlands.GroupScheme.CocharacterUniformizer.SplitTorusUniformizerSectionStatement.{u}`.
It applies to every actual split commutative group scheme over every
nonarchimedean local field in universe `u`, with the hypotheses and the intrinsic
section of `CocharacterUniformizer` unchanged.

The source convention is Renard, *Représentations des groupes réductifs
p-adiques*, 9 July 2026 French edition, V.2.5, printed page 107/PDF page 113,
registered as `renard-2026-representations-groupes-reductifs-padiques`.
There the uniformizer gives a lift of the cocharacter lattice into the rational
points of a split torus. This module implements the integral-dual argument for
that construction using the Library's actual character and cocharacter lattices.
The helper lemmas below are derived proofs about the published constructions;
they introduce no new section or additional hypotheses.

Write `π = SplitTorusValuation.uniformizerUnit F`, `X` for
`characterLattice A`, and `Y` for `cocharacterLattice A`. The map under
consideration is the published homomorphism
`latticeSection F A : Multiplicative Y →* rationalPoints A.toGrp`, namely
`c ↦ c(π)`. Its target is the actual rational-point group. The valuation and
common norm kernel are respectively
`Plancherel.rationalCharacterValuation A.toGrp` and
`Plancherel.rationalCommonNormKernel A.toGrp`.

The imported `CocharacterUniformizerEvaluation` lemma
`rationalCharacterEval_cocharacterPoints` proves, without a local-field
or splitness assumption, that evaluating a character `α` after a cocharacter
`c` at a field unit `a` gives `a ^ latticePairing A α c`.
The Lean proof rewrites the composite group-scheme homomorphism as the
`gmEndEquiv` inverse of its integer pairing and uses the published all-test-point
power-map identity `gmEndEquiv_symm_comp`. Applying the actual affine-point
equivalence then gives the asserted equality of units.

`latticePairing_isPerfPair` obtains a finite split presentation from
`IsSplitTorus A.toGrp`. It turns the group-object isomorphism into an
isomorphism of commutative group schemes and applies the published
`latticePairing_isPerfPair_of_split` from
`Langlands.GroupScheme.Torus.WeilRestrictionNormOneCharacters`.
Thus the integral pairing is perfect on the actual lattices of `A`; coordinates
are used only to supply this existing perfectness theorem. In particular,
evaluation in the second argument identifies `Y` with the integral linear dual
of `X`.

The imported `rationalCharacterValuation_latticeSection` applies the first evaluation
identity at the same chosen `π`. The order map sends an integer power to the
corresponding integer multiple, and the published
`SplitTorusValuation.fieldOrderUnits_uniformizerUnit` says that `π` has order
one. Consequently the actual rational-character valuation of `c(π)` at `α`
is exactly `latticePairing A α c`. This formula needs no splitness assumption.

`mem_normKernel_mul_section_inv_iff` uses the published
`Plancherel.mem_rationalCommonNormKernel_iff_valuation`. The valuation of
`a * (latticeSection F A c)⁻¹` is the valuation of `a` minus the pairing
functional of `c`. The character-lattice equivalence then proves that this
point belongs to the actual common norm kernel exactly when those two integer
functionals agree on every actual character.

`isUniformizerLatticeSection` assembles the three required conclusions:

- If two section values agree, their valuations agree on all characters.
  Injectivity of the second-argument map of the perfect pairing then identifies
  the two cocharacters, proving injectivity of `latticeSection`.
- The valuation formula is the lemma already established.
- For any rational point `a`, its actual character valuation, transported through
  `rationalCharacters.equivCharacterLattice A`, is an integral linear functional
  on `X`. Surjectivity of the second-argument map of the perfect pairing supplies
  a cocharacter representing it. The norm-kernel criterion gives the required
  representative, and injectivity of that same map proves its uniqueness.

Finally `splitTorusUniformizerSection` introduces the universally quantified
field, instances, actual torus and splitness hypothesis and applies
`isUniformizerLatticeSection`. The proof retains arbitrary universe `u`, both
characteristics and the rank-zero case. It establishes the three conjuncts of
the stated intrinsic section theorem.
