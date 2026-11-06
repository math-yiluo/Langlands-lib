# Irreducible quotient of the actual unitary Jacquet summand

This derived supporting construction implements the finite-generation and
irreducible-quotient choice used in Renard, *Représentations des groupes
réductifs p-adiques*, 9 July 2026 edition, VII.2.6, printed p.231 / PDF p.237
(registered source `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`).
Renard invokes VI.1.3 for finite generation and A.VI.3 for an irreducible
quotient of the chosen nonzero unitary Jacquet module. This pair isolates that
step with its geometric and splitting inputs explicit.

The field and representation-carrier universes are independent. The maps
`p : P ⟶ G`, `l : M ⟶ P`, and `r : U ⟶ P` are the supplied actual parabolic,
rational Levi and matching geometric radical, with their multiplication
isomorphism. The ambient rational points have their canonical topology and
the stated local compactness and nonarchimedean-group instances.

`unitaryJacquetPart_moduleFinite_of_isCompl` assumes compactness of the
literal left quotient by `pointImage p`, irreducibility of the ambient smooth
representation, and complementarity of its published unitary and nonunitary
Jacquet submodules. Irreducibility supplies finite generation over the ambient
group algebra. The published `JacquetFiniteGeneration.finite_of_compactQuotient`,
applied to the actual point-image semidirect decomposition, supplies finite
generation of the normalized Jacquet module over the literal Levi image.
The existing `SmoothRep.complementaryDesc` with the identity on the unitary
part and zero on the nonunitary part gives a projection. Its restriction to
the unitary inclusion is the identity, so it is surjective. The
intertwiner/group-algebra correspondence and `Module.Finite.of_surjective`
then transfer finite generation to this actual unitary subrepresentation.

`UnitaryJacquetIrreducibleQuotientData` stores a smooth representation of
`M(F)`, its irreducibility, an actual morphism from
`leviUnitaryJacquetModule`, and surjectivity of that morphism. The Levi has the
published `leviPointTopology`. `unitaryJacquetIrreducibleQuotient` chooses
these data when the literal unitary summand is also nontrivial. It reuses
`JacquetCommonConstituent.exists_irreducible_quotient_of_moduleFinite`, rather
than repeating the maximal-submodule argument. Pullback along
`leviPointsEquiv` retains the vector carrier and surjective map and transports
irreducibility along the surjective group equivalence.

The construction does not prove the complementary splitting, compactness of
the parabolic quotient, existence of a minimal parabolic with nonzero unitary
part, temperedness or square-integrability of the selected quotient, or its
extension to the full Jacquet module. It proves none of the three
unconditional VII.2.6 statements. It does not require ambient temperedness;
the explicit inputs are sufficient for this algebraic step alone.
