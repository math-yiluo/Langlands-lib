# Unitary Jacquet nonvanishing for a quotient of semisimple induction

This derived supporting construction implements the map reversal and
reciprocity step in Renard, *Représentations des groupes réductifs p-adiques*,
edition dated 9 July 2026, VII.2.6 theorem, uniqueness proof, printed p.231 /
PDF p.237. The source reverses a nonzero map from an induced geometric
piece to the second square-integrable representation using semisimplicity.
Tempered Frobenius reciprocity then makes the second unitary Jacquet
part nonzero. The VII.2.4 square-integrability criterion rules out a
proper second intersection parabolic.

The construction applies to an arbitrary actual represented parabolic
`p : P ⟶ G`, with its rational Levi `l`, geometric unipotent radical `r`,
semidirect multiplication witness and split component `ha`. The induction
is the published `leviInductionFunctor` and the unitary Jacquet module
is the literal `leviUnitaryJacquetModule`. The ambient and Levi point
topologies are their canonical published topologies. The field universe
`u`, inducing carrier universe `v` and target carrier universe `w` are
independent.

`unitaryJacquetMapOfSemisimpleInductionQuotient` assumes an actual
nonzero intertwiner from normalized induction of `σ` to an irreducible
`π`, semisimplicity of that induction, and normalized-exponent
temperedness of both `π` and `σ`. Irreducibility makes the given map
surjective. The proof converts it to a map of the associated
complex group-algebra modules and uses Mathlib's
`IsSemisimpleModule.lifting_property` to split this actual surjection.
Its right inverse is nonzero: composing a putative zero right inverse
with the original map would make that original map zero. The published
`temperedInductionUnitaryReciprocity` carries the right inverse to a
nonzero intertwiner from the actual unitary Jacquet module of `π`
to `σ`. Classical choice selects and returns the resulting proved
nonempty subtype of nonzero intertwiners.

`unitaryJacquetPart_ne_bot_of_semisimple_induction_quotient` uses this
map to prove the actual unitary Jacquet subrepresentation is not bottom.
If it were bottom, each of its vectors would be zero, making the
constructed map zero.

`isIso_of_squareIntegrable_semisimple_induction_quotient` is explicitly
conditional on the exact published
`TemperedSquareIntegrableUnitaryPartStatement`. It also assumes
square-integrability of `π` for a specified arbitrary Haar measure
on the quotient by the abstract center of its point group.
The central character needed by that criterion is extracted from
the square-integrability datum itself. Its forward implication makes
the unitary Jacquet part vanish if `p` is proper. This contradicts
the preceding theorem and proves `IsIso p`.

The input semisimplicity, temperedness, nonzero induction map and the
VII.2.4 criterion are retained explicitly. This file does not prove
the criterion, induction semisimplicity or temperedness, the geometric
lemma, or either intersection's required hypotheses. In the VII.2.6
application the parabolic is the second actual intersection parabolic
and `σ` is the conjugated inner unitary Jacquet module. Establishing
its temperedness and semisimplicity of its induction remains separate
work. No final VII.2.6 statement is proved or modified here.
