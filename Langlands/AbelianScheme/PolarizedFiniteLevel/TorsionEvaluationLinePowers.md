# The level power of a cubic evaluation line is trivial

`Datum.torsionEvaluationLine r` is the pullback of the actual cubic bundle
along the torsion section with label `r`. Its underlying module is exactly
the codomain of `Datum.torsionEvaluation r`.

For a datum over any base scheme in its universe,
`Datum.isoClass_torsionCanonicalBundle_pow` computes the `n`-th power of the
class of the pullback of the canonical diagonal bundle along that section.
The diagonal formula identifies the class with the Poincaré class at
`(λ(Pᵣ), Pᵣ)`. The published theorem of the square, iterated in the
abelian-scheme variable while keeping the dual variable fixed, identifies
this power with the class at `(λ(Pᵣ), [n]Pᵣ)`. The section belongs to the
actual multiplication kernel. Its `n`-fold multiple is zero, where the
Poincaré class is trivial. No field, reducedness, or level invertibility
assumption is needed for this calculation.

The cubic bundle has the cube of the canonical class, and pullback
preserves tensor powers on classes. Thus the `n`-th power class of the
cubic evaluation line is trivial as well. The isomorphism-class
criterion gives `Datum.nonempty_torsionEvaluationLine_tensorPowIso`, an
actual isomorphism of that tensor-power sheaf to the structure module.
`Datum.torsionEvaluationLinePowerIso` chooses this isomorphism. This
choice does not come with a coherence assertion across base changes;
for the bracket map it can be fixed once on the given base and then
pulled back. No trivialization of the evaluation line itself is asserted.

This is a derived consequence of the Library's Poincaré point-class
formulas, torsion sections, and tensor powers of line-bundle classes.
