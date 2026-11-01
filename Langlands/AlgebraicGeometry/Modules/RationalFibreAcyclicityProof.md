# Open-local rational-fibre acyclicity: proof

Author: Worker 1159.

The theorem
`Langlands.AlgebraicGeometry.Modules.rationalFibreAcyclicity.{u}` has complete
type
`Langlands.AlgebraicGeometry.Modules.RationalFibreAcyclicityStatement.{u}`.
It proves the published proposition with no additional premises.

For an algebraically closed field `K : Type u`, a locally finite-type
structure morphism `g : Y ⟶ Spec K`, a smooth proper morphism `f : X ⟶ Y`,
an actual line bundle `Q` on `X`, and an arbitrary open `U` of `Y`, the
proposition assumes vanishing of the actual relative cohomology of `Q` on
every `K`-rational fibre over `U`. It concludes that
`(Scheme.Modules.pullback U.ι).obj ((DerivedSections.higherDirectImage f n).obj Q.obj)`
is a zero object for every `n : ℕ`. Both the fibre hypothesis and the
conclusion include degree zero.

## Implemented proof

The proof introduces precisely the quantified data and hypotheses of
`RationalFibreAcyclicityStatement`. Its geometric hypotheses are explicit
arguments, whereas the published helper expects instances. The three
anonymous `let` declarations install the given proofs of `LocallyOfFiniteType g`,
`Smooth f`, and `IsProper f` as local instances.

It then applies
`DerivedSections.isZero_pullback_higherDirectImage_of_rationalFibres` from
[RationalFibreVanishing](RationalFibreVanishing.md), with arguments
`universalPerfectSections K g f Q U hQ n`. Here `hQ` is exactly the
statement's rational-fibre hypothesis: the point satisfies
`x ≫ U.ι ≫ g = 𝟙 (Spec K)`, and the coefficient on
`pullback f (x ≫ U.ι)` is the ordinary module pullback of `Q.obj` along
`pullback.fst`. The helper's conclusion is exactly the required zero-object
assertion for the ordinary pullback along `U.ι` of the actual higher direct
image.

The helper's additional argument `hups` is discharged by the published
theorem `universalPerfectSections.{u}` from
[UniversalPerfectSectionsProof](UniversalPerfectSectionsProof.md). That
theorem has complete type `UniversalPerfectSectionsStatement.{u}`, with no
extra assumptions. Thus universal perfect sections is supplied by a proof
inside this implementation and is not an outer premise of the new theorem.

## Provenance and scope

This is an internal deduction from the two published proofs just named.
The rational-fibre helper already implements rational-point and
residue-field transport, iterated-fibre comparisons, perfect-complex
acyclicity detection, and detection of higher-direct-image vanishing on
affine opens. This file reuses that implementation. The universal
perfect-sections proof supplies its geometric input through the published
Čech and noetherian-approximation route described in its companion account.
The original-source provenance of the target remains in
[RationalFibreAcyclicityStatement](RationalFibreAcyclicityStatement.md).

The result retains arbitrary universe `u`, every characteristic, and
arbitrary open `U`. No projectivity, reducedness, connectedness, group law,
positive dimension, or global finite-type assumption is added. Its
conclusion is open-local vanishing of higher direct images; it asserts no
total cohomology vanishing, finite-support acyclicity, or abelian-square
projection theorem.
