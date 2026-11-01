# Closed irreducible images from discrete valuative existence

`Langlands.AlgebraicGeometry.discreteValuativeClosedIrreducibleImages.{u}`
proves exactly the published
`Langlands.AlgebraicGeometry.DiscreteValuativeClosedIrreducibleImagesStatement.{u}`.
For every locally noetherian scheme `S` and every separated, locally finite
type morphism `p : X ⟶ S`, the actual discrete valuative existence premise
implies that every closed irreducible subset of `X` has closed image in `S`.
There are no additional outer hypotheses, and the universe is arbitrary.

The target is the displayed-base consequence of Grothendieck and
Dieudonne, *EGA IV*, fourth part (1967), Remark 18.10.20, printed
pp.167–168. In the registered PDF the remark begins on zero-based page
165 and its closed-image characterization is on page 166. The source is
`grothendieck-dieudonne-ega-iv4-1967`, SHA256
`b4277fb99c6edf8feec5b01f54368e4b8521bcd52871316c0edf6ff4ae69389e`.
The original List 3 errata check is recorded with the published target.
The proof here gives a direct specialization-lifting argument, using
Mathlib and the Library's existing DVR domination theorem, rather than
formalizing the full essential-properness equivalence in the remark.

The supporting theorem
`DiscreteValuativeCriterion.Existence.specializingMap` starts with
`x : X` and a specialization `p x ⤳ y` in `S`. When `p x = y`, the
point `x` itself is the required lift. Otherwise consider the ring map
from the stalk of `S` at `y` to the residue field of `X` at `x`, obtained
from the specialization stalk map, the morphism's stalk map and the
residue quotient. The `DiscreteValuativeSchemeAdapter` module shows
that it is essentially of finite type and that a local such map would
force `p x = y`. Its domain is noetherian by local noetherianity of `S`.

The `DiscreteValuationFactor` module therefore provides a DVR valuation
subring `A` of that same residue field, containing the ring map's image,
with a local factorization from the stalk at `y`. Taking spectra gives
an actual `ValuativeCommSq p`, whose field is precisely the chosen
residue field, with its canonical fraction-field structure over `A`,
whose top map is `X.fromSpecResidueField x`, and whose bottom map is the
spectrum of the local factor followed by `S.fromSpecStalk y`. The
commutativity proof uses the naturality of the stalk and specialization
maps. The premise is applied directly to this square and its proved
`IsDiscreteValuationRing A` instance; its conclusion is the square's
actual `HasLift`.

Evaluate that lift at the closed point of `Spec A`. Continuity shows
that this point specializes from `x`, because every point of `Spec A`
specializes to its closed point and the lift restricts to the original
residue-field map. The bottom-map identity and locality show that the
lifted point lies over `y`. This proves `SpecializingMap p`. Finally,
the published `closedIrreducibleImages_iff_specializingMap` equivalence
gives the exact target.

Only local noetherianity and local finite type are used by the
supporting specialization theorem. The exact target retains its
separatedness hypothesis. No quasi-compactness, finite type, global
noetherianity, integrality, normality, unramifiedness, properness,
dimension or rank hypothesis is introduced. The argument uses no
full arbitrary-valuation existence premise and does not assume
closedness of any image. It concludes the stated closed-image property
on the displayed base.

The finite-generator DVR factorization was contributed by Worker 208;
the scheme adapters and final assembly were contributed by Worker 336.
