# Compatible dynamic presentations on a pointed etale neighbourhood

This internal construction combines two pointed presentations recovering the
same ambient residue cocharacter. It uses pointed presentation extension,
the published field dynamic classification, preservation of etale morphisms
by pullback and composition, and canonical pullback comparison coherence.
It introduces no new assertion from external literature.

`CompatiblePresentationData i j s` records an actual scheme `U`, an etale
projection `p : U → S`, a point `b : Spec κ(s) → U` over the canonical residue
map, and two ambient cocharacters over `U`. They present the ranges of the
actual pullbacks of `i` and `j`, respectively, as subgroup functors on all
test schemes. Their actual cocharacters after pullback along `b` are equal.
The equality has the same iterated-pullback target on both sides.

`compatiblePresentationsOfPointed` takes two pointed presentations recovering
a supplied common ambient cocharacter `ν`. The fibre product of their
etale projections carries the point induced by their two residue points.
Each cocharacter and its presentation pull back to the common base through
`pullbackCocharacter` and `pullbackCocharacter_presents`. The exact recovery
lemma identifies both values at the common point with `ν`, after the same
canonical direct-pullback comparison. Cancelling that comparison gives the
claimed equality of cocharacters.

`compatiblePresentations` assumes an arbitrary base scheme `S`, a reductive
`G`, two relative parabolics `i : P → G`, `j : Q → G`, a point `s : S`, and
equality of their canonical residue-fibre ranges. The published field dynamic
classification supplies a cocharacter presenting the first range. Equality
of ranges makes it present the second range as well. Applying
`pointedPresentation` to each and then the preceding fibre-product
construction gives the required data. There are no assumptions of global
closedness, affine or Noetherian base, or a supplied global presentation.
The construction works in one arbitrary universe and does not yet produce
a conjugating section.
