# Selecting generalized weights of a central action

This internal algebraic helper is derived from the generalized weight spaces of
Renard 2026, VII.1.1 (printed p.220 / PDF p.226) and the decomposition step used
in VII.2.3 and VII.2.5 (printed pp.229–230 / PDF pp.235–236).
The source is the registered 9 July 2026 edition,
`renard-2026-representations-groupes-reductifs-padiques`.
The predicate selecting characters is arbitrary; choosing zero normalized real
part is the intended application to the unitary part. This module does not
prove the tempered geometric lemma.

`selectedWeightPart` is the literal sum of the existing compact-open uniform
generalized weight subrepresentations satisfying the chosen predicate.
Intertwiners preserve that sum. For a smooth representation, the selected sum
and its complementary selection are disjoint by independence of generalized
weights. Their sum is the sum of all generalized weight spaces.

If the source weight spaces span and the target representation is smooth, a
surjective intertwiner restricts to a surjection on the selected parts. Under
the same spanning and smoothness conditions, an injective intertwiner reflects
membership in the selected part. Neither assertion assumes target admissibility.
Both proofs split a source vector into its selected and complementary pieces.
Their images belong to the respective target parts; disjointness forces the
unselected image to vanish. Surjectivity then gives the selected lift, while
injectivity makes the unselected source vector vanish.
