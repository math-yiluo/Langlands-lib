# Original stabilizer projection and source-radical image geometry

This internal adapter retains an explicit simultaneous dynamic realization
`R : D.DynamicRealization` of the original represented triples in the datum's
original common torus. It does not assert existence of that realization.

The original target Levi projection preserves the inverse conjugate of the
original source parabolic. Indeed, the latter is the dynamic parabolic of
the source cocharacter and is stable under the target cocharacter of the
same torus. The closed-stable projection theorem therefore applies to the
original target decomposition. Its restriction maps the full orbit
stabilizer onto the literal intersection parabolic inside the original
target Levi image. Each point of that intersection lifts through the
original target Levi section, proving surjectivity and the displayed image
equality without choosing another projection.

The inverse-conjugated source point and its original source projection
commute with ambient conjugation. The proof uses uniqueness of the
original conjugated semidirect decomposition: the conjugated projection
lies in its Levi and its inverse times the conjugated point lies in its
radical. Common-torus unipotent preservation for that same conjugated
decomposition then shows, in original source coordinates, that the source
projection preserves the forward conjugate of the original target radical.

For a point of the full stabilizer in the original target projection
kernel, its ambient point lies in the original target radical. Original
orbit conjugation puts its inducing-side point in the forward conjugate
of that radical. The preceding preservation law places the original
source projection in the literal intersection defining the source
radical. The original source Levi point equivalence is injective, so the
ambient intersection equality recovers membership in the actual source
radical on the source Levi's own points. This proves the reverse image
inclusion needed by the raw quotient comparison. The already constructed
literal radical lift proves the opposite inclusion and hence equality.

All declarations use no local field assumptions. The final source-image
declarations use the existing original source Levi point projection.
All original parabolics, radicals, projections, representatives and point maps are retained.
The simultaneous realization remains an explicit hypothesis throughout;
the module does not prove its existence, a modulus cancellation or the
closed normalized local orbit comparison.
