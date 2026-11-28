# Fixed-level finiteness for orbit products of segment heads

Let `E` be a finite extension of `ℚ_p` with supplied topological data `T`.
Let `F` be a field equipped with a topology and an algebra structure on
`E`. Take an `F`-algebra automorphism `σ` of `E` and assume that `T` gives
`E` its `F`-module topology (`IsModuleTopology F E.Carrier`).
`SegmentOrbitFixedLevelStatement` fixes the positive segment length `s`,
the orbit length `t` and the positive rank `r` of the segment's
supercuspidal base. For a compact open subgroup of `GL_r(E)`, it gives
a finite determinant-twist cover of irreducible smooth complex
representations on `GL_n(E)` given by normalized orbit products of
segment heads with `t * (s * r) = n`. The supercuspidal base must have a
nonzero fixed vector at the supplied subgroup. The base field, extension
field and product carrier universes are independent. The segment head
and its base are compared in the maximum of the extension and carrier
universes.

The segment construction uses Zelevinsky (1980), §§9.1 and 9.3. The normalized
orbit product is the one in Henniart–Lemaire (2011), §II.4.12. The
finiteness argument combines these constructions with the finite cover of
supercuspidals at a compact open level, from Bernstein–Zelevinsky (1976),
§§3.20–3.29 and 4.14–4.16.

For each supercuspidal family in that cover, Lean chooses one irreducible
orbit product when it has a representative of the prescribed shape.
Two bases covered by the same family differ by the quotient of their
determinant parameters. Segment induction commutes with that character
twist, and the unique irreducible heads give an equivalence on the seed
representations. The `F`-module topology makes `σ` and its inverse
continuous. Invariance of the normalized absolute value then gives
invariance of the valuation under every power of `σ`, so the same
character twists every block of the orbit product. Applying
`sigmaOrbitDeterminantTwist` and the normalized product congruence
transports the seed equivalence to the product in the original carrier
universe.
