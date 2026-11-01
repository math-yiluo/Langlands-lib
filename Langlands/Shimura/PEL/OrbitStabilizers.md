# Coset detection for free right actions on level orbits

This internal deduction complements `OrbitFibers`. Let `G` act on the right
of `X`, with `right x g = MulOpposite.op g • x`, and assume that for each
`x` the map `g ↦ right x g` is injective. For subgroups `U,V` and actual
transporters `g,h` from `U` to `V`, their translations of any given
`U`-orbit agree if and only if `g⁻¹ * h ∈ V`.

The proof uses the same representative of the source orbit for both
translations. Equality of target orbits supplies `a ∈ V` with
`x h = (x g) a`. The action law and freeness give `h = g a`, which proves
the coset condition. Conversely that condition supplies the witness
`a = g⁻¹ h` in the orbit relation. The stabilizer corollary takes `h = 1`
and uses closure under inversion. Quotient induction and subtype
extensionality transfer the results to orbits fixed by a commuting
monodromy group `Γ`. Neither normality nor transitivity on `X` is needed.

The statements use the original `RightOrbit.translate` and
`InvariantOrbit.translate` maps. They are derived group-action results,
authored by Worker 57, rather than additional assertions attributed to
Harris–Taylor. Their intended use is uniqueness of the translating
coset for actual compatible level structures on one fixed polarized
object. They supply no claim about rational self-isogenies or freeness
after quotienting polarized objects by rational isogeny.
