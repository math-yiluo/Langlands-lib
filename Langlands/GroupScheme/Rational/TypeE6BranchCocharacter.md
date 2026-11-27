# The split cocharacter at the short-arm end of the E₆ diagram

`NumberFieldTotallyComplexTypeE6BranchDistinguishedStatement` states that Bourbaki's
simple vertex α₂ is distinguished in the actual Tits index of a simply connected,
absolutely almost-simple E₆ group over a number field without real places. It uses
the same field, group and numbered Cartan hypotheses as
`NumberFieldTotallyComplexTypeE6VanishingStatement`. In `CartanMatrix.E 6`, vertex `1`
is α₂, the end of the short arm attached to the trivalent vertex α₄. The code uses
membership in `d.distinguishedVertices`, meaning that the simple root has nonzero
restriction to the actual maximal split torus. The statement covers both inner and
outer forms.

## Construction from a marked vertex

The cocharacter construction works over an arbitrary field. The E₆ diagram has
identity and arm exchange as its two symmetries. Both fix the short-arm end, so
`TitsIndexData.star_eq_typeE6Branch` makes that vertex a singleton orbit. By
`titsIndexRelativeSimpleRoots`, when the vertex is distinguished its restriction is
a simple relative root and differs from the restrictions of all other distinguished
vertices. The rational independence of the simple relative roots and
`IsSplitTorus.exists_scaled_pairings` give an integral cocharacter pairing positively
with that simple relative root and vanishing at all other simple relative roots.
The nondistinguished vertices already have zero restriction. This proves
`TitsIndexData.exists_scaled_typeE6BranchCocharacter`.

For a simply connected group, the absolute simple coroots are an integral basis.
In this basis the vector `(1, 2, 2, 3, 2, 1)` pairs to `1` at vertex `1` and to `0`
at all other simple vertices. This is the cocharacter `typeE6BranchCoweight`, and
the six Cartan equations determine it uniquely. Consequently the cocharacter just
constructed on the split torus becomes a positive integral multiple of this vector
in the absolute torus. Cocharacters factoring through a closed subgroup form a
saturated submodule, so the vector itself lies in the cocharacter lattice of the
base-changed split torus. The base-change equivalence for the split torus then gives
the rational cocharacter. The restricted root at vertex `1` is a retraction because
the pairing is `1`. The section is a closed immersion, and composing with the
maximal split torus inclusion gives the closed copy of `Gm` in
`TitsIndexData.exists_typeE6BranchCocharacter`.

## Source

Platonov and Rapinchuk, *Algebraic Groups and Number Theory* (1994), registered as
`platonov-rapinchuk-1994-algebraic-groups-number-theory`, retained PDF SHA-256
`c333b953ca0ace6306663f648cd853a75da55023bf873e0ef2688d997216717f`. In §6.8, the
inner-form argument on printed pp. 382–383 (one-based PDF pp. 392–393) uses isotropy
and excludes the D₄ anisotropic kernel from the index list (6.57). The outer-form
argument on printed p. 385 (PDF p. 395) uses the corresponding exclusion in (6.53)
on printed p. 379 (PDF p. 389). The resulting marked α₂ yields the split line cut out
by the remaining five simple roots. The Lean construction identifies its primitive
cocharacter by the simple-root pairings and assumes the marking.
