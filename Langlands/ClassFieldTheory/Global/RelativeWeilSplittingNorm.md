# The splitting norm descended to base idele classes

Let `F` and `E` be number fields in `Type u`, with `E/F` Galois.
`ideleClassInclusionInvariants` is the actual inclusion of `C_F` into
`C_E`, written additively and with invariant codomain for the actual
relative Galois action. The published `ideleClassGaloisDescent` theorem
proves its injectivity and surjectivity onto this invariant submodule.
`ideleClassInvariantsEquiv` packages exactly that inclusion as an additive
equivalence. The symmetric equivalence is characterized by inclusion
back into `C_E`.

For a global class family `c`, `splittingNormToBase F E c` takes the
actual coinvariants of the chosen splitting representation defining the
relative Weil group. It applies the splitting norm with values in
coefficient invariants and then inverts the idele-class invariant
equivalence. Its values are actual base idele classes, written
additively. `ideleClassInclusion_splittingNormToBase` characterizes the
result by the existing inclusion into `C_E`.

`splittingNormToBase_bijective` assumes `FundamentalClass.Generates c`
and `FundamentalClass.Restriction c`. The chosen normalized representative
has cohomology class `c F E`, so the global Tate cup theorem gives the
all-degree cup bijectivity needed by `splittingNorm_bijective`.
Composition with Galois descent therefore proves bijectivity onto `C_F`.

This is an internal composition of the established actual splitting
construction, its norm theorem, the global idele-class cup input and
Galois descent. It neither changes the coefficient action nor selects
a new fundamental class family. Identifying the source coinvariants
with the relative Weil group's abelianization and comparing the map
with its actual transfer remain separate obligations.
