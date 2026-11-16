# Determinant lines of finite locally free module sheaves

This derived construction starts from actual module sheaves on an arbitrary
scheme in universe `u`. `HasFiniteLocalBasis M` means that a single local
generator datum is both locally free and finite type. The rank may vary from
chart to chart. There is no global basis, constant rank, connectedness,
nonempty-base or nontrivial-section-ring hypothesis.

`FiniteLocalFrames M` packages a covering of opens, a natural-number rank on
each open, and actual isomorphisms from free module sheaves on
`ULift (Fin rank)` to the module on that open. `ofLocalBasis` constructs this
data from any certified finite local basis datum. Each finite generator index
type is enumerated by `Fintype.equivFin`, and the free-sheaf functor transports
this equivalence to a free-sheaf isomorphism. This is composed with the actual
local presentation isomorphism. Conversely, the free generators in any such
frame system give a single finite local basis witness.

`lineBundle` glues the actual mixed determinant transition units using
`VariableDeterminantFrames`. `isoMap` applies the already constructed
determinant map to any actual module-sheaf isomorphism. Its identity and
composition equations are equalities of actual line-bundle isomorphisms.
`changeIso` is the determinant map of the identity between two independent
frame systems; its transitivity and its compatibility with `isoMap` follow
from this composition equation.

`finiteLocallyFreeDeterminant h` chooses local frames from the proved
finite local basis condition and takes their glued determinant line.
`finiteLocallyFreeDeterminantIso` supplies the corresponding determinant of
each actual isomorphism and preserves identity and composition.
`finiteLocallyFreeDeterminantPresentationIso` compares this choice to every
supplied covering frame system. The final naturality equation says that these
comparisons intertwine the determinant of every actual module isomorphism.
Together with transitivity of `changeIso`, this gives coherent independence
of the frame presentation.

Pulling back each free chart gives `FiniteLocalFrames.pullback` for any
scheme morphism. `pullbackIso` and its naturality equation are the actual
frame-level determinant pullback comparison, obtained from the existing
variable-rank pullback theorem. Preservation of `HasFiniteLocalBasis` also
follows from the published finite-local-basis pullback theorem. Coherence of
pullback on the *chosen* determinant lines is constructed separately.

The provenance is internal and derived: this module assembles the existing
variable-rank determinant, cover comparison, isomorphism and pullback APIs
with Mathlib's actual finite local generator data and free-sheaf functor.
It does not assert ampleness or representability of parabolic subgroups.
