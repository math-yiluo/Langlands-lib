# Morphism equality from dense actual rational points

This internal helper uses the published `HasDenseRationalPoints` predicate
from `RationalDensityStatement`: the union of the images of all actual
ground-field sections is Zariski dense.

For arbitrary field `k`, reduced relative scheme `X` and separated relative
scheme `Y`, `hom_ext_of_denseRationalPoints` proves that two relative
morphisms `X ⟶ Y` agreeing after every rational section are equal, provided
`X` has dense rational points. Neither finite type nor algebraic closedness
is assumed; density is an explicit premise.

The construction `rationalPointEqualizerLift` lifts each rational section
where the two morphisms agree to their actual categorical equalizer.
The proof places the dense union of rational images inside the range of the
equalizer inclusion. This makes that inclusion dominant. Mathlib's
`ext_of_isDominant_of_isSeparated`, using reducedness of `X` and
separatedness of `Y`, then proves equality. It does not identify residue
fields or replace scheme morphisms by functions on rational points.

This is derived infrastructure for eliminating parameter families with a
wound target. It supplies no rational-density theorem, unipotent-group
structure theorem, or proof of the full woundness criterion.
