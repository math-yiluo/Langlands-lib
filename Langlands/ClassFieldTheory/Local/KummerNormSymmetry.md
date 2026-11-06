# Kummer characters and finite-extension norm symmetry

This is derived support for norm separation. The definitions and theorems concern
actual fields, their unit groups, determinant norm subgroups and relative Galois
cohomology. All fields have a common arbitrary universe. The exponent `n` is a
nonzero natural number.

`KummerNorm.character` is Mathlib's `autEquivZmod`, restricted to its underlying
monoid homomorphism. Its inputs are an irreducible polynomial `X^n - a`, a
splitting field, and a primitive `n`th root of unity in the base field. The
character takes values in the multiplicative notation for `ZMod n` and is
injective. `character_action` fixes the positive convention: the automorphism
with coordinate `r` sends an `n`th root `alpha` of `a` to `zeta^r * alpha`.
The proof applies Mathlib's inverse-coordinate action formula to the standard
residue of the character, then cancels the coordinate equivalence.

`norm_iff_of_root_actions` concerns finite Galois extensions `L/K` and `R/K`
embedded compatibly in a common finite Galois extension `M/K`. It assumes two
injective characters with values in `ZMod n`, roots of base units `a` and `b`
in the additive notation for `M` units, and a fixed `n`-torsion unit recording
both root actions. Under exactly these hypotheses it proves
`b` belongs to the determinant norm subgroup for `L/K` if and only if `a`
belongs to that for `R/K`. The carry-cochain theorem says that the corresponding
two carry classes add to zero after inflation to `M`. The published cyclic
class criterion identifies norm membership with vanishing before inflation.
Injectivity of degree-two inflation in each finite Galois tower then proves
both implications.

`included_root_power` transports a unit root through a field tower.
`included_root_action` transports the normalized character action by the same
inclusion, using commutation with normal restriction of automorphisms.
`norm_iff_of_irreducible_radicals` specializes the preceding norm equivalence
to two irreducible radical splitting fields with a common primitive root and
specified unit roots. It proves the torsion and fixedness hypotheses for the
included base root of unity and supplies the transported root actions.
The existence of these fields, roots and their common overextension is retained
as hypotheses here. This module does not assert universal-norm divisibility or
the unconditional norm-separation target.

The normalization and symmetry calculation follow the Kummer-symbol argument
of Serre, *Local Fields*, XIV.2, Proposition 5 and Proposition 7(v), printed
pages 207–209. The formulation here is derived: it uses explicit carry classes
and injective relative inflation rather than introducing a Hilbert symbol or
Brauer algebra. The character implementation itself reuses Mathlib's existing
Kummer equivalence; all displayed norm claims are proved in Lean from the
stated hypotheses.
