# Standard Levis and cocharacter annihilators

This internal auxiliary development defines
`cocharacterAnnihilatorCentralizer i J` as the intersection of the dynamic
centralizers of all cocharacters whose lattice pairing with every character
in `J` is zero. It is a subgroup functor on every test scheme. It makes no
choice of chamber or standard cocharacter.

`Dynamic.centralizingCocharacters i g` is the integer submodule of
cocharacters through `T` that centralize a given point `g`. The proof uses
the published equivalence between the dynamic centralizer of a
multiplicative-group homomorphism and its whole-group centralizer. Evaluation
of a sum of cocharacters is a product of points, and evaluation of an
integer multiple is an integer power. Commutation is preserved by products
and integer powers.

`IsStandardCocharacter.exists_add_zsmul` assumes that the actual simple-root
set is finite and that a standard cocharacter `zeta₀` is given. For every
cocharacter `zeta` vanishing on `J`, it constructs an integer `m` such that
`zeta + m • zeta₀` is standard for `J`. The finite set of the negatives of
the pairings with `zeta` has an upper bound `b`; taking `m = max b 0 + 1`
makes every required positive pairing strictly positive, because each
positive integral pairing with `zeta₀` is at least one.

`standardLevi_eq_cocharacterAnnihilatorCentralizer` assumes finite simple
roots and existence of one standard cocharacter. A point in the standard
Levi centralizes both `zeta₀` and the shifted standard cocharacter. The
integer-submodule property then shows that it centralizes `zeta`. The
reverse inclusion follows directly because every standard cocharacter
vanishes on `J`.

These lemmas are internal consequences of the published definitions and
elementary integer inequalities. They do not establish finiteness or
standard-cocharacter existence for general reductive groups. They do not
prove the unconditional standard-Levi conjugation target. Those structural
premises remain explicit in the auxiliary equality.
