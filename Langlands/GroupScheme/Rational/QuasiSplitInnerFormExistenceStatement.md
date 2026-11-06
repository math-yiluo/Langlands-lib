# Quasi-split inner forms of connected reductive field groups

`QuasiSplitInnerFormExistenceStatement.{u}` is an unproved proposition for
arbitrary universe `u`. For every field `K : Type u` and every actual
connected reductive group scheme `G` over `K`, it requires a
`QuasiSplitInnerForm G`.

The conclusion supplies a quasi-split ground-field model `H`, an actual
adjoint quotient `H → A` with quasi-split target, a finite Galois field
cover in the same universe, natural local isomorphisms from `H` to `G`
on every relative test, and an `A`-valued cocycle giving their discrepancy
under the actual inner action. Both quasi-splitness assertions retain
field-defined Borels that remain Borel over the algebraic closure.
Connected reductivity, the adjoint quotient and the cocycle keep their
existing scheme-theoretic meanings. No dimension, norm, perfectness,
characteristic, supplied Borel or supplied descent premise is assumed.

The structural source is Conrad, *Reductive group schemes* (2014),
Proposition 7.2.11, printed/PDF p.258. It constructs a quasi-split inner
form by the section of the automorphism group defined by a pinning.
The field discussion in Section 7.2, printed/PDF pp.250–252, describes
inner forms as twists by cocycles in the adjoint quotient and proves
in Proposition 7.2.2 that the fibers over outer forms consist precisely
of inner forms of each other. Source
`conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
No source-specific project errata note was found.

This is a derived concrete field formulation, not a literal transcription
of the cohomological statement. Its proof must construct the actual
adjoint quotient and its inner action, show its quasi-splitness, choose
finite Galois representatives in the universe of `K`, and pass from
inner twisting to the stated all-test local isomorphisms and discrepancy
equation. Those comparisons remain proof obligations. Acceptance of
this statement would provide a structural proof target; it would prove
neither its existence claim nor the dimension-one quasi-splitness theorem.
