# Formal intertwining of strata

Source: Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups*
(1993), `bushnell-kutzko-1993-admissible-dual-gln`, (1.5.7), printed p. 44,
and (1.5.11), printed p. 46 (PDF pp. 56, 58).

`Stratum.formalIntertwining S T` is the subset of
`G = (Module.End K V)ˣ` consisting of `g` for which there is
`y ∈ S.coset` with `g⁻¹ y g ∈ T.coset`. This is precisely the
nonempty intersection of the conjugate of the first coset with the
second coset, with the conjugation direction specified in (1.5.11).
The two orders, depths and levels may differ.

`Stratum.formalSelfIntertwining S` takes `T = S`, giving (1.5.7).
The cosets and radical powers are the definitions already used in
`Stratum`; no equivalence invariance or intertwining theorem is a
definition field.

The ring-and-field generality is inherited from `Stratum` and allows
the same definitions both over the original local field and in
centralizers over extension fields.
