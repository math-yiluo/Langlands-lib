# Harish-Chandra finiteness from the description of the Bernstein centre

`HarishChandraFinitenessFromCenterFunctionsStatement` derives
`HarishChandraFinitenessStatement` from the global scalar description
`BernsteinCenterFunctionsStatement`. For an actual rational parabolic
`P = MN` and any ring homomorphism `φ` from the centre of the smooth
representation category of `G` to that of `M` compatible with normalized
induction, the latter centre is a finite module over the former
through `φ`.

The proof chooses a standard Bernstein family containing the specified
parabolic, Levi and radical, and gives `M` the induced standard family.
The global scalar description identifies the two centres with their
products of Bernstein component rings by ring isomorphisms `eG` and
`eM`. Write `ψ` for restriction on those products.

To show that `eM (φ z) = ψ (eG z)`, the proof evaluates both sides at
each character of each chosen Levi datum. Evaluation of the first side
is the scalar of `φ z` on the normalized induction of the twisted datum
inside `M`. By induction compatibility and the induction-in-stages
comparison for the represented parabolic, this is the scalar of `z` on
the twisted induction of the transported datum in `G`. The evaluation
law of `ψ` identifies the second side with that same scalar. Since
evaluations determine the functions at every coordinate, the two
tuples agree.

It follows that `φ` is the composite of `eG`, the finite ring map `ψ`,
and `eM.symm`. Finiteness composes, and the module structure of this
finite ring map agrees with `Module.compHom _ φ` in the statement.

This implements the finiteness in David Renard, *Représentations des
groupes réductifs p-adiques*, French edition of 9 July 2026, VI.10.5
(printed p. 213, PDF p. 219). The product presentation and evaluation
use VI.10.4, Theorem and Remark 1 (printed pp. 211–212, PDF pp. 217–218),
and the restriction represents pullback along the Levi map of VI.7.3
(printed p. 185, PDF p. 191). The source is registered as
`renard-2026-representations-groupes-reductifs-padiques` with SHA-256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
