# Finite étale descent on affinoid algebra triangles

Take actual bounded maps `A → B → C` between presented affinoid algebras
over a complete ultrametric normed field. The algebra lemma shows that
`A → B` is finite Banach and algebraically finite étale when `B → C` and
`A → C` have both properties and the spectral map from `C` to `B` is
surjective.

`BoundedAlgHom.finiteFaithfullyFlatRetraction` chooses a bounded
`B`-linear retraction for a finite Banach faithfully flat map `B → C`.
A finite coefficient map onto `C` splits by projectivity.
The coordinates of the chosen lift of `1` generate the unit ideal by
faithful flatness. A linear functional on the coefficient module sends
this lift to `1`. The resulting retraction is bounded because the
finite Banach presentation gives coefficients with uniform norm
control.

`BoundedAlgHom.IsFiniteBanach.of_faithfullyFlat_comp_of_projective`
works with normed algebras over a normed field. Suppose that `A → C`
is finite Banach and that `C` is projective and faithfully flat over
`B`. Algebraic finiteness of `C` over `B` follows from finiteness over
`A`. The same coefficient splitting gives a `B`-linear retraction.
Applying it to the generators and the coefficient identities over `A`
gives coefficient lifts for `A → B`. If `D` bounds the lifts over `A`
for `A → C` and `L` bounds the map `B → C`, the new lift bound is
`D L`. The norm estimate uses boundedness of `B → C`, so the argument
applies before any affinoid presentation of `B` is supplied.
For presented affinoid algebras, the finite Banach faithfully flat map
`B → C` gives projectivity by finite presentation and flatness.
`BoundedAlgHom.IsFiniteBanach.of_faithfullyFlat_comp` uses this case.

Flatness over `A` descends by faithful flatness of `C` over `B`. Étaleness
of `B → C` identifies the base change of the relative differentials of
`B` over `A` with those of `C` over `A`. The latter vanish. Faithful
flatness gives unramifiedness, and Noetherianity of `A` gives finite
presentation from finiteness. Spectral surjectivity supplies faithful
flatness for the finite étale application. The argument allows trivial
norms and arbitrary finite positive polyradii.

This is a derived algebraic step for descent on finite affinoid pieces.
Its inputs come from the Library's coefficient maps, affinoid
Noetherianity and spectral criterion for faithful flatness and from
Mathlib's projectivity of finite presentation flat modules and its
formally étale base change for Kähler differentials.
