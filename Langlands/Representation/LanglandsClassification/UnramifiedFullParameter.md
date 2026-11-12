# The actual full torus parameter of a Levi character

This internal supporting unit identifies the full real torus parameter of an
actual unramified Levi character with every selected-coroot-annihilating lift
of its split-component parameter. When that parameter belongs to the published
open coroot chamber, its actual full parameter is strictly positive on the
unselected simple coroots. Its Weyl translates outside the standard Levi Weyl
subgroup consequently have a nonzero parabolic cone displacement.

The construction uses a compatible `ParabolicRootPresentation r` for the
specified maps `p : P → G`, `l : M → P` and `a : A → M`. In particular, its
maximal split torus, generic cocharacter, simple-root subset, all-test standard
Levi equality and split-component factor are the original published objects.
The field is a nonarchimedean local field with the canonical rational-point
topologies. Coroot comparison and the final cone conclusion additionally assume
that `G` is connected reductive and locally of finite type. The supplied
`RelativeRootReflectionData` remains explicit.

`standardLeviRepresentative` obtains the represented standard Levi from
compatibility and the closed Levi and parabolic embeddings. `leviTorusHom`
then uses the published `standardLeviTorusFactor` to map the ambient maximal
split torus into the specified Levi. Its composite with `l ≫ p` is the
original ambient torus embedding. Monomorphism cancellation proves that the
specified split-component factor followed by this map is exactly `a`.

`leviUnramifiedFullRealPart r ψ` is the normalized real part of the original
character `ψ` restricted along `r.leviTorusHom`. The kernel is open because the
unramified character has open kernel and rational-point maps are continuous.
Normalized real-part functoriality and the preceding factor identity prove
`restrict_leviUnramifiedFullRealPart`: restriction along the actual component
factor gives precisely the published `leviUnramifiedRealPart`.

The generic character helper uses an actual `IsNormalizingPoint` witness.
Its inverse torus automorphism acts by conjugation in the ambient group, and a
character into the abelian group of complex units kills that conjugation.
Real-part functoriality therefore makes the torus parameter invariant under
that automorphism and under the actual full real normalizer action.

`relativeWeylFullRealAction_leviUnramifiedFullRealPart` applies this argument to
the standard Levi Weyl subgroup. A normalizer representative of one of its
classes lies in the actual standard Levi. Compatibility lifts it through the
specified `l ≫ p`, and the existing monomorphism reflection lemma transports
its normalization witness into `M`. Thus the full parameter of `ψ` is fixed.

`pair_leviUnramifiedFullRealPart_selectedCoroot` uses the proved actual relative
Weyl Coxeter theorem. It identifies the supplied reflection representative of
each selected simple root with the corresponding Coxeter generator. The
Coxeter parabolic comparison places that generator in the actual standard
Levi Weyl subgroup. Its fixedness and the full real reflection formula give
`x - ⟨x, α̌⟩ α = x`. Pairing with the same coroot, whose pairing with its root
is two, forces `⟨x, α̌⟩ = 0`.

`leviUnramifiedFullRealPart_eq_of_restrict_eq` now applies the published
`eq_of_restrict_eq_of_selectedCoroot_pair_eq_zero`. Any full lift annihilating
the same selected coroots and having the same restriction is the actual
parameter. Applying this equality to the existential lift in
`restrictedCorootChamber` transfers strict positivity to that parameter.

Finally, `restrict_weyl_leviUnramifiedFullRealPart_eq_sub_nonzeroCone` combines
these pairing facts with the published dominant and strict Weyl displacement
theorems. For every actual Weyl element outside the actual Levi Weyl subgroup,
the restriction of its action on the full parameter equals the original
split-component parameter minus a nonzero vector in `r.nonnegCone`.

All results are internal consequences of the imported constructions and
theorems; no original-source assertion is newly transcribed here. The
geometric-piece character comparison, opposite-cone comparison, spectral
separation and full regularity theorem remain separate obligations.
