# Actual automorphism action and fixed full-level parameters

This internal construction concerns a supplied abelian scheme `A` over
`S`, a natural dimension index `g`, and a positive natural level `n`
invertible on `S`. It packages the actual action of family automorphisms
on the full-level parameter and constructs its fixed schemes. It uses
the existing exact prescribed ordered sections and every actual test
scheme `T` over `S`; it imposes no dimension, numerical torsion rank, or
nonemptiness hypothesis.

`fullLevelParameterAut` is a homomorphism from `Aut A` to the
automorphism group of the full-level parameter. Its identity and
multiplication laws are the identity and composition laws of
`fullLevelParameterIso`, with the categorical convention for
automorphism multiplication.

`fullLevelParameterIso_fixed_iff` identifies fixed parameter maps with
full levels whose exact prescribed ordered sections are fixed by the
pulled-back automorphism. Injectivity of the full-level classification
and of its section data proves the equivalence.

`FullLevel.mapTuple_eq_iff_torsionMap_eq` says that two actual family
morphisms agree on a supplied full level's ordered sections exactly when
their induced maps on the actual torsion schemes agree. One direction
uses `FullLevel.torsionMap_ext`; the reverse evaluates equality of the
torsion maps on each section through `kernelLevelEquiv`. Applying this
to the pulled-back automorphism and the identity gives
`fullLevelParameterIso_fixed_iff_torsion`.

`fullLevelParameterFixedScheme` is the actual equalizer in `Over S` of
the induced parameter automorphism and the identity.
`fullLevelParameterFixedHomMapEquiv` is the equalizer universal property,
expressed as an equivalence with the subtype of fixed parameter maps.
Composing with the full-level classification gives
`fullLevelParameterFixedHomEquiv`, the subtype of full levels whose
ordered sections are fixed.

The equalizer inclusion is the pullback of the parameter's diagonal.
Finite étaleness of the parameter makes this diagonal both an open
immersion and a closed immersion, using unramifiedness and separatedness.
Base change preserves those properties, so the equalizer inclusion is
both open and closed. Composing it with the finite étale parameter
structure map proves `fullLevelParameterFixedScheme_finiteEtale`.
`fullLevelParameterFixedFiniteEtaleCover` bundles this same equalizer as
an object of `Langlands.AlgebraicGeometry.FiniteEtale.Cover S`; its
underlying-object comparison is definitional. Here `Cover S` means the
category of finite étale schemes over `S` and does not assert
surjectivity.

All results are internal consequences of the supplied-family parameter
classification, its isomorphism transport and finite étale geometry,
and the ordered-section torsion detection theorem. They do not prove
that a family automorphism trivial on torsion is the identity, that the
automorphism action is faithful, or that an ambient moduli scheme exists.
