# Simultaneous equality as a closed subscheme

For families of maps `f j, g j : X ⟶ Y` of schemes over `S`, with `Y → S`
separated, `simultaneousEqualizer f g` is a closed subscheme of `X` over `S`.
Its defining ideal sheaf is the sum of the kernel ideals of the single
closed equalizers, indexed by all `j`. This uses Mathlib's joins of ideal
sheaves; no finiteness of the index set or reducedness of the schemes is
required. `simultaneousEqualizer_condition` states that the inclusion
satisfies every equality. Conversely, `simultaneousEqualizerLift` lifts an
arbitrary test map `a : T ⟶ X` on which every equality holds: the kernel of
each single equalizer lies in `a.left.ker`, hence so does their sum. The
lift composes to `a` by the universal property of a closed immersion and
is unique since the inclusion is monic.

`overHom_ext_of_schematicallyDominant` states that two maps over `S` to the
same separated target agree if they agree after a schematically dominant
map to their source. Its proof uses the single equalizer: the given map
factors through it, so the equalizer ideal is contained in the zero kernel
of the given map. Thus the equalizer inclusion is an isomorphism. This
checks equality of maps of schemes even when the source is nonreduced.

These are internal consequences of Mathlib's scheme-theoretic equalizer,
ideal sheaf and closed immersion APIs. The application to linear systems is
to cut out the translations that fix the images of a whole family of points.
No subgroup law, density theorem or quotient is part of this module.
