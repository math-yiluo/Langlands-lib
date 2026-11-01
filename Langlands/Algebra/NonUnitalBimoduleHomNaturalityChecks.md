# Natural-map and Hom-functor interface checks

Author: Worker 1174. This internal companion imports
`NonUnitalBimoduleHomNaturality`; that module's paired Markdown supplies the
source citations, proof explanations and mathematical limits. No new source
assertion is made here.

The private interface abbreviations spell out complete dependent function
types for `sourceMap`, `targetMap`, `rightSourceMap`, `homMap`,
`homMap_val`, `homCovariantFunctor`, `homContravariantFunctor` and both
`Functor.Additive` instances. Every ring, group and original action is an
explicit instance binder, supplied by name wherever it is used, and the Hom
carriers, their inherited groups and the
named residual actions `sourceAction`, `targetAction` and
`rightSourceAction` appear explicitly in the result types. Each `example`
assigns the corresponding unapplied declaration to that type, so binder
order and the maximum Hom carrier universe are tested on the full
declaration. The examples use arbitrary independent universes, then
unequal 0/1 assignments and their reversals. The universe linter is
disabled for these private abbreviations because their sort intentionally
takes a maximum of all universes; no type equality or kernel check is
disabled.

The `ThreeUniverses` section checks the composition laws of `homMap`,
`sourceMap` and `targetMap` through three carriers in the universes 0, 1
and 2 on each side, with residual rings in three different universes. It
also checks the pointwise value `g' (g (h (f (f' y))))` of the composite.

The `Competing` section places two ring instances on each scalar type, two
group instances on each carrier, alternative original actions and
alternative actions on the exact Hom carrier in scope. An explicit
application of `homMap` has exactly the named Hom bimodule type. The
bundled `sourceHom` and `targetHom` objects keep the named actions, and
both functors send the named bimodules to exactly the core `hom`. The
overlapping-instance linter is locally disabled for these intentional
examples only. `CompetingHomActions` keeps unique rings and groups but adds
competing instances of residual actions on both Hom carriers. It checks
that `homMap`, `sourceMap` and `targetMap` are linear for the scalar
endomorphisms of the named actions.

The subsingleton examples show that `homMap` is zero when the new source
`Y'` or the new target `Z'` is a subsingleton, and that the functor
objects are subsingletons when the varying carrier is.

The integer-zero examples choose zero original actions on `ℤ` for arbitrary
`S` and arbitrary unital residual rings `R` and `T`. The map
`H(id, id)` is the identity of the actual Hom bimodule, and it is nonzero:
equality with zero would give `(1 : ℤ) = 0` by evaluating the identity
Hom at `1`. Doubling both variables gives `H(2·id, 2·id)`, which evaluates
to `4`, while `H(id, id) + H(id, id)` evaluates to `2`; so `H` is not
jointly additive in `(f, g)`. The covariant functor sends the identity of
the zero-action `ℤ` bimodule to a nonzero map, while both residual actions
on its object, the actual nonzero Hom, have zero scalar endomorphisms even
though `R` and `T` are unital.

These checks establish interfaces and the stated examples. They do not
assert Hom nondegeneracy, tensor-Hom isomorphisms, adjunction, exactness,
coefficient-scalar or unitization compatibility, or any of the source's
forgetful or induction functors.
