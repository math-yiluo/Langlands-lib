# Actual homomorphism descent along arbitrary surjective étale maps

This internal construction extends the existing fpqc homomorphism descent
argument to arbitrary surjective étale maps without a quasi-compactness
assumption. Both base schemes and all group schemes are arbitrary.

For two group schemes already over the base,
`Descent.EtaleHomDescent.hom` descends an actual upstairs homomorphism compatible
with their canonical descent data. The existing compatibility lemma proves that
the underlying map to the downstairs target is constant above equal projection
images. The projection is an fppf effective epimorphism, so it supplies an actual
descended scheme map. That map respects the structure maps by epimorphic
cancellation. Pullback recovers the given underlying map, and faithful monoidal
pullback reflects the unit and multiplication laws. Thus the descended map is
an actual group-scheme homomorphism.

`baseChange_hom` proves exact recovery; `unique` proves that it characterizes
the descended homomorphism.

`Descent.Solution.descendHomOfEtale` applies this construction through two
supplied actual solutions of possibly different data. Conjugating the supplied
upstairs map by the solution comparisons gives a map compatible with canonical
data. `baseChange_descendHomOfEtale` gives the recovery square and
`descendHomOfEtale_unique` its uniqueness.

The source of this module is the internal published `Descent.FpqcHomDescent`
construction and its compatibility lemma, together with fppf effective
epimorphisms and faithful pullback from Mathlib. No object-effectivity
assumption is introduced, and no descent solution is constructed here.
