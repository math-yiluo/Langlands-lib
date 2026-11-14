# Identifying a relative radical in an ambient dynamic presentation

This internal construction identifies the image in a reductive group of a
supplied relative unipotent radical of a supplied dynamic parabolic. The base
scheme and universe are arbitrary. The proposition
`DynamicRelativeLeviStatement` is an explicit hypothesis throughout; this module
does not prove it or the global existence and uniqueness statement.

`dynamicParabolicRadicalComparison` takes a reductive group `G`, a cocharacter
`χ`, representatives `iP : P → G` and `iU : U → G` of its dynamic parabolic and
identity-limit subgroup, and a full relative radical certificate for
`n : N → P`. It returns an actual isomorphism `e : N ≅ U` together with the
identity `e.hom ≫ iU = n ≫ iP` in the ambient group.

The construction factors `iU` through `iP` using containment of the dynamic
identity-limit subgroup in the dynamic parabolic on all test schemes. Published
arbitrary-base dynamic representability supplies a centralizer representative.
The assumed dynamic relative Levi theorem then certifies that factor as a
relative radical. `dynamicParabolicRadicalIso` compares it with the supplied
radical, and composing the compatibility identity with `iP` gives the stated
ambient identity. The reductive predicate supplies the affine and smooth
structure morphism hypotheses used by these constructions.

`radical_ambient_range_eq_of_dynamic_parabolic` needs no supplied identity-limit
representative. It obtains one by arbitrary-base dynamic representability and
uses the comparison isomorphism and invariance of the image under a source
isomorphism to prove
`SubgroupFunctor.range (n ≫ iP) = Dynamic.unipotent χ`.
This equality holds on every scheme over the base, including nonreduced test
schemes. `isRepresentedBy_unipotent_of_relativeRadical` adds monicity, obtained by
composing the closed inclusion `n` with the monomorphic representative `iP`.

These are internal consequences of the published representative and dynamic
interfaces together with the relative radical comparison construction. They are
intended for comparison and gluing arguments. No local dynamic presentation of
an arbitrary parabolic, radical existence without a supplied certificate, or
descent assertion is made here.
