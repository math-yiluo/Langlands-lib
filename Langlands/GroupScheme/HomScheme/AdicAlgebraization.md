# Algebraizations of compatible adic Hom systems on test schemes

This internal module supports the finite étale descent step of the adic Hom
comparison. It states what it means for an actual relative homomorphism over a
test scheme to induce a given compatible adic Hom system.

## Setting

Let `A` be a commutative ring with ideal `I`. Let `H` and `G` be group schemes
over `Spec A`. The published structure `HomScheme.Adic.System I H G` is a
compatible family of homomorphisms, one for each `n`. Its member `s.hom n` is a
relative homomorphism over the thickening `quotientMap I n : Spec A/I^(n+1) → Spec A`.
For a test scheme `V` over `Spec A`, a `RelativeHom H G V` is a homomorphism
`H_V → G_V` of the base-changed groups. For a test-scheme map `t : T → V`,
`evaluate t` restricts such a homomorphism to `T`.

## Definition

`System.IsAlgebraization s a` takes a compatible system `s` and a relative
homomorphism `a` over `V`. It says the following. Take any `n`, any test scheme
`T` over `Spec A`, and any map `t : T → V` over `Spec A`. Suppose the structure
map of `T` factors as `u` followed by the thickening map
`Spec A/I^(n+1) → Spec A`. Then evaluating `a` along `t` gives the same result
as evaluating `s.hom n` along the induced test-scheme map
`Over.homMk u hu : T → Spec A/I^(n+1)`.

In words, `a` is a family of homomorphisms parametrized by `V`. It induces the
system `s` on every test scheme over `V` that is killed by some power `I^(n+1)`.
The quantifier runs over all such test schemes and all factorizations `u`.
`u` is unique when it exists, because `quotientMap I n` is a closed immersion.
Including it in the data avoids choosing it. This remark is only motivation; the
module neither states nor uses it.

## Lemmas

* `System.isAlgebraization_evaluate`: if `a` algebraizes `s` over `V` and
  `w : W → V` is a test-scheme map, then `evaluate w a` algebraizes `s` over
  `W`. This follows from `evaluate_comp`: evaluating `evaluate w a` along `t`
  is evaluating `a` along `t ≫ w`.
* `System.isAlgebraization_restrict`: let `f : H ⟶ G` be a homomorphism over
  `Spec A`. On every test scheme `V`, its constant family `(baseChange V.hom).map f`
  algebraizes the restriction system `restrict I H G f`. Both sides reduce
  to the constant family `(baseChange T.hom).map f`. The rewrite uses the
  published `evaluate_baseChange` and `restrict_hom`.

## Provenance

The provenance is internal. The predicate restates the condition that a
homomorphism over a test scheme induces the given formal (adic) system. The
finite étale descent step of SGA 3, Exposé IX, Théorème 7.1 compares such
homomorphisms over a finite cover and over its double overlap. Here it is
expressed with the Library's `HomScheme.Adic.System`, `evaluate`, and
`AdicAffinePoints.quotientMap`. No completeness, noetherianity, or
diagonalizability hypothesis is used in this module.

The module imports `Langlands.GroupScheme.HomScheme.AdicSystemBaseChange`
(pullback of adic systems along ring maps) so that downstream modules can use
both interfaces together. The declarations here use only the published
`AdicSystem` and `ConjugationMap` API.
