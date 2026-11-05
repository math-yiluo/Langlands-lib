# Lifting generic torus conjugators along homomorphisms

Author: Worker 1420.

This internal, derived module transports the predicate
`HasGenericTorusConjugator` of `MaximalTorusGenericConjugator` from a target
group to a source group along a homomorphism. It also records the central
torus case. The field `k : Type u` is arbitrary; there is no infinitude,
perfection or characteristic assumption.

`ReflectsTorusNormalizer φ j₀ j₀'` is defined for a homomorphism `φ : G → G'`
of group schemes over `Spec k` and torus homomorphisms `j₀ : T₀ → G`,
`j₀' : T₀' → G'`. It says the following. For every scheme `U` over `k` and every point
`x : U → G.X`, if `x ≫ φ` lies in the all-test torus normalizer of `j₀'` over
`U`, then `x` lies in the all-test torus normalizer of `j₀` over `U`. No
relation between `j₀` and `j₀'` is built into the definition. A typical
source is a central isogeny whose kernel lies in `T₀`, but this module
proves no such instance.

`HasGenericTorusConjugator.of_hom` assumes that the underlying scheme
morphism of `φ` is flat, surjective, quasi-compact and universally open, and
that `φ` reflects torus normalizers from `j₀'` to `j₀`. From a generic
conjugator `(n, X', π', g')` for `j₀'` it builds one for `j₀`, with the
same finite `n`. The new source is the fiber product `X = X' ×_{G'} G` of `g'`
and `φ`, viewed over `Spec k` through `X'`. The new morphism to the rational
function field is the first projection followed by `π'`, and the new point
`g` is the second projection.

- The first projection is a base change of `φ`, so it is flat and quasi-compact
  (Mathlib instances). It is surjective because its range is the preimage of
  the range of `φ` (`Scheme.Pullback.range_fst`). Composing with `π'` keeps all
  three properties.
- `g` has dense range: its range is the preimage of the range of `g'` under
  `φ` (`Scheme.Pullback.range_snd`), and the preimage of a dense set under an
  open map is dense.
- Descent: if two test points `a₁, a₂` of `X` agree after the new map to the
  function field, their images in `X'` agree after `π'`. The descent condition
  for `g'` puts `((a₁ ≫ pr) ≫ g')⁻¹ * ((a₂ ≫ pr) ≫ g')` in the normalizer of
  `j₀'`. This point equals `((a₁ ≫ g)⁻¹ * (a₂ ≫ g)) ≫ φ`, because `φ` is a
  monoid homomorphism on points (`IsMonHom.monoidHom`) and `g ≫ φ = pr ≫ g'`
  is the pullback square. Reflection gives the normalizer condition for
  `j₀`.

`hasGenericTorusConjugator_of_centralizer_eq_top` assumes that every point of
`G`, over every test scheme, lies in the all-test centralizer
`torusCentralizer j`, and that `G.X.hom` is flat and quasi-compact. The
published inclusion `torusCentralizer_le_torusNormalizer` then puts every point
in the normalizer, and `hasGenericTorusConjugator_of_normalizer_eq_top` applies.

Provenance: derived from the helper module `MaximalTorusGenericConjugator`, the
published `torusNormalizer`, `torusCentralizer` and
`torusCentralizer_le_torusNormalizer`, and pinned Mathlib fiber products of
schemes, base change of flat and quasi-compact morphisms, and universally open
morphisms. It supplies the central-isogeny transport and the central-torus base
case of the induction planned for the generic conjugator statement. That
induction follows the dimension induction in SGA 3, Exposé XIV, Théorème 6.1.
There, dividing by a central subgroup does not change the scheme of maximal
tori. No literature statement is formalized, and this module does not prove
`MaximalTorusGenericConjugatorStatement`.
