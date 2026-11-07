# Principal irreducibility neighborhoods from a global coefficient basis

Worker 452. This module specializes the principal-open assembly in
`CompactCompressionPrincipalOpen` to the case with no localization. Worker
1444's planned actual universal induced family is meant to use this case.
It is an internal step
of the proof of Renard, *Représentations des groupes réductifs p-adiques*
(9 July 2026), VI.8.4 Proposition, printed pp. 192–193, PDF pp. 198–199.
The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

`isLocalization_away_one` records that a commutative ring `B` is its own
localization away from `1`. The proof applies Mathlib's
`IsLocalization.away_of_isUnit_of_bijective` to the identity map and the
unit `1`. `awayEvaluation_one` says that, for this trivial localization,
`awayEvaluation 1 χ hχ` is the complex character `χ` of `B` itself. The proof
checks this on every element using `awayEvaluation_algebraMap`; here the
algebra map is the identity.

`exists_polynomial_principal_neighborhood_of_global` takes the following
inputs over the actual unramified characters of a connected reductive group
scheme `M` over a nonarchimedean local field. The rational points `M(F)` carry
their canonical topology.

- A complex algebra `B` with an equivalence `e` to the actual regular
  functions on those characters.
- A smooth representation `A` of a topological group `G` with compatible
  `B`-coefficients, a compact open subgroup `K` of `G`, and a finite
  `B`-basis `b` of the actual `K`-fixed vectors of `A`.
- A family `D` of smooth representations of `G` indexed by the unramified
  characters.
- Full specialization of `A` to `D χ` at the character
  `coefficientCharacter M e χ` of `B`, for every unramified character `χ`.
- Detection of every irreducible actual subquotient of every `D χ` by a
  nonzero `K`-fixed vector.

If the fiber at `χ₀` is irreducible, the theorem produces a polynomial in the
published canonical coordinates. Its principal open set
`rationalUnramifiedPrincipalOpen M hM p` contains `χ₀`, and `D χ` is
irreducible for every `χ` in it. Unlike
`exists_polynomial_principal_neighborhood`, it needs no localization element
`g` and no premise that `g` is nonzero at `χ₀`.

The proof treats `B` as its own localization away from `1`. It applies
`exists_polynomial_principal_neighborhood` with `S = B` and `g = 1`. Then
`g` is nonzero at `χ₀` by simplification. The specialization at
`awayEvaluation 1 (coefficientCharacter M e χ) hχ` is rewritten by
`awayEvaluation_one` to the supplied specialization at
`coefficientCharacter M e χ`.

`IsGlobalCoefficientFamily A M e D` is a proposition about a representation
`A` with compatible `B`-coefficients, the equivalence `e` and the family `D`.
It holds when two conditions are met. First, for every compact open subgroup
`K` of `G`, the actual `K`-fixed vectors of `A` form a free and finitely
generated `B`-module. Second, for every unramified character `χ`, `A`
specializes fully to `D χ` at `coefficientCharacter M e χ`, in the sense of
`IsFullSpecialization`. In Renard's argument, `B` is the regular-function
algebra of the unramified characters and `D χ` is the induction of the twist
by `χ`. There the fixed vectors of the universal induced family are used
through a local basis, while this predicate asks for a global one. This
module does not prove the predicate for any actual family.

`exists_polynomial_principal_neighborhood_of_family` has the same conclusion
as `exists_polynomial_principal_neighborhood_of_global`. In place of a chosen
basis and the specialization hypothesis, it takes `IsGlobalCoefficientFamily
A M e D` and a compact open subgroup `K` that detects every irreducible
subquotient of every fiber. The proof gets freeness and finiteness of the
`K`-fixed vectors from the first condition. It takes the basis
`Module.Free.chooseBasis`, which is indexed by a finite type with decidable
equality. Then it applies `exists_polynomial_principal_neighborhood_of_global`
with the second condition.

All universes are independent. The basis or global family, the full
specialization, coefficient compatibility and uniform detection requirements
remain explicit inputs. This module does not construct the universal induced
family and does not prove the closed `InducedIrreducibilityOpenStatement`.
