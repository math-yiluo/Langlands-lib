# The rank-one start of Proposition 4.8 with complex-place parameters

Module `Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerAuxiliaryRankOneProof`,
namespace `Langlands.Global.Harris`.

The theorem `Langlands.Global.Harris.proposition48ExactStabilizerAuxiliaryRankOne.{uF, uV}`
proves the published statement
`Langlands.Global.Harris.Proposition48ExactStabilizerAuxiliaryRankOneStatement.{uF, uV}` from
module `HarrisProposition48ExactStabilizerParameterAuxiliaryStatement`. The universes `uF` and
`uV` are arbitrary and independent, and no hypothesis is added. The proof uses only `propext`,
`Classical.choice` and `Quot.sound`.

## The statement

For every `Q : Proposition48Problem` with `Q.IsAuxiliaryValid` and `[E' : E] = 1`, the problem
has a parameter solution (`Q.HasParameterSolution`). This means a cuspidal class `c` of some
`GL_(r+1)` over `E` such that:

- `c` is a weak automorphic induction of `ξ = Q.ξ`;
- `c` is regular algebraic;
- `c` is conjugate self-dual;
- `c` has a supercuspidal component at the auxiliary place `Q.Ps.v`;
- at every complex place `v` of `E`, `c` has the parameter induced from `ξ`.

## The proof

Only two conjuncts of `IsAuxiliaryValid` are used.

- `IsAlgebraicAfterTwist ([E' : E] - 1) ξ` becomes `IsAlgebraicAfterTwist 0 ξ` once
  `[E' : E] = 1`. It gives an infinity type `t` with `ξ.atInfinity = InfinityType.toCharacter t`.
- `IsConjugateInverse ξ`.

Let `χ = restriction ξ = ξ ∘ ι`, where `ι : C_E → C_{E'}` is the idele-class inclusion. Take
`r = 0` and `c = (cuspidal χ).isoClass`, the automorphic `GL(1)` realization of `χ`. All helper
lemmas are in namespace `Langlands.Automorphic.RankOneHecke`.

1. **Parameters of `ξ`.** At a place `w` of `E'` above a complex place `v`, the character `ξ`
   has the parameter `dξ w = exponentData (t σ) (t σ̄)`, where `σ = w.embedding`
   (`hasComplexPlaceParameter_of_atInfinity`). Every place of `E'` is complex because `E'` is
   CM.
2. **Exactly one place lies above `v`** (`card_infinitePlacesAbove`). By
   `restriction_hasComplexPlaceParameter`, `χ` has at `v` the parameter
   `normParameter v w (dξ w)`. This is either `exponentData (t σ) (t σ̄)` or, by
   `exponentData_conj`, `exponentData (t σ̄) (t σ)`. Choosing these exponents `a v` and `b v`
   gives `∀ v, χ.HasComplexPlaceParameter v (exponentData (a v) (b v))`.
3. **Weak induction**: `cuspidal_restriction_isWeakAutomorphicInductionOf`.
4. **Regular algebraic**: `cuspidal_isRegularAlgebraic_of_exponentData a b`. The field `E` is
   totally complex because it is CM.
5. **Conjugate self-dual**: `cuspidal_isConjugateSelfDual`. Here `χ` is conjugate inverse by
   `restriction_ideleClassComplexConj`.
6. **Supercuspidal component** at `Q.Ps.v`: `cuspidal_hasSupercuspidalComponent`. Every local
   component of the `GL(1)` realization is supercuspidal.
7. **Induced parameters.** Fix a complex place `v` and the enumeration
   `e : Fin 1 ≃ InfinitePlacesAbove E' v` from the cardinality. Take
   `ds = [normParameter v (e 0) (dξ (e 0))]`. The class `c` has the parameter `ds` at `v` by
   `cuspidal_hasComplexPlaceParameter`. With `d = 1`, the enumeration `e` and the parameters
   `dξ` of step 1, `complexPlaceLanglandsSum_fin_one` shows that the Langlands sum
   `complexPlaceLanglandsSum v e (fun w => [dξ w])` equals `ds`. A list is a permutation of
   itself.

## Helper modules

- `Langlands.Automorphic.RankOneHeckeRealization`: the realization `cuspidal χ`, its parameter
  `[d]`, its Euler polynomials and its supercuspidal components.
- `Langlands.Automorphic.RankOneHeckeRegularAlgebraic`: regular algebraicity from integral
  exponents at the complex places.
- `Langlands.Automorphic.RankOneHeckeConjugateSelfDual`: conjugate self-duality for a
  conjugate-inverse character.
- `Langlands.Automorphic.RankOneHeckeRestriction`: degree-one comparisons for `ξ ∘ ι`, the
  weak induction, parameters, conjugation, and the parameters of algebraic characters.

These modules also use helper modules of the parameter untwist
(`HarrisProposition48ExactStabilizerParameterUntwistProof`): `Langlands.Automorphic.ComplexPlaceParameterHeckeTwist`,
`Langlands.Automorphic.Unramified.ComplexPlaceParameterNorm` and
`Langlands.Representation.Archimedean.ComplexStandardDeterminantTwist`.

## Relation to the source

The target is an internal interface for the exact-stabilizer form of the induction for Harris
(1998), Proposition 4.8 (see the paired Markdown of the statement module). It is not a statement
of Harris. The proof follows the argument sketched there under "Why it should hold": in degree
one, `ξ` is a Hecke character of `E` through the idele-class inclusion, and its `GL(1)`
realization has the four properties. Its parameter at a complex place `v` is the one-block list
of the parameter of `ξ` at the unique place above `v`, read in the coordinates of `v`.
