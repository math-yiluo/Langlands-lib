# Untwisting complex-place parameters in Proposition 4.8

Module `Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerParameterUntwistProof`,
namespace `Langlands.Global.Harris`.

The theorem `Langlands.Global.Harris.proposition48ExactStabilizerParameterUntwist.{uF, uV}`
proves the published statement
`Langlands.Global.Harris.Proposition48ExactStabilizerParameterUntwistStatement.{uF, uV}`
(module `HarrisProposition48ExactStabilizerParameterAuxiliaryStatement`) at arbitrary
independent universes `uF`, `uV`, with no added hypothesis. It uses only `propext`,
`Classical.choice` and `Quot.sound`.

## The statement

For a problem `Q`, a parity `b`, `ν : HeckeCharacter Q.E`, `χs`, and actual cuspidal
realizations `S T` of `GL_(r+1)` over `E` with `Q.IsUntwistedSolution ν S T`: if `T` has, at
every complex place `v` of `E`, a parameter that is the parameter induced from the corrected
character `ξ' = Q.correctedCharacter ν = ξ · (ν ∘ N_{E'/E})`, then `S` has at every complex
place a parameter induced from `ξ`. The validity and normalization hypotheses
(`IsAuxiliaryValidAtParity`, `IsAuxiliaryParityNormalization`) are not used by the proof.

## The proof

Fix a complex place `v` of `E`. The hypothesis gives a list `ds` with
`T.isoClass.HasComplexPlaceParameter v ds`, an enumeration `en : Fin d ≃` (places of `E'`
above `v`), parameters `dξ w` of `ξ'` at the places `w` above `v`, and
`ds ~ complexPlaceLanglandsSum v en (fun w => [dξ w])`. The first step restates the
hypothesis with `change` in terms of `Q` itself rather than `Q.withCharacters ...` (the two
problems have the same fields and instances, definitionally).

1. `exists_hasComplexPlaceParameter` gives a parameter `e` of `ν⁻¹` at `v`.
2. The last conjunct of `IsUntwistedSolution` is
   `OperatorRealization.IsDeterminantMultiple ν S.realization T.realization`.
   `IsDeterminantMultiple.hasComplexPlaceParameter`
   (module `Langlands.Automorphic.ComplexPlaceParameterHeckeTwist`) shows that `S` has the
   parameter `ds.map (·.mul e)` at `v`: `S` is `T` twisted by `ν⁻¹`, and the twist rule
   multiplies every block by the parameter of `ν⁻¹`.
3. The new data for `ξ` use the same `d` and `en`, with parameters
   `(dξ w).mul (normParameter v w e)` at `w`. By `hasComplexPlaceParameter_comp_ideleClassNorm`
   (module `Langlands.Automorphic.Unramified.ComplexPlaceParameterNorm`), `ν⁻¹ ∘ N` has the
   parameter `normParameter v w e` at `w`; `HasComplexPlaceParameter.mul` gives the product
   parameter for `ξ' · (ν⁻¹ ∘ N)`, which is `ξ` by
   `Proposition48Problem.correctedCharacter_mul_inv_comp`.
4. The permutation: `ds.map (·.mul e)` is a permutation of
   `(complexPlaceLanglandsSum v en (fun w => [dξ w])).map (·.mul e)` (`List.Perm.map`), and
   `complexPlaceLanglandsSum_map_mul` rewrites the latter as
   `complexPlaceLanglandsSum v en (fun w => [(dξ w).mul (normParameter v w e)])`. In the
   conjugate case this uses `conj (a · ē) = ā · e`.

## Helper modules

- `Langlands.Representation.Archimedean.ComplexStandardDeterminantTwist`: multiplication by
  `η ∘ det` on the `U(n)`-finite principal-series functions of `GL_n(ℂ)` and its interaction
  with right translations and right derivatives.
- `Langlands.Automorphic.ComplexPlaceParameterHeckeTwist`: the twist rule for complex-place
  parameters under an arbitrary Hecke character, parameters of products, existence of
  parameters of Hecke characters, and untwisting along `IsDeterminantMultiple`.
- `Langlands.Automorphic.Unramified.ComplexPlaceParameterNorm`: the local norm at a complex
  place in the selected coordinates, the parameter of `μ ∘ N`, and the list identity.

## Relation to the source

The target is an internal interface for the exact-stabilizer form
of the induction for Harris (1998), Proposition 4.8 (see the paired Markdown of the statement
module); it is not a statement of Harris. The proof follows the argument sketched there under
"Why it should hold": the parameter of `S` is that of `T` twisted back by `ν⁻¹` at `v`, and the
parameter of `ξ' = ξ · (ν ∘ N)` at `w` is that of `ξ` times that of `ν ∘ N`, read in the
coordinates of `w`.
