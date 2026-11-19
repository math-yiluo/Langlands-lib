# Proof: finite components almost everywhere determine a Hecke character

`Langlands.Automorphic.Unramified.heckeLocalComponentRigidity` proves the
published proposition
`Langlands.Automorphic.Unramified.HeckeLocalComponentRigidityStatement.{u}`.
The universe `u` is arbitrary. Of the hypothesis at each finite place
`v ∉ S`, the proof uses only the equality of finite components; the two
unramifiedness conjuncts are not used.

Scope: only this conjunct of
`HeckeCharacterRigidityStatement` is proved. Finite ramification, power-trace
independence and Euler-product rigidity are neither proved nor used here.

## Route

Fix a number field `K`, Hecke characters `χ` and `η`, and a finite set `S`
of finite places, such that `χ.finiteComponent v = η.finiteComponent v`
for every finite `v ∉ S`.

1. **Ratio.** `HeckeRigidity.ratio χ η` is the continuous character
   `x ↦ χ(x) / η(x)` of the full idele group. If it is identically one, then
   `χ = η`, because the idele-class map is surjective
   (`eq_of_ratio_eq_one`).
2. **Local triviality outside `S`.** Equality of finite components says
   exactly that the ratio is trivial on the published local inclusion
   `finiteIdeleInclusion K v` for every `v ∉ S`
   (`ratio_finiteIdeleInclusion`).
3. **Integral units outside `S`.** Pull the ratio back along the published
   `integralUnitIdeles K` from the product of all local integral unit groups.
   The preimage of the ball of radius `1/2` about one contains a product
   neighbourhood constraining a finite set `T` of coordinates. An element
   equal to one on `T` has all powers in that neighbourhood, so its value is
   one, by the published `complex_eq_one_of_forall_norm_pow_sub_one_lt`.
   An integral unit family equal to one on `S` is a product of such an
   element and finitely many single-coordinate elements at places of `T`
   outside `S`. These are trivial by step 2 and
   `integralUnitIdeles_mulSingle` (`ratio_integralUnitIdeles`).
4. **Decomposition.** Let `x` be an idele. Its finite coordinates are local
   integral units outside a finite set `R`, which contains `S`. The proof
   takes `R` to be the union of the exceptional set of the restricted
   product with `S`. Coordinatewise, `x` is the product of three factors:
   - its archimedean part, inserted with `infiniteIdelesInclusion`;
   - the finite product over `R` of the local insertions of its coordinates;
   - the integral-unit idele formed from its remaining coordinates.

   Equality is checked through the infinite part and every finite
   coordinate (`idele_ext`, `ratio_eq_local`). By steps 2 and 3,
   `ratio(x)` is the ratio at the archimedean part times the product over
   `v ∈ S` of the ratio at the local inclusion of `x_v`.
5. **Weak approximation.** `localRatio` is the resulting continuous
   character on
   `(∏_w (K_w)ˣ) × (∏_{v ∈ S} (K_v)ˣ)`, archimedean `w` and `v ∈ S`.
   - Hecke characters are trivial on `diagonalUnits K a`
     (`HeckeCharacter.onIdeles_diagonalUnits`). Applied to that idele, step 4
     shows that `localRatio` equals one at the diagonal image of every
     `a ∈ Kˣ` (`localRatio_localDiagonal`).
   - The diagonal image is dense. The published
     `denseRange_numberFieldFiniteCompletionDiagonal` makes `K` dense in the
     product of these completions. Mathlib's `Units.isEmbedding_val₀`
     identifies each unit group with the open set of nonzero elements. A
     point with all coordinates nonzero is therefore a limit of diagonal
     units (`denseRange_localDiagonal`).
   - By continuity `localRatio` is identically one, so the ratio is one at
     every idele.

## Dependencies

The proof imports, by Lean name, the target statement module, the published
`Langlands.Global.Factors.HeckeFiniteRamification` and
`Langlands.Global.GlobalCompletionWeakApproximation`. Lean reports only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

The argument is the standard strong-multiplicity-one argument for
characters: a character of the idele class group is determined by its
components at almost all places, by weak approximation. It is internal
Lean work by Worker 116 of the previous FormalGeyser instance, adopted
unchanged from the shared draft of task 34b81620-20d7-4059-9b08-6bedd1c1c029,
and follows the route described in the proof task contract. No literature
statement is formalized beyond the published target.
