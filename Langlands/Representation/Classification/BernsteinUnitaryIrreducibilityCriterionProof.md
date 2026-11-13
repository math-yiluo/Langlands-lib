# Proof of the unitary finite-length highest-derivative irreducibility criterion

Author: Worker 5193.

This module proves the target with no added hypothesis. The final theorem is
`Langlands.Classification.bernsteinUnitaryFiniteLengthIrreducibilityCriterion`.

## Target

The target is
`Langlands.Classification.BernsteinUnitaryFiniteLengthIrreducibilityCriterion.{uF, uV} F T`
from `BernsteinUnitaryIrreducibilityCriterionStatement`, for
`{p : ℕ} [Fact p.Prime]`, `F : PadicField.{uF} p` and `T : F.TopologicalData`.
After `letI := T.topology` it says the following. Let `N > 0`, let `ψ` be a
unitary additive character, and let `A` be a finite-length unitarizable smooth
representation of `GL_N(F)` with carrier in `Type (max uF uV)`. Let `hd` be a
highest positive derivative order of `A`, with order `h`. Assume that the
shifted derivatives `ν^(1/2) A^(k)` with `k < h` (including `k = 0`) have only
positive Bernstein exponents. Assume that `ν^(1/2) A^(h)` is irreducible and
unitarizable. Then `A` is irreducible.

## Declarations

- `isUnitarizable_of_isSubquotient_of_semisimple`: let `A` be a semisimple
  unitarizable smooth representation of any topological group. Then every
  actual subquotient `D` of `A` is unitarizable. Write `D` as a quotient of a
  subrepresentation `C` of `A`. The module `C` is semisimple, so
  `IsSemisimpleModule.lifting_property` splits the quotient map `C → D`. The
  splitting composed with the inclusion embeds `D` into `A`. The invariant
  inner product of `A` pulls back along this embedding
  (`IsUnitarizable.of_injective`).
- `generalLinear_compactOpen_cofinal`: every open subgroup of `GL_n(F)`
  contains a compact open subgroup. This is `T.generalLinearCompactOpen`.
- `isSemisimple_of_hasFiniteLength_of_isUnitarizable`: a finite-length
  unitarizable smooth representation `B` of `GL_n(F)` is semisimple. Finite
  length gives admissibility (`glFiniteLengthAdmissibility`). An admissible
  unitarizable representation is semisimple (`admissibleUnitarySemisimplicity`,
  with the cofinality lemma above).
- `hasBernsteinCentralExponent_zero_of_isUnitarizable`: an irreducible
  unitarizable smooth representation `E` of `GL_n(F)` has Bernstein central
  exponent `0`. `E` is admissible, so `unitarizableCentralCharacter` gives it a
  unitary central character `c`. The scalar matrix `a` then acts by
  `c (scalarToCenter a)`, which has norm `1 = |a|^0`.
- `bernsteinUnitaryFiniteLengthIrreducibilityCriterion_of_unitarizability`:
  the criterion, under the hypothesis
  `hH : BernsteinShiftedHighestDerivativeUnitarizability.{uF, uV} F T`. For
  every `N > 0`, every `ψ`, every irreducible unitarizable `π` of `GL_N(F)`
  with carrier in `Type (max uF uV)` and every highest-order datum `hd` of
  `π`, `hH` says that `shiftedHighestDerivative F T ψ hd` is unitarizable.
- `bernsteinUnitaryFiniteLengthIrreducibilityCriterion`: the target
  `BernsteinUnitaryFiniteLengthIrreducibilityCriterion.{uF, uV} F T`. It applies
  the previous theorem to the Library theorem
  `bernsteinShiftedHighestDerivativeUnitarizability.{uF, uV} F T`, which proves
  `hH` with no hypothesis.

## Proof of the criterion from `hH`

Let `J` be the actual derivative functor
`Derivative.generalLinearDerivative T ψ N h`. It maps short exact sequences to
short exact sequences (`generalLinearDerivativeExactness`). By the twist
lemma `SmoothRep.isIrreducible_twist_iff`, `J A` is irreducible, because its
twist by `ν^(1/2)` is irreducible by hypothesis.

The proof applies `ExactFunctorIrreducibility.isIrreducible_of_obj` to `J`
and the finite-length representation `A`. That lemma concludes that `A` is
irreducible once `J D` is nonzero for every irreducible actual subquotient `D`
of `A`. Fix such a `D`.

1. `A` is semisimple (`isSemisimple_of_hasFiniteLength_of_isUnitarizable`),
   so `D` is unitarizable (`isUnitarizable_of_isSubquotient_of_semisimple`).
2. `D` is nonzero, so `chooseGeneralLinearHighestDerivativeOrder` gives a
   highest positive order `d` of `D`.
3. For every order `k`, the derivative `D^(k)` is an actual subquotient of
   `A^(k)`, because exact functors preserve subquotients
   (`ExactSmoothTransport.map_isSubquotient`).
4. Case `d < h`. By `hH`, `S = ν^(1/2) D^(d)` is unitarizable. `S` has finite
   length (`generalLinearDerivativeFiniteLength` and `finiteLength_twist_iff`)
   and is nonzero. So `S` has an irreducible actual subquotient `E`
   (`SmoothRep.exists_irreducible_subquotient`). `S` is semisimple by the
   lemma above, so `E` is unitarizable and has exponent `0`. Twisting step 3
   by `ν^(1/2)` (`SmoothRep.IsSubquotient.twist`) and using transitivity
   (`smoothSubquotientTransitivity`) makes `E` an irreducible subquotient of
   `ν^(1/2) A^(d)`. The positivity hypothesis at `d < h` then says that this
   exponent is positive. That is a contradiction.
5. Case `d = h`. Then `J D = D^(h)` is nonzero by the choice of `d`.
6. Case `d > h`. The datum `hd` says that `A^(d)` is zero. By step 3, `D^(d)`
   is a quotient of a subrepresentation of `A^(d)`, so it is zero as well.
   This contradicts the choice of `d`.

So `J D` is nonzero in every possible case, and `A` is irreducible.

The proof follows the constituent route mentioned in the statement's
Markdown. It does not use the Hermitian-dual argument of Bernstein's
Proposition 8.1(a).

## Source of the unitarity input

The hypothesis `hH` is the unitarity half of Bernstein's theorem on the
shifted highest derivative (J. N. Bernstein, LNM 1041 (1984), §7.4 and §8,
registered as `bernstein-1984-p-invariant`). The Library states it as
`Langlands.Classification.BernsteinShiftedHighestDerivativeUnitarizability`
and proves it as `bernsteinShiftedHighestDerivativeUnitarizability`
(module `BernsteinShiftedHighestDerivativeUnitarizabilityProof`, which uses
the Library proof of `Derivative.MirabolicPhiMinusUnitarity`). This module
imports that proof and uses it only through the final theorem.
