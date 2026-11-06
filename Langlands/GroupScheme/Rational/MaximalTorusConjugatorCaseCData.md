# Generic conjugation data for Case C

Author: Worker 1420.

This internal, derived module proves `semisimpleCentralizerConjugationData`. The theorem
derives the proposition `SemisimpleCentralizerConjugationDataStatement` of module
`Rational/MaximalTorusConjugatorCaseC` from three published statements:

- `SemisimpleMaximalTorusLieCentralizerStatement`;
- `CharZeroTorusLieCentralizerStatement`;
- `MaximalTorusBaseChangeStatement`.

All three are published statements (module `Lie/TorusLieCentralizerStatements` and
`Torus/MaximalBaseChangeStatement`). The module takes them as hypotheses `hW`, `hW0` and
`hbc`; module `MaximalTorusParameterUnirationalProof` supplies their published proofs.

The proof follows the generic-element argument of the project's Case C: take the generic Lie
element `X` of `G` over the function field `K` of the affine space of Lie coordinates. Its
centralizer (or the centralizer of a prime power of it, in characteristic `p`) is a proper
smooth subgroup of `G_K`. Over an algebraically closed field `Ω`, a point of `G` with dense
image conjugates `T₀` into that centralizer. No single literature statement is formalized.
Every step combines published Library results, which are named below.

Throughout, `G_E` denotes `(GroupScheme.baseChange (algebraBaseMap k E)).obj G` for a
`k`-algebra `E`, and `kbce E` abbreviates the published identification
`Lie.kernelBaseChangeEquiv k E G E` of the Lie kernel of `G` with coefficients in `E` with the
`E`-rational Lie kernel of `G_E`. Three local instances record that `G_E` is affine, locally
of finite type, or smooth over `E` when `G` is so over `k`, using the pullback of `G.X.hom`.

## The predicate

`HasGenericCentralizerConjugator j₀` (a `Prop`-valued definition, for `j₀ : T₀ ⟶ G` with `G`
affine and locally of finite type over `k`) says that there are:

- a field `K` with a `k`-algebra structure such that `algebraBaseMap k K` reduces rational
  function fields (`ReducesRationalFunctionFields`), and
- a `K`-rational Lie element `Y` of `G_K` such that
  - the centralizer group `Lie.elementCentralizerGroup G_K Y` is smooth over `K`;
  - the Lie centralizer `Lie.elementCentralizerLie G_K Y` is not the whole Lie algebra;
  - `HasCentralizerConjugator G j₀ Y` holds. This is the published predicate of
    `MaximalTorusConjugatorCaseCAssembly`: a point of `G_K` over an algebraically closed
    field, with dense image in `G`, conjugates the base change of `j₀` into the centralizer
    of `Y` over every test scheme.

These are exactly the hypotheses of the published `conjugationData_of_hasCentralizerConjugator`,
which produces the data of `SemisimpleCentralizerConjugationDataStatement`. In that data, `H`
is the identity component of the centralizer group of `Y`.

## The generic field

`reducesRationalFunctionFields_genericField`: the extension of `k` to the function field of
`𝔸^d` (indexed by `ULift (Fin d)`) reduces rational function fields. The published
`algebraBaseMap_rationalFunctionField` identifies this extension with a rational function field
over `k`, and `reducesRationalFunctionFields_rationalFunctionFieldOver` applies.

## A conjugate of the generic Lie element in the torus-centralizer slice

`exists_conjugate_genericLieElement` assumes that `G` is smooth, affine and connected over `k`,
that `c` is a family of finite Lie coordinates of `G` of size `d`, and that `j₀` is a maximal
torus. It produces:

- an algebraically closed field `Ω` over `k`;
- a `k`-algebra map `ψ` from the function field of `𝔸^d` to `Ω`;
- a point `g` of `G` over `Ω` whose underlying map has dense range;
- a Lie element `Z` of `G` over `Ω`.

These satisfy `Ad(g) Z = ψ(genericLieElement c)`, and every tangent vector of the base change
of `T₀` to `Ω` lies in the Lie centralizer of `(kbce Ω).symm Z` in `G_Ω`.

Proof. `G` is irreducible, because it is smooth and connected
(`DynamicConnected.irreducibleSpace_of_smooth`). `T₀` is affine and of finite type, since
`j₀` is a closed subgroup. The published `Lie.exists_torusCentralizerSlice` gives a matrix `B`
over `k` with two properties. Every column of `B` is centralized by the Lie algebra of `T₀`.
The adjoint slice map `(g, t) ↦ Ad(g)(B t)` has dense range. The published
`Lie.exists_adjoint_eq_genericLieElement_of_denseRange` then gives the following data:

- a field `L` and a map `φ` from the function field to `L`;
- a point `g` of `G` over `L` hitting the generic point of `G`;
- a Lie element `Z` over `L` whose coordinates lie in the column space of `B` over `L`;
- the equation `Ad(g) Z = φ(genericLieElement c)`.

Let `Ω` be the algebraic closure of `L` and `e : L → Ω` the inclusion. Take `ψ = e ∘ φ`, the
point `e(g)` and the Lie element `e(Z)`:

- *Coordinates.* The coordinates of `e(Z)` lie in the column space of `B` over `Ω`. This
  follows from naturality of the coordinates `c` and `RingHom.map_mulVec`.
- *Lie containment.* The published
  `Lie.targetMap_mem_elementCentralizerLie_baseChange_of_mulVec` then gives the containment.
- *Conjugation.* The equation `Ad(e(g)) e(Z) = ψ(genericLieElement c)` follows from
  `adjoint_naturality` and `lieKernelMapLinear_comp`.
- *Density.* The generic point of `G` lies in the range of `e(g)`, because `Spec Ω → Spec L`
  hits the unique point of `Spec L`. Its closure is all of `G`, so the range is dense.

## Assembly lemmas

- `elementCentralizerLie_ne_top_of_not_isNilpotent`: for a group `H` over a field `K` with
  finite Lie coordinates `cH`, a `K`-rational Lie element whose adjoint differential is not
  nilpotent does not have the whole Lie algebra as its Lie centralizer. By the published
  `Lie.elementCentralizerLie_eq_top_iff_adjointDifferential_eq_zero`, a full Lie centralizer
  would make the adjoint differential zero.
- `hasGenericCentralizerConjugator_of`: `HasGenericCentralizerConjugator j₀` from a field `K`
  and its four component conditions. The existential's field and algebra instances are left
  for unification (`⟨K, _, _, …⟩`). Supplying them as `inferInstance` made elaboration time
  out.

## The generic conjugation situation

`exists_generic_conjugate` adds to the previous assumptions that `G` is locally of finite type
and has a noncentral geometric semisimple Lie element
(`HasNoncentralGeometricSemisimpleElement G`). It gives:

- a field `K` reducing rational function fields: the function field of `𝔸^d`, by
  `reducesRationalFunctionFields_genericField`;
- a Lie element `X` of `G` over `K` (the generic Lie element) whose adjoint differential in
  `G_K`, in the base-changed coordinates `c.baseChange k K`, is not nilpotent;
- `Ω`, `ψ`, `g` and `Z` as in `exists_conjugate_genericLieElement`, with
  `Ad(g) Z = ψ(X)`.

Non-nilpotence uses `Lie.adjointDifferentialFamily_apply` and the published
`Lie.adjointRepresentation_baseChange_tangentMatrix` to rewrite the adjoint differential in
`G_K` as the adjoint tangent matrix of `X` in `G`. The published
`Lie.not_isNilpotent_tangentMatrix_genericLieElement` (module `Lie/GenericNoncentral`) states
that this matrix is not nilpotent.

## Characteristic `p`

`hasGenericCentralizerConjugator_of_charP hW hbc p c hj₀ hS` (for `k` of characteristic `p`)
proves `HasGenericCentralizerConjugator j₀`. Take `K`, `X`, `Ω`, `ψ`, `g` and `Z` from
`exists_generic_conjugate`. The fields `K` and `Ω` also have characteristic `p`.

1. *Relation.* The published `exists_hasPrimePowerRelation` gives `m` with
   `HasPrimePowerRelation X p m`. This is a linear relation over `K` among the field prime
   powers of `X` (module `Lie/PrimePowerFieldExtension`) with nonzero coefficient at exponent
   `m`.
2. *Transfer to `Z`.* The relation transfers along `ψ` (`HasPrimePowerRelation.map`) and along
   conjugation by `g⁻¹` (`HasPrimePowerRelation.conjugation`). Since `Ad(g⁻¹) Ad(g) Z = Z`,
   this gives `HasPrimePowerRelation Z p m` over `Ω`.
3. *Conjugation of prime powers.* Put `Y' = fieldPrimePower k K G X p m` and
   `Z' = fieldPrimePower k Ω G Z p m`. Field prime powers commute with constant-point
   conjugation and with coefficient change (`lieKernelConjugation_fieldPrimePower`,
   `lieKernelMap_fieldPrimePower`), so `Ad(g) Z' = ψ(Y')`.
4. *Lie containment for `Z'`.* `(kbce Ω).symm Z'` is the prime power
   `Lie.primePowerKernel` of `(kbce Ω).symm Z` in `G_Ω`, by definition of `fieldPrimePower`.
   Taking prime powers can only enlarge Lie centralizers
   (`Lie.elementCentralizerLie_le_primePowerKernel`). So the tangent vectors of `T₀` over
   `Ω` lie in the Lie centralizer of `(kbce Ω).symm Z'`.
5. *Torus centralizes `Z'`.* `G_Ω` is connected (`GroupScheme.connectedSpace_baseChange_of_smooth_affine`).
   The base change of `j₀` to `Ω` is a maximal torus (`hbc`). `(kbce Ω).symm Z'` is
   semisimple (`HasPrimePowerRelation.isSemisimpleElement`). Then `hW` applied to `G_Ω`
   shows that the base change of `T₀` centralizes `(kbce Ω).symm Z'` over every test scheme.
6. *Conjugator.* The published `rangeFixesLieElement_of_range_le` and
   `hasCentralizerConjugator_of_adjoint_eq` (module `MaximalTorusConjugatorCaseCConjugator`)
   then give `HasCentralizerConjugator G j₀ ((kbce K).symm Y')`.
7. *The other two conditions for `(kbce K).symm Y'`.*
   - Its centralizer group is smooth. It is semisimple by
     `HasPrimePowerRelation.isSemisimpleElement`, and `Lie.smooth_elementCentralizerGroup`
     applies.
   - Its Lie centralizer is not everything. It equals `Lie.primePowerKernel` of
     `(kbce K).symm X`, and the published `Lie.elementCentralizerLie_primePowerKernel_ne_top`
     applies because the adjoint differential of `X` is not nilpotent.

`hasGenericCentralizerConjugator_of` assembles the result.

## Characteristic zero

`hasGenericCentralizerConjugator_of_charZero hW0 c hj₀ hS` (for `k` of characteristic zero)
proves `HasGenericCentralizerConjugator j₀` with `Y = (kbce K).symm X` itself:

1. *Torus centralizes `Z`.* The base change of `T₀` to `Ω` is a torus
   (`IsTorus.baseChange`). By `hW0` applied to `G_Ω`, with the Lie containment of
   `exists_generic_conjugate`, it centralizes `(kbce Ω).symm Z` over every test scheme.
2. *Conjugator.* `rangeFixesLieElement_of_range_le` and
   `hasCentralizerConjugator_of_adjoint_eq` give `HasCentralizerConjugator G j₀ Y`.
3. *Smoothness.* The centralizer group of `Y` is a closed subgroup of `G_K`
   (`Lie.isClosedSubgroup_elementCentralizerGroupι`). It is therefore affine and locally of
   finite type over the characteristic-zero field `K`, hence smooth by Cartier's theorem
   (`affineCartierSmooth`).
4. *Noncentrality.* The adjoint differential of `Y` is not nilpotent, so
   `elementCentralizerLie_ne_top_of_not_isNilpotent` shows that its Lie centralizer is not
   everything.

## Generic conjugation data

`semisimpleCentralizerConjugationData hW hW0 hbc : SemisimpleCentralizerConjugationDataStatement`.
Given `k`, `G`, `T₀`, `j₀`, maximality of `j₀` and a noncentral geometric semisimple Lie
element, take the coordinates `Lie.finiteCoordinates G`. Then split on the characteristic of
`k` (`CharP.exists`, `CharP.char_is_prime_or_zero`). The two producers above give
`HasGenericCentralizerConjugator j₀`. Unpacking it, the published
`conjugationData_of_hasCentralizerConjugator` gives the required field `K`, subgroup `H`,
algebraically closed field `Ω` and conjugating point.
