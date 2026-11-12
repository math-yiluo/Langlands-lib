# Weak induction association from local class field theory inputs

Author: Worker 5130. This is an internal supporting unit of the proof task
`f096b984-dff5-4425-861f-8f298e5896fb`. That task's exact target is
`Langlands.ClassField.Global.RelativeWeilGroup.WeakInductionAssociationStatement`.
The module defines the proposition
`Langlands.ClassField.Global.RelativeWeilGroup.WeakInductionAssociationReductionStatement`
and proves it as `weakInductionAssociation_reduction`. It keeps three published,
still unproved propositions as antecedents. It does not prove the unconditional
target, and publishing it does not complete the host task.

## The reduction statement

`WeakInductionAssociationReductionStatement.{u, uV, uP}` is the implication

```
LocalClassField.WeilReciprocityExistenceUniqueness.{u} →
  LocalRelativeWeilMapExistenceStatement.{u} →
    LocalInducedRestrictionStatement.{uV, u} →
      WeakInductionAssociationStatement.{u, uV, uP}
```

The antecedents and the conclusion are the published propositions, with
unchanged quantifiers and universes:

- `Langlands.LocalClassField.WeilReciprocityExistenceUniqueness.{u}`
  (`Langlands/ClassFieldTheory/Local/WeilReciprocityStatement.lean`): for every
  p-adic field and every topological datum there is a unique geometrically
  normalized Weil reciprocity candidate. Proof task Task 4920
  (`b5f5d445-0427-4757-8ab0-b62da08c1a5f`).
- `Langlands.ClassField.Global.LocalRelativeWeilMapExistenceStatement.{u}`
  (`Langlands/ClassField/Global/LocalRelativeWeilMapStatement.lean`): for class
  families that are fundamental classes of class formations with the arithmetic
  normalization, every geometric candidate of `E_w` has a local map
  `ι : W_{F_v} → W_{E/F}` with `IsLocalRelativeWeilMap v w e ι`. Proof task
  Task 5073 (`241e7251-de0b-431f-83a9-5584e974e22b`).
- `Langlands.ClassField.Global.RelativeWeilGroup.LocalInducedRestrictionStatement.{uV, u}`
  (`Langlands/VirtualRepresentation/Global/RelativeWeilLocalRestrictionStatement.lean`):
  the local restriction formula for representations induced from `W_{E/K}`,
  with local maps `ιᵤ` whose transfer is inverse geometric local reciprocity.
  Proof task Task 5078 (`cfea3159-7908-43b1-a677-75834c3859bd`).
- The conclusion is the exact target
  `Langlands.ClassField.Global.RelativeWeilGroup.WeakInductionAssociationStatement.{u, uV, uP}`
  (`Langlands/Automorphic/WeakInductionAssociationStatement.lean`).

The first antecedent is needed only for existence: `IsUnramifiedMatchAt` demands a
local map at every place above `v`, and each local map comes with a geometric
reciprocity candidate of `L_w`. The arithmetic hypothesis
`IsArithmeticClassFamily c` of the target supplies exactly the hypotheses of the
second antecedent.

## Provenance

Internal. The implication is the step of Henniart (2000), §3.4, from Harris's weak
automorphic induction (Harris 1998, Definition 1.3(b)) to weak association with
`Ind_{W_{L/E'}}^{W_{L/F}} (ξ ∘ τ_{E'})`, with the local inputs isolated as
the published propositions above. The route through Tate's restriction formula
(Tate 1979, (2.3.5) with (1.6.1)) is the one sketched in the target pair's
Markdown and in the Markdown of `LocalInducedRestrictionStatement`. No source
statement is translated here. The proposition only chains published statements.

## Other declarations

All are proved; none is assumed.

- `FiniteRepresentation.eulerPolynomial_invariants_of_isUnramified I A hA g`: if
  the normal subgroup `I` acts trivially on `A`, the Euler polynomial of `g` on
  `A^I` is the Euler polynomial of `g` on `A`. The invariant subspace is `⊤` by
  the published `invariantSubspace_eq_top_iff_isUnramified`. Mathlib's
  `LinearEquiv.ofTop` conjugates the two operators, and the published
  `LocalFactor.eulerPolynomial_conj` concludes.
- `FiniteRepresentation.isUnramified_of_natDegree_eulerPolynomial_invariants`:
  if the Euler polynomial of some `g` on `A^I` has degree `rank A`, then `I` acts
  trivially. The published `eulerPolynomial_natDegree_representation` identifies
  that degree with `rank A^I`, and the published
  `invariants_rank_eq_iff_isUnramified` concludes.
- `Weil.Local.InertiaEuler.characterEulerPolynomial_weilCharacter_of_isUnramified`:
  for a geometric candidate `e` of a p-adic field `F` and a quasi-character `χ`
  trivial on the valuation units, the classical Euler polynomial of `χ ∘ e` is
  `1 - χ(ϖ) X`, with `ϖ` the canonical uniformizer. It uses the published
  `Correspondence.weilCharacter_eq_one_of_mem_localInertia` and
  `Correspondence.weilCharacter_apply_of_isUnramified`, with
  `localGeometricFrobenius_degree` for the degree one of `Fr`.
- `CompletionPadic.discreteValuation_padicFieldAt w h`: the normalized discrete
  valuation of the canonical package `padicFieldAt w h` is the completion
  valuation `Valued.v`. This is the published
  `AdelicFunctoriality.FiniteExtension.topologicalData_discreteValuation`
  transported by `topologicalData_eq_canonicalTopologicalData`.
- `CompletionPadic.valued_uniformizerUnit_padicFieldAt w h`: the canonical
  uniformizer of that package has `Valued.v` equal to `exp (-1)`, by the
  published `uniformizerUnit_zpow_value`.
- `CompletionPadic.isUnramifiedCharacter_quasicharacterAt w h χ hχ`: if the Hecke
  character `χ` is unramified at `w`, its component `χ_w` is trivial on the
  canonical valuation units of `K_w`. A unit of normalized order `0` has
  completion valuation `1` by the previous lemma. Such a unit and its inverse lie
  in the completed integers, so it lies in the unit group to which `IsUnramifiedAt`
  refers.
- `CompletionPadic.extensionResidueDegree_completionPadicAlgHom v w`: the residue
  degree of the completion embedding `F_v → K_w` is the inertia degree of `w`
  over `v`. The published `extensionResidueCardinality` gives
  `N(w) = N(v)^f`, using `residueCardinality_padicFieldAt` and
  `HeckeEulerProduct.residueCardinality_eq`. Mathlib's
  `Ideal.absNorm_pow_inertiaDeg` gives `N(w) = N(v)^{f(w|v)}`, and `N(v) > 1`
  (`one_lt_absNorm`) makes the exponent unique.
- `RelativeWeilGroup.natDegree_one_sub_C_mul_X`: `1 - z X` has degree one when
  `z ≠ 0`.
- `RelativeWeilGroup.characterEulerPolynomial_reciprocityCharacter_comp hrec ξ u hξ φ hφ`:
  at a place `u` of `K` above `v` where `ξ` is unramified, let `φ` be a local map
  `W_{K_u} → W_{E/K}` whose transfer is inverse geometric reciprocity for every
  geometric candidate. Then the classical Euler polynomial of
  `(ξ ∘ τ_K) ∘ φ` is `1 - ξ_u(ϖ_u) X`. The first antecedent supplies one
  geometric candidate `e_u`. The published
  `continuousReciprocityCharacter_comp_eq_weilCharacter` rewrites the character
  as the Weil character of `ξ_u` along `e_u`, and the previous lemmas conclude.
- `RelativeWeilGroup.exists_eulerPolynomial_localComponent_eq_prod hres h ξ hι`:
  for a local map `ι` at a place `w` of `L` above `v`, the local maps `ιᵤ` of the
  restriction formula have the transfer property. The Euler polynomial on inertia
  invariants of `S ∘ ι`, for `S = inducedReciprocityRepresentation c F E' L h ξ`,
  equals `∏_{u | v} P_u(X^{f_u})`. Here `P_u` is the classical Euler polynomial
  of `(ξ ∘ τ_{E'}) ∘ ιᵤ` and `f_u` is the residue degree of `F_v → E'_u`.
- `RelativeWeilGroup.isUnramifiedMatchAt_inducedReciprocityRepresentation`: the
  local matching at one place, described below.
- `RelativeWeilGroup.weakInductionAssociation_of_local hrec hmap hres`: the target
  under the three antecedents. `weakInductionAssociation_reduction` is this
  theorem in curried form.

## Proof

Write `S = inducedReciprocityRepresentation c F E' L h ξ`.

1. **Global data.** Let `s` be the spectral system attached to `π` that witnesses
   weak induction. The same `s` witnesses weak association. `S` is continuous for
   the default topology by the published
   `inducedReciprocityRepresentation_isContinuous`. Its rank is `[E' : F]` by
   `inducedReciprocityRepresentation_rank`, which is `r + 1` by the rank clause
   of weak induction. Both published lemmas are in
   `Langlands/Automorphic/InducedReciprocityBasic.lean`.
2. **Places.** The cofinite set of places is that of the weak induction,
   intersected with the complement of the exceptional set of `s`. At such a place
   `v` every place `u` of `E'` above `v` has ramification index `1`, `ξ` is
   unramified at `u`, and the Euler polynomial of `s` at `v` equals
   `inducedEulerPolynomial ξ v ϖ` for every uniformizer family `ϖ`. No place of
   `L` is excluded.
3. **Existence of local maps.** At a place `w` of `L` above `v`, the first
   antecedent gives a geometric candidate `e` of `L_w`. Destructuring
   `IsArithmeticClassFamily c` gives the hypotheses of the second antecedent,
   which gives `ι` with `IsLocalRelativeWeilMap v w e ι`.
4. **Euler polynomial along any local map.** Let `ι` satisfy
   `IsLocalRelativeWeilMap v w e ι`. The third antecedent at `K = E'` gives local
   maps `ιᵤ` and the restriction formula. Apply the formula to the published
   continuous class `characterClass (continuousReciprocityCharacter c E' L ξ)`.
   By the published `inducedReciprocityRepresentation_class`, the left side is
   the restriction of the class of `S` along `discreteLocalMap ι`, which is the
   class of `localComponent S ι`. The published `continuousRestrict_characterClass`
   turns the summands into inductions of character lines. Apply the published
   L-factor homomorphism `Weil.Local.InertiaEuler.lFactorHom (padicField v)`. By
   `lFactorHom_ofRepresentation` and
   `lFactorHom_continuousInduceAlong_characterClass`, the L-factor of
   `localComponent S ι` is the product of the L-factors of the induced lines.
   Inverting and using injectivity of `ℂ[X] → RatFunc ℂ`, the Euler polynomials on
   inertia invariants agree. The published
   `eulerPolynomial_induceAlong_characterLine` evaluates each factor as
   `expand f_u P_u`.
5. **Local characters.** By
   `characterEulerPolynomial_reciprocityCharacter_comp`, with the transfer
   property of `ιᵤ`, `P_u = 1 - ξ_u(ϖ_u) X`. Here `ϖ_u` is the canonical
   uniformizer of `towerPadicField v u`, and these uniformizers form a uniformizer
   family by `valued_uniformizerUnit_padicFieldAt`. With
   `f_u = f(u|v)` (`extensionResidueDegree_completionPadicAlgHom`) the product is
   `inducedEulerPolynomial ξ v ϖ`, hence the Euler polynomial of `s` at `v`.
6. **Unramifiedness by degree.** Each factor `expand f_u (1 - ξ_u(ϖ_u) X)` is
   nonzero, since `f_u > 0` by the published `extensionResidueDegree_pos`, and
   has degree `f_u`. The product has degree `Σ_u f(u|v)`. Since every
   ramification index is `1`, the published fundamental identity
   `finitePlacesAbove_sum_ramification_inertia` gives `[E' : F] = rank S`. So the
   Euler polynomial on the inertia invariants of `localComponent S ι` has full
   degree, and inertia acts trivially on `S ∘ ι`.
7. **Matching.** Since inertia acts trivially,
   `eulerPolynomial_invariants_of_isUnramified` identifies the published
   `localEulerPolynomial S ι` (on the whole carrier) with the Euler polynomial on
   invariants. By steps 4 and 5 that is the Euler polynomial of `s` at `v`.

The proof uses no unitarity of `ξ` or `π` and no finite-image or semisimplicity
assumption. It uses no global functional equation or local Langlands result.
Besides the three antecedents, only published proved theorems are used.
