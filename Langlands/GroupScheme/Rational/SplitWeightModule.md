# Torus weights on modules over the operator algebra of a split group

Author: Worker 902.

This module is internal infrastructure for the proof of Milne's character theorem
(Theorem 22.38) in
[`Rational.SplitRepresentationCharacterReduction`](SplitRepresentationCharacterReduction.md).
It defines torus weight spaces on arbitrary modules over the operator algebra
`OperatorAlgebra G` of
[`MatrixRepresentation.OperatorModule`](../MatrixRepresentation/OperatorModule.md). It shows
that they agree with the Library's `p.representationWeightSpace ρ lam` on the module of an
actual representation. It also shows that their dimensions are invariant under module
isomorphisms and add over direct sums. Throughout, `k` is a field, `G` an affine group scheme
over `Spec k` and `p : SplitPinning G`.

## Realized modules

`MatrixRepresentation.IsRealized G M` says that the module `M` over the operator algebra
embeds, by an injective module map, into `OperatorModule τ` for some
`τ : MatrixRepresentation G (Fin r)`.

- `isRealized_operatorModule`, `IsRealized.of_injective` and `IsRealized.submodule`:
  modules of representations in coordinates `Fin r` are realized, and so are modules that
  embed into a realized module, in particular its submodules.
- `IsRealized.finiteDimensional`: a realized module is finite-dimensional over `k`.
- `isRealized_of_injective`: embedding into the module of a representation in arbitrary
  finite coordinates `n` is enough (apply `exists_linearEquiv_submodule` to `⊤`).
- `IsRealized.exists_linearEquiv`: a realized module is isomorphic to `OperatorModule τ`
  for some `τ` in coordinates `Fin r` (apply `exists_linearEquiv_submodule` to the range
  of the embedding).

## Weight spaces

The torus-local instance `splitWeightModuleTorusIsAffineHom` records that the split torus
is affine (`p.isSplitTorus.isAffineHom`), as other Library modules do locally.

- `torusPoint` is the universal point of the torus, `CharacterUnits.universalPoint`,
  composed with `p.inclusion`. It is a point of `G` with values in the torus coordinate
  algebra `CharacterUnits.Coord p.torus.toGrp`.
- `torusOperator ℓ` is the operator index `(Coord, torusPoint, ℓ)`.
- `weightUnit lam` is the unit of the torus coordinate algebra given by the character `lam`
  (through `rationalCharacters.equivCharacterLattice`).
- `weightSubmodule M lam` is the `k`-subspace of those `v : M` with
  `ι(torusOperator ℓ) • v = ℓ(weightUnit lam) • v` for every functional `ℓ` on the torus
  coordinate algebra.

Formal properties, valid for every module:

- `map_mem_weightSubmodule`, `mem_weightSubmodule_of_injective` and
  `weightSubmodule_ne_bot_of_injective`: module maps preserve weight spaces, and injective
  module maps reflect membership.
- `weightSubmodule_map_linearEquiv` and `finrank_weightSubmodule_eq_of_linearEquiv`: a
  module isomorphism maps weight spaces onto weight spaces of the same dimension.
- `weightSubmoduleProdEquiv`, `finrank_weightSubmodule_prod`, `weightSubmodulePiEquiv` and
  `finrank_weightSubmodule_pi`: the weight spaces of a binary product or of a finite product
  are the products of the weight spaces, so their dimensions add.
- `weightProjector lam` is the operator `ι(torusOperator ℓ_lam)`, where `ℓ_lam` is the
  Library's `characterCoefficient` of `lam`, the coefficient of the basis unit of `lam`.
  `weightProjector_smul_of_mem` (by `characterCoefficient_unit`): it acts as the identity
  on the weight space of `lam` and as zero on the weight space of every other `mu`.

## Comparison with representations

For `ρ : MatrixRepresentation G n`:

- `toModule_mem_weightSubmodule_iff` and `weightSubmodule_operatorModule`: the weight space
  of `lam` in `OperatorModule ρ` is the image of `p.representationWeightSpace ρ lam`.
  The Library's `mem_characterSpace_iff` says that `v` lies in the character space when the
  universal torus matrix sends the scalar extension of `v` to `weightUnit lam` times it.
  Both sides are compared through all functionals `ℓ` (`vector_ext_of_functionals`).
- `finrank_weightSubmodule_operatorModule`: the dimensions agree.
- `iSup_weightSubmodule_operatorModule`: the weight spaces span, by the Library's
  `iSup_representationWeightSpace_eq_top`.
- `exists_finset_eq_sum_weightProjector` and `weightProjector_smul_mem_operatorModule`:
  every vector is the sum of its weight projections over a finite set of weights, and
  `weightProjector lam` maps into the weight space of `lam`.
- `finite_weightSubmodule_ne_bot_operatorModule`: only finitely many weight spaces are
  nonzero, by independence of character spaces (`characterSpace_iSupIndep` and Mathlib's
  `Submodule.finite_ne_bot_of_iSupIndep`).

## Realized modules, continued

Transporting along the embedding:

- `weightProjector_smul_mem_of_isRealized`: `weightProjector lam` maps a realized module
  into its weight space of `lam`.
- `eq_zero_of_isRealized_of_weightSubmodule_eq_bot`: a realized module whose weight spaces
  are all zero is zero.
- `finite_weightSubmodule_ne_bot_of_isRealized`: a realized module has only finitely many
  nonzero weight spaces.
- `exists_isSimpleModule_weightSubmodule_ne_bot_of_isRealized`: in a realized semisimple
  module with a nonzero weight space for `lam`, some simple submodule has a nonzero weight
  space for `lam`. Otherwise `weightProjector lam` kills every simple submodule. Since these
  span the module (`IsSemisimpleModule.sSup_simples_eq_top`), it kills the whole module,
  but it fixes a nonzero vector of weight `lam`.
- `finrank_weightSubmodule_eq_add_of_isCompl`: for complementary submodules `S`, `T` of a
  finite-dimensional module, the weight dimensions of the module are the sums of those of
  `S` and `T` (`Submodule.prodEquivOfIsCompl` and the product formula).

## Characters of direct sums

- `exists_finrank_representationWeightSpace_eq_sum`: for a finite family of
  representations `τ i`, there is `σ : MatrixRepresentation G (Fin r)` whose weight
  multiplicities are the sums of those of the `τ i`. Here `σ` is a coordinate model of the
  Library's `directSum τ`, and the sum formula comes from `directSumModuleEquiv` and
  `finrank_weightSubmodule_pi`.
- `exists_finrank_representationWeightSpace_eq_add`: the same for two representations.
- `exists_finrank_representationWeightSpace_eq_zero`: some representation (the empty direct
  sum) has every weight multiplicity zero.

## Provenance

The definitions are internal. `weightSubmodule` is the classical torus eigenspace
`V_λ = {v | t·v = λ(t)v}` (Milne, *Algebraic Groups* (2017), Example 22.36, printed p. 473),
read off from the coefficient operators at the universal torus point. Its agreement with
the Library's `representationWeightSpace` is proved here, so it introduces no new notion of
weight. The additivity of characters over direct sums is part of Milne's definition of the
character map on the Grothendieck group (p. 474).
