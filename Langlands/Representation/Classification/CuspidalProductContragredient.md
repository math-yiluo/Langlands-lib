# Contragredients and determinant twists of cuspidal products

Author: Worker 1166. Two arguments follow Worker 264's published proofs (see
"Credits" below).

This internal helper pair belongs to task
`0b3bf4c1-9878-444f-899e-ba29d7679c29`, the proof of
`Langlands.Classification.CuspidalProductMirabolicSupportShift` (BZ77 Lemma
4.7(b), mirabolic form). That proof dualizes the cuspidal product
`π = A_1 × ⋯ × A_r` and the irreducible representation `σ`. This module supplies
the facts about duals and twists that the dualization needs:

- the cuspidal datum `ρ̃` of the contragredient, and how it interacts with the
  twist `ν^s` (`ν = |det|`);
- the representatives `Ã` and `|det|^t Ã` of the data `ρ̃` and `ν^t ρ̃`;
- `(A_1 × ⋯ × A_r)~ ≅ Ã_1 × ⋯ × Ã_r` and
  `ν^t Ã_1 × ⋯ × ν^t Ã_r ≃ |det|^t (A_1 × ⋯ × A_r)~`;
- if `s` is a supercuspidal support of an irreducible `σ`, then `s̃` is one of
  `σ̃`.

It does not prove the task target. All declarations are in the namespace
`Langlands.Classification.CuspidalProductContragredient`. The pair introduces no
proposition definitions, no axioms, no theorem-valued premises and no
`set_option`. Every result is proved from published Library results only.

Throughout, `p` is a prime, `F : PadicField p` and `T : F.TopologicalData`.
Every topology on `F` or on a group `GL_n(F)` is the supplied one:
`T.topology` and `T.generalLinearTopologicalGroup n`, introduced by `letI`
inside each statement.

## Data

- `dualClass ρ` is
  `T.supercuspidalClassContragredient supercuspidalContragredient ρ.rank ρ.cls`,
  the isomorphism class of the smooth contragredient of any representative of
  `ρ`. It is marked `@[irreducible]`. `dualClass_def` states its defining
  equation; proofs unfold it only through this lemma. (Reason: without it,
  type-checking a product over the data `ρ̃_i` makes Lean compare `ρ̃_i` with
  `ρ_i` by unfolding the contragredient class, and the elaboration of the
  product lemmas below times out.)
- `dualDatum ρ` is the cuspidal datum with the same rank and class
  `dualClass ρ`, written `ρ̃`. `dualDatum_rank` (rank unchanged, by `rfl`) and
  `dualDatum_cls` (class is the contragredient class) record its fields.
- `dualDatum_dualDatum : dualDatum (dualDatum ρ) = ρ`, from the published
  involutivity `T.supercuspidalClassContragredient_involutive`.
- `classContragredient_realPowerTwist`: dualizing a class commutes with
  `ν^s ↦ ν^(-s)`, i.e. the class of `(|det|^s A)~` is that of `|det|^(-s) Ã`.
  Proof: the published `SupercuspidalClass.contragredient_twist`, plus
  `realPowerCharacter_neg` to identify the inverse of `|det|^s` with
  `|det|^(-s)`.
- `dualDatum_twist : dualDatum (ρ.twist s) = (dualDatum ρ).twist (-s)`, i.e.
  `(ν^s ρ)~ = ν^(-s) ρ̃`.
- `twistedDualData t ρ` is the family `i ↦ (dualDatum (ρ i)).twist t`, i.e.
  `ν^t ρ̃_i`. `twistedDualData_rank` and `sum_twistedDualData_rank` record that
  ranks, and hence rank sums, are unchanged (both by definitional equality).
- `ofFn_twistedDualData`: the multiset `List.ofFn (twistedDualData t ρ)` is the
  image of `List.ofFn ρ` under `x ↦ ν^t x̃`.
- `twist_le_of_dual_le`: if `s.map dualDatum ≤ List.ofFn (twistedDualData 1 ρ)`
  as multisets, then `s.map (CuspidalDatum.twist 1) ≤ List.ofFn ρ`. Proof: apply
  the map `x ↦ ν x̃` to both sides (`Multiset.map_le_map`). On the left,
  `ν (x̃)~ = ν x` by `dualDatum_dualDatum`. On the right,
  `ν (ν ρ̃)~ = ν ν^(-1) ρ = ρ` by `dualDatum_twist`, `dualDatum_dualDatum` and
  `CuspidalDatum.twist_twist`. Multiplicities are respected throughout.

## Products

Here `B : BlockShape n` is a block shape, and `T.normalizedProductInduced B σ`
is the published normalized parabolic induction of the external tensor product
of the blocks `σ_i`.

- `determinant_parabolic`: for an element `g` of the upper block parabolic
  subgroup over a commutative ring, `det g` is the product of the determinants
  of its diagonal blocks `B.leviProjection R g i`. Proof: reindex the matrix
  through `B.indexEquiv`, where it is block triangular, and use
  `Matrix.BlockTriangular.det_fintype`.
- `determinantPowerCharacter_leviEmbedding` and
  `determinantPowerCharacter_parabolic`: `|det|^t` of a block-diagonal element,
  and of an upper block parabolic element, is the product of `|det|^t` of its
  blocks. Both write `|det|^t` as a monoid homomorphism composed with the
  determinant and use `determinant_leviEmbedding` (published) and
  `determinant_parabolic`.
- `nonempty_twist_productEquiv`: for every block family `σ` (no admissibility
  needed),
  `|det|^t (σ_1 × ⋯ × σ_r) ≃ (|det|^t σ_1) × ⋯ × (|det|^t σ_r)`,
  as an equivalence of linear representations of `GL_n(F)`. Proof: the published
  `Induction.smoothInductionTwistEquiv` moves the twist by the smooth character
  `|det|^t` of `GL_n(F)` inside the induction, where it becomes the twist by its
  restriction to the parabolic. That restriction equals `|det|^t` of the Levi
  projection, by `determinantPowerCharacter_parabolic`. On the Levi, the twist of
  the external tensor product by a character that factors over the blocks is
  the tensor product of the twisted blocks (`SmoothCharacter.external_coordinate_twist`;
  the coordinates are computed by `determinantPowerCharacter_leviEmbedding`).
  The two twists by `|det|^t` and the modulus half commute.
- `nonempty_contragredient_productEquiv`: for admissible blocks `τ_i`,
  `(τ_1 × ⋯ × τ_r)~ ≃ τ̃_1 × ⋯ × τ̃_r`, where `~` is the smooth contragredient.
  Proof: the published normalized induction duality
  `Parabolic.naturalNormalizedInductionDuality` for the admissible external
  tensor product (`FiniteTensor.isAdmissible_external`), then the published
  bijectivity of the smooth-dual tensor map
  (`FiniteTensor.smoothDualTensorInjectivity`,
  `FiniteTensor.smoothDualTensorMap_surjective`, using that `GL_m(F)` has a
  cofinal family of compact open subgroups, `compactOpen_cofinal`) to identify
  the dual of the tensor product with the tensor product of the duals.

## Representatives

- `dualRep T A` is the published smooth contragredient of a supercuspidal
  representation `A` (`SupercuspidalRep.contragredient`), with
  `dualRep_obj` recording that its underlying object is `A.obj.contragredient`.
- `twistedDualRep T t A` is the published twist
  `SupercuspidalRep.twist (T.determinantPowerCharacter n t)` of `dualRep T A`,
  i.e. `|det|^t Ã`.
- `dualRep_represents` and `twistedDualRep_represents`: if `A` represents `ρ`,
  then `Ã` represents `ρ̃` and `|det|^t Ã` represents `ν^t ρ̃`.
- `cuspidalProductInduced_dualDatum` and
  `cuspidalProductInduced_twistedDualData` (both by `rfl`): the published
  cuspidal products `T.cuspidalProductInduced` over the data `ρ̃_i` and
  `ν^t ρ̃_i`, with these representatives, are the normalized products over the
  block shape `T.cuspidalShape ρ h` of the original data. Proofs rewrite with
  these lemmas first, so that the block-shape equivalences above apply over the
  shape of `ρ` (this, together with the irreducible `dualClass`, is what keeps
  elaboration fast).
- `nonempty_contragredient_cuspidalProductIso`:
  `(A_1 × ⋯ × A_r)~ ≅ Ã_1 × ⋯ × Ã_r` in the category of smooth representations,
  from `nonempty_contragredient_productEquiv` (supercuspidal representations are
  admissible: `(A i).property.2.1`).
- `nonempty_twistedDual_cuspidalProductEquiv`:
  `ν^t Ã_1 × ⋯ × ν^t Ã_r ≃ |det|^t (A_1 × ⋯ × A_r)~` as linear
  representations, combining the two product equivalences with `twistEquiv`.

## Subquotients

`isSubquotient_of_injective_of_surjective` holds for smooth representations of
any topological group over any commutative ring: if `i : B ⟶ C` is injective and
`r : A ⟶ C` is surjective, then `B` is a subquotient of `A`
(`SmoothRep.IsSubquotient`). Proof: let `D ⊆ A` be the preimage under `r` of the
image of `i`. It is a subrepresentation, and `r` followed by the inverse of `i`
on its image is a surjective intertwiner `D ⟶ B`. The intertwining property
is checked after applying the injective `i`. The published
`SmoothRep.isSubquotient_iff_exists` then gives the claim.

## Support

- `isCuspidalConstituent_contragredient`: if `T.IsCuspidalConstituent ρ σ`
  (so `σ` is an irreducible subquotient of some product of representatives of
  `ρ`), then `T.IsCuspidalConstituent (fun i => dualDatum (ρ i)) σ̃`. Proof: `σ`
  is admissible (the published `CuspidalSupport.cuspidalEmbedding`, first
  component), so `σ̃` is irreducible
  (`SmoothRep.isIrreducible_contragredient_iff`). Write `σ` as a quotient
  `q : C ↠ σ` of a subrepresentation `i : C ↪ π`. Dualizing gives `σ̃ ↪ C̃` and
  `π̃ ↠ C̃`, by the published exactness of the smooth contragredient
  (`contragredientMap_injective_of_surjective`,
  `contragredientMap_surjective_of_injective_of_compact_cofinal`). So `σ̃` is a
  subquotient of `π̃` by `isSubquotient_of_injective_of_surjective`. Finally
  `π̃ ≅ Ã_1 × ⋯ × Ã_r` by `nonempty_contragredient_cuspidalProductIso`, and
  `Ã_i` represents `ρ̃_i`.
- `isSupercuspidalSupport_contragredient`: if `T.IsSupercuspidalSupport σ s`,
  then `T.IsSupercuspidalSupport σ̃ (s.map dualDatum)`. This is the previous
  lemma applied to the witness family of `s`.

## Universes

`dualClass`, `dualDatum`, `twistedDualData` and the representatives are at the
universes of `T.CuspidalDatum.{uV, uF}` and `SupercuspidalRep.{uF, uV}`. The
support lemmas concern `σ : SmoothRep.{0, uF, max uF uV} ℂ (GL_n(F))`, the
universe of `T.cuspidalProductInduced` and of `IsSupercuspidalSupport`. The
subquotient lemma is universe-polymorphic.

## Provenance

The module is internal. The mathematical facts are standard properties of
parabolic induction and smooth duality. For example, the contragredient of a
normalized induced representation is BZ77 Proposition 2.3(d) (printed p. 446),
and the contragredient itself is BZ77 §1.4 (printed p. 443). Each fact is
derived here from the published Library results named above, specialized to
cuspidal products. `dualDatum` and `twistedDualData` are bookkeeping names for
the data `ρ̃` and `ν^t ρ̃` of the source.

## Credits

`determinant_parabolic` and `nonempty_twist_productEquiv` follow the argument
of Worker 264's published `Classification.TwistedProductCharacterTwistProof`.
`nonempty_contragredient_productEquiv` follows Worker 264's published
`Classification.TwistedProductOrdinaryDualProof`, without segment exponents.
Those modules are not imported, because their import closures contain
`Classification.UnitaryGenericCompatibilityStatement`. This module needs only
the plain block-product forms.

## Import closure

The module imports only published Library modules: the cuspidal-support
definitions (`Classification.SupercuspidalSupport`), supercuspidal
contragredients (`Classification.SupercuspidalContragredient` and its proof),
normalized induction duality, smooth-dual tensor injectivity and surjectivity,
block and twist equivalences of induction, smooth-part twists, the flattened
modulus calculation, exactness of the smooth contragredient and the cuspidal
embedding. At Library commit `b22e185743f7c318f709e14e422801f4360105d5`, its
transitive Langlands import closure has 239 modules. None is a module of the
excluded task `f81d9b36` (`HighestDerivativeSupportShiftBoundary`,
`CuspidalProductDerivativeQuotientSupport`, its main proof), or
`CuspidalSupport.WholeLeviTransport`, any Leibniz-rule or exactness-of-derivative
module, `UnitaryGenericCompatibilityStatement`, or a `TwistedProduct*` /
`TwoSupercuspidalProductDualTwist` module.
