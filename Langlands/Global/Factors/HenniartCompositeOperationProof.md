# Proof of the transport of the operation clauses to Henniart's composite map

Lean module: `Langlands.Global.Factors.HenniartCompositeOperationProof`.

## Statement proved

`Langlands.Global.PoleComparison.henniartCompositeOperation` proves
`Langlands.Global.PoleComparison.HenniartCompositeOperationStatement.{uF, uK, uW, uP}`
(Library `Langlands/Global/Factors/HenniartCompositeMapStatement.lean`). The
statement concerns a Galois extension `E/F` of number fields, a class family `c`,
a finite place `v` and an isometry
`T : weilImage F E c v ≃ₗ[ℤ] automorphicImage F E c v`. Suppose `T` is a generated
positive isometry (`RelativeGeneratedPositiveIsometry`) and has the contragredient,
twist and character clauses at `F_v` (`RelativeIsometryOperations`). Then for
every prime `p` with `residuePrime v = p`, every p-adic field `K` and every
`ℚ_p`-algebra isomorphism `f : K ≅ F_v`, the composite
`henniartCompositeMap F E c v h K f T` has `OperationProperties` at `K`. These are
the isometry, generator, contragredient, twist and character clauses of Henniart
(2000), 3.8 (a) and (c), for every geometric reciprocity candidate and every
modulus-one character of `K`. No hypothesis is added.

## Mathematical idea

Henniart's composite map at `K` (§3.7) has three steps. It pulls a class back
from `K` to `F_v` on the Weil side, applies `T`, and pulls back from `F_v` to `K`
on the supercuspidal side. Both pullbacks along `f`,
`completionWeilLatticeEquiv` and `completionSupercuspidalLatticeEquiv`, are
relabellings of the unitary lattices. They preserve the multiplicity pairings,
the degrees and the generators. They also commute with the contragredients. They
carry the twist by a character of `F_v` to the twist by the corresponding
character of `K`, and the rank-one class of a character of `F_v` to that of the
corresponding character of `K`. Each clause at `K` is therefore the image of the
same clause at `F_v`.

## Lemmas of this module

### Lattice facts

- `VirtualRepresentation.exists_generator_iff_of_map_generator`: suppose a linear
  equivalence `L` of integral lattices sends each generator `generator i` to
  `generator (e i)` for a bijection `e`. Then `L x` is a generator iff `x` is one.
- `VirtualRepresentation.exists_generator_of_pairing_self_eq_one`: let `d` be an
  integral functional that is positive on every generator. A vector `x` with
  `pairing x x = 1` and `0 < d x` is a generator. Proof:
  `integralNormOneSignedBasis` writes `x` as `± generator i`, and the minus sign
  contradicts positivity.
- `LocalWeil.unitaryDegree_generator(_pos)` and
  `PadicSupercuspidal.unitaryDegree_generator(_pos)`: the degree of a unitary
  generator is its rank, hence positive (`simp` through the definitions of the
  inclusion and of the ranked degree).

### Pullbacks at the completion

In namespace `Langlands.Global`, for `v`, `h : residuePrime v = p`, `K` and `f`
as in the statement:

- `exists_completionSupercuspidalLatticeEquiv_generator`: the supercuspidal
  pullback sends generators to generators along a bijection of unitary bases.
- `unitaryPairing_completionSupercuspidalLatticeEquiv`,
  `unitaryDegree_completionSupercuspidalLatticeEquiv`: it preserves pairings and
  degrees.
- `completionSupercuspidalLatticeEquiv_unitaryContragredientLatticeEquiv`: it
  commutes with the canonical contragredient.

Each of these four is proved by `subst h`, after which the pullback is
`PadicSupercuspidal.unitaryLatticeEquiv K (padicFieldAt v rfl) f`. The Library
lemmas `unitaryLatticeEquiv_generator`, `unitaryPairing_unitaryLatticeEquiv`,
`unitaryDegree_unitaryLatticeEquiv` and
`PadicSupercuspidal.unitaryLatticeEquiv_unitaryContragredientLatticeEquiv` (from
`Langlands.VirtualRepresentation.Supercuspidal.FieldTransportOperations`) then
apply.
- `completionWeilLatticeEquiv_generator`: the Weil pullback sends generators to
  generators along `Weil.restrictUnitaryBasisEquiv`.

### Clauses at `K`

In namespace `Langlands.Global.PoleComparison`:

- `RelativeGeneratedPositiveIsometry.exists_generator_iff`: a generated positive
  isometry sends exactly the generators of the Weil image to generators. For the
  forward direction, a generator has self-pairing one and positive degree, so
  the norm-one clause of the hypothesis applies. For the converse, `T x` is a
  generator, so `x` has self-pairing one (pairings are preserved) and positive
  degree (degrees are preserved). By
  `exists_generator_of_pairing_self_eq_one`, `x` is then a generator.
- `exists_eq_completionWeilLatticeEquiv`: every element of the transported Weil
  image is `⟨completionWeilLatticeEquiv v h K f y, _⟩` for some `y` in the Weil
  image. With the Library's `henniartCompositeMap_apply`, the composite on such
  an element is `completionSupercuspidalLatticeEquiv v h K f (T y)`.
- `henniartCompositeMap_eq_of_eq`: the same value for any representative `z` of
  the transported class with `z = completionWeilLatticeEquiv v h K f y`.
- `henniartCompositeMap_isometry`: `Isometry`. Pairings and degrees are preserved
  by both pullbacks (`Weil.unitaryPairing_restrictUnitaryLatticeEquiv`,
  `Weil.unitaryDegree_restrictUnitaryLatticeEquiv` and the supercuspidal lemmas
  above) and by `T`.
- `henniartCompositeMap_generatorCompatibility`: `GeneratorCompatibility`. It
  combines `exists_generator_iff_of_map_generator` for both pullbacks with
  `RelativeGeneratedPositiveIsometry.exists_generator_iff`.
- `henniartCompositeMap_dualCompatibility`: `DualCompatibility`. Take `x`, the
  transport of `y`. The clause at `F_v` puts the contragredient of `y` in the
  Weil image, and `T` of it is the contragredient of `T y`. The Weil pullback
  commutes with the contragredient
  (`completionWeilLatticeEquiv_unitaryDualLatticeEquiv`), so the contragredient
  of `x` is in the transported image. The supercuspidal pullback also commutes
  with the contragredient, which gives the equality.
- `henniartCompositeMap_twistCompatibility`: `TwistCompatibility` at `K` for
  `(e, χ)`. The inputs are a candidate `e'` and a modulus-one character `χ'` of
  `F_v` with three properties:
  - the Weil character of `χ'` along `e'`, restricted along
    `completionWeilEquiv`, is the Weil character of `χ` along `e` (`hcomp`);
  - the supercuspidal pullback carries the twist by `χ'` to the twist by `χ`
    (`hsc`);
  - the twist clause of `T` at `F_v` holds for `(e', χ')`.

  The proof has the same shape as the contragredient clause. It uses
  `completionWeilLatticeEquiv_unitaryFieldCharacterTwistLatticeEquiv` on the
  Weil side.
- `henniartCompositeMap_characterCompatibility`: `CharacterCompatibility` at `K`
  for `(e, χ)`. Its inputs are `hcomp`, the rank-one compatibility `hsc` of the
  supercuspidal pullback, and the character clause of `T` at `F_v` for
  `(e', χ')`. The witness is the transport of the witness at `F_v`. Its Weil
  class is handled by `includeUnitary_completionWeilLatticeEquiv_rankOne`, and
  its image by `henniartCompositeMap_apply` and `hsc`.
- `henniartCompositeMap_operationProperties_of`: `OperationProperties` at `K`.
  The hypotheses are the generated positive isometry and the operation clauses
  at `F_v`, together with the supercuspidal twist and rank-one compatibilities
  for every pair `χ`, `χ'` related by
  `∀ a b, (b : F_v) = f (a : K) → χ' b = χ a`. Given a geometric candidate `e`
  and a modulus-one `χ` of `K`:
  - `exists_geometric_completionReciprocity` gives a geometric `e'` of `F_v`
    with `rec_{F_v} ∘ φ = f ∘ rec_K`;
  - `exists_completionQuasiCharacter` gives a modulus-one `χ'` related to `χ`;
  - `weilCharacter_comp_completionWeilEquiv` gives `hcomp`.

  The clauses of `T` at `F_v` for `(e', χ')` then yield the clauses at `K`.

The final theorem `henniartCompositeOperation` introduces the data of the
statement. It applies `henniartCompositeMap_operationProperties_of` and
discharges the two supercuspidal compatibilities with the twist and rank-one
lemmas of `Langlands.Global.Factors.HenniartCompositeOperationSupercuspidalTwist`.

## Dependencies

- `Langlands.Global.Factors.HenniartCompositeMapStatement`: the target and
  `henniartCompositeMap_apply`.
- `Langlands.VirtualRepresentation.Supercuspidal.FieldTransportOperations`: the
  supercuspidal pullback commutes with contragredients and twists.
- `Langlands.Global.Factors.CompletionReciprocityTransport` and
  `Langlands.Global.Factors.HenniartCompositeOperationWeil`: transport of
  reciprocity candidates and characters, and the Weil-side commutation.
- `Langlands.Global.Factors.HenniartCompositeOperationSupercuspidalTwist`: the
  supercuspidal twist and rank-one compatibilities.
- `Langlands.VirtualRepresentation.DescentProof`: `integralNormOneSignedBasis`
  and `pairing_generator_self`.

## Reference

G. Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur un
corps p-adique*, Invent. Math. 139 (2000), §§3.7–3.8, page 451.

The generator-degree identities are reused from `Langlands.VirtualRepresentation.UnitaryDegreeGenerators`, which also serves the stable-image construction.
