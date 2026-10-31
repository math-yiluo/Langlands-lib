# Finite twisted coinvariants of irreducible cuspidal Levi representations

Author: Worker 288.

`Langlands.Whittaker.leviCuspidalCoinvariantFiniteness` proves exactly the
published proposition
[`LeviCuspidalCoinvariantFinitenessStatement.{uF,uV}`](LeviCuspidalCoinvariantFinitenessStatement.md).
The field universe `uF` and representation-carrier universe `uV` remain
independent. There are no additional premises.

For every prime `p`, p-adic field `F`, supplied topological data `T`, positive
rank `n` and ordered positive block shape `B`, the theorem installs
`T.topology`. Given an irreducible smooth complex representation `σ` of the
actual product Levi `B.Levi F.Carrier` satisfying
`CuspidalSupport.IsLeviCuspidal B σ.representation`, it proves finite
dimensionality of the actual quotient by

```lean
Subgroup.pi Set.univ
  (fun i : Fin B.length => GeneralLinear.upperUnipotent (B.size i) F.Carrier)
```

with respect to every locally constant complex-valued unit character `η`.
The quotient is by the span of `σ(u)v - (η u : ℂ) • v`, preserving the
positive-character convention. Arbitrary, trivial and degenerate characters,
blocks of size one and one-block shapes are included.

## Implemented proof

This is a derived assembly of published results.

1. Apply
   [`CuspidalSupport.padicLeviCuspidalFactorization`](../CuspidalSupport/LeviTensorFactorizationProof.md)
   to obtain actual irreducible supercuspidal block representations `A i`
   and an equivalence `e` from `σ.representation` to their block tensor.
   Instantiate both carrier universes of that theorem with `uV`; its field
   universe is still the independent `uF`.
2. Put `U i = upperUnipotent (B.size i) F.Carrier` and
   `θ i = FiniteTensor.coordinateCharacter U η i`. This restriction evaluates
   `η` on the tuple with the given element in coordinate `i` and identity
   elsewhere. The continuous coordinate insertions show that each `θ i` has
   locally constant complex values
   (`isLocallyConstant_coordinateCharacter`). The reconstruction theorem
   `productCharacter_coordinateCharacter` gives
   `FiniteTensor.productCharacter U θ = η`. Both results are in
   [`ProductCharacterDecomposition`](../Tensor/ProductCharacterDecomposition.md).
3. Apply the published theorem
   [`supercuspidalCoinvariantFiniteness`](SupercuspidalCoinvariantFinitenessProof.md)
   to each `A i`, using `B.positive i`, its irreducibility and its
   supercuspidality. This gives a finite-dimensional actual quotient for
   every `θ i`. Register these results as the family of local instances.
4. The equivalence
   [`Jacquet.Localization.representationEquiv`](../Jacquet/LocalizationTransport.md)
   induced by `e` identifies the quotient of `σ` at the product character
   with the quotient of the block tensor. The block tensor is definitionally
   `FiniteTensor.external`. The published
   [`FiniteTensor.characterLocalizationEquiv`](../Tensor/CharacterLocalization.md)
   identifies that second quotient with
   `PiTensorProduct ℂ (fun i => Coinvariants (A i).obj.representation (U i) (θ i))`.
5. Mathlib's `LinearAlgebra.PiTensorProduct.Finite` supplies finite
   dimensionality of this finite tensor product. The Lean expression
   `(L.symm.trans E.symm).finiteDimensional` transports it to the quotient
   of `σ` at the product character. Finally, transport along the exact
   character equality yields the quotient at the original `η`.

No nondegeneracy case split is needed in this assembly: the published
single-block theorem already handles every locally constant character.
It proves degenerate vanishing using a zero ordinary Jacquet quotient;
for a nondegenerate character it constructs a finite spanning set using
admissible principal-congruence fixed vectors, Iwasawa decomposition and
two bounds on torus translates. Its rank-one case has an empty set of
adjacent roots and is included. Consequently the applications at
`B.size i = 1` require no extra hypothesis.

## Source correspondence

The registered original is I. N. Bernshtein and A. V. Zelevinskii,
*Representations of the group GL(n,F) where F is a non-Archimedean local
field* (1976), source ID
`bernstein-zelevinsky-1976-representations-gln`, retained PDF SHA256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
Printed pages equal one-based PDF pages.

Theorem 7.12, step (5), printed p.61, decomposes `U ∩ G_β` into the product
of the block upper-unipotent groups and the restricted character into its
block characters. It concludes dimension zero or one for irreducible
cuspidal coefficients by the single-block assertion in §5.18, p.50.
The present theorem proves only the requested finite-dimensional consequence.
Its tensor factorization, character reconstruction and tensor-localization
equivalence implement the product step for an arbitrary character of the
actual abstract product Levi subgroup.

The quotient convention is Definition 2.30 and §§2.30–2.35, pp.24–25.
The character conventions are §§5.5–5.7, p.45. Proposition 5.15(a),
pp.49–50, supplies the source's degenerate vanishing step; §5.18 cites it
and Theorem 5.16. The published single-block proof uses the alternative
finite-spanning argument described above and does not assume the
source's stronger multiplicity-one assertion. These passages were read
for this task; the literature index and available source audits supplied
no relevant erratum.

## Dependencies and independence

The direct imports are the unchanged target statement, the published
single-block proof, Levi tensor factorization, product-character
decomposition, localization transport and Mathlib's finite tensor module.
Only this proof pair is new; the target pair and all its imports are
unchanged. The mathematical inputs are exactly the proved declarations
named in the five steps above.

The single-block proof was independently accepted and published before
use. Its integrated source was checked against the archived candidate:
the sole Lean refactor extracts the orbit-spanning lemma to the
Mathlib-only module `Langlands.Representation.OrbitSpan`. The entire
77-module Langlands import closure of that proof matches the supplied
Library. The proof and its transitive imports use none of the following
excluded inputs:

- The parent `IrreducibleCoinvariantFinitenessStatement`, its proof or
  consequences, or the parent-dependent mirabolic finite-length route.
  The lower proof also has no dependence on this Levi statement or proof.
- `MultiplicityOneStatement`, `SupercuspidalKirillovStatement`,
  `SupercuspidalDerivatives`, a top-derivative comparison, additive
  self-duality, or an unproved proposition used as a theorem.
- Segment socle or head existence, irreducibility, reducibility,
  commutation, gluing, Jacquet or derivative formulas; multisegment
  existence or exhaustion; the two-supercuspidal product conclusions;
  generic segment uniqueness; special-head product criteria; tempered
  uniqueness; or square-integrable, analytic or regular classification
  and exhaustion. Thus the complete segment and BZ77 consumer exclusions
  of the single-block task remain satisfied. The imported
  `Classification.SupercuspidalDerivativeVanishing` contributes only
  elementary block-unipotent matrix lemmas to that lower proof.

The remaining assembly inputs are tensor factorization, algebraic
quotient equivalences, elementary finite-product character restrictions
and finite-dimensional tensor products. They do not invoke the parent
finiteness conclusion. The full assembly's 174-module Langlands import
closure was also checked: every existing Lean source matches the supplied
Library, and the only occurrence of the Levi target is its statement and
this proof. None of the other excluded conclusions occurs in the closure.
The factorization imports include `Classification.Segments` and
`Classification.ConstituentRelations` for definitions and elementary
transport identities; they supply no segment existence, derivative or
classification theorem. A finite-length predicate and a cuspidal-induction
length proposition also occur transitively, but no mirabolic finite-length
proof or parent coinvariant-finiteness conclusion is imported or applied.
The closed proof adds no theorem-valued hypothesis, proof hole or new axiom.
