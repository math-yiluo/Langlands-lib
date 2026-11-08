# The actual Weil pushout class of a finite unramified extension

Author: Worker 1556. Worker 1839 is a coauthor through the reused modules
`Langlands.GroupTheory.ExtensionAkizukiWitt` and
`Langlands.Weil.Local.FiniteGaloisEquivariance`. This is a derived unit for task
`37d6d58f-e378-4630-8a8c-0f3d7212a970`. All declarations are in
`Langlands.Weil.Local`.

## Setting

Fix a prime `p`, p-adic fields `F : PadicField.{u} p` and `E : PadicField.{v} p`,
and an embedding `f : F.Carrier →ₐ[Padic p] E.Carrier`. Fix
`hGal : IsGalois F.Carrier E.Carrier` for the algebra structure
`extensionAlgebra F E f`. Write `q = finiteGaloisQuotient F E f hGal` for the
actual quotient `W_F → Gal(E/F)`. Write `Φ = localGeometricFrobenius F`; it has
degree one. `finiteGaloisClass F E f hGal e he` is the class, in the existing
relative `H²`, of the actual Weil pushout built from a geometric reciprocity
candidate `e` of `E` (module `FiniteGaloisPushout`).

## Results

- `ord_reciprocityUnits_localGeometricFrobenius`: if
  `heF : GeometricWeilReciprocityRelation F F.canonicalTopologicalData eF`,
  then `ord (reciprocityUnits F eF Φ) = 1`. This is the geometric order relation
  `heF.1` evaluated at `Φ`, together with `localGeometricFrobenius_degree`.
- `finiteGaloisRestriction_inverse_power_congruence`: assume `Gal(E/F)` is
  commutative, and let `σ` be an absolute Galois element with
  `localResidueMap F σ = geometricFrobenius`. Then for every `x : E` with
  canonical discrete valuation at most one, the element
  `(finiteGaloisRestriction σ).symm x - x ^ q_F` has canonical discrete
  valuation below one. Here `q_F` is `F.canonicalTopologicalData.residueCardinality`.
  The proof moves to the image field `J = extensionFiniteIntermediate F E f` in
  the algebraic closure of `F`. It packages `J` as an actual finite abelian
  extension `L`, which is Galois and abelian because `E ≃ J` over `F`. It then
  applies the published `finite_inverse_power_congruence` (module
  `Correspondence.BaseGeometricResidue`) to `L`. The result is carried back to
  `E` along the `Padic p`-algebra isomorphism `E ≃ L` built from
  `extensionIntermediateFieldEquiv`. It preserves canonical discrete
  valuations by `PadicField.CanonicalTransport.discreteValuation_map`, and on the
  algebraic closure it intertwines `σ⁻¹` with the restriction of `σ⁻¹`.
- `finiteGaloisQuotient_inv_localGeometricFrobenius`: let
  `χ : Gal(E/F) ≃* Multiplicative (ZMod n)` be an arithmetic unramified
  coordinate (`IsArithmeticUnramifiedCoordinate F E.Carrier χ`). Then
  `χ (q Φ⁻¹) = ofAdd 1`: the inverse of geometric Frobenius maps to the
  arithmetic Frobenius. The proof takes the commutativity of `Gal(E/F)` from
  `χ`, applies the previous congruence to `σ = localProjection F Φ`
  (`localGeometricFrobenius_residue`), and uses the published
  `FiniteArtinSystemUniqueness.inverse_coordinate_eq_one`.
- `frobeniusPowerSection F E f hGal χ hχ` is the normalized section of `q`
  given by `powerSection` for the generator `Φ⁻¹`. By
  `frobeniusPowerSection_apply` it sends `g` to `Φ⁻¹ ^ (χ g).toAdd.val`.
- `finiteGaloisClass_eq_cyclicClass`: assume the transfer square
  `hT : ExtensionWeilTransferReciprocityStatement.{u,v}`. Let `eF` be a geometric
  candidate of `F`, `e` one of `E`, and `χ` an arithmetic unramified coordinate.
  Then
  `finiteGaloisClass F E f hGal e he = cyclicClass F E χ (reciprocityUnits F eF Φ)`.
  The proof follows these steps.
  1. By `finiteGaloisClass_eq_of_section` the class may be computed with
     `frobeniusPowerSection`, the power section of `q` for the generator `Φ⁻¹`.
  2. `cocycle_powerSection` writes the cocycle as
     `r (Φ⁻ⁿ) ^ cyclicCarry (χ g) (χ h)`, where `r` is the inverse kernel
     reciprocity map.
  3. `transfer_powerSection`, with the kernel equality `finiteGaloisQuotient_ker`,
     shows that the transfer of `reciprocityUnits E e ∘ rangeInverse` at `Φ⁻¹`
     is its value at `Φ⁻ⁿ`. The transfer square `hT` at `Φ⁻¹` identifies this
     value with `f (reciprocityUnits F eF Φ⁻¹)`. Hence
     `r (Φ⁻ⁿ) = f (reciprocityUnits F eF Φ)`.
  4. The resulting cocycle is exactly `cyclicUnitCocycle`, whose class is
     `cyclicClass`.
- `finiteGaloisClass_isFundamental_of_unramified`: let `F M : PadicField.{u} p`,
  `f : F →ₐ M` with `M/F` Galois, and
  `F.ramificationIndex = M.ramificationIndex`. Take geometric candidates
  `eF`, `eM`, the transfer square `hT`, and an invariant family `J` with
  `J.ArithmeticNormalization`. Then `finiteGaloisClass F M f hM eM heM` is a
  fundamental class for `J.relative F M`, that is, its invariant is
  `reciprocalClass [M : F]`. The arithmetic coordinate comes from the published
  `arithmeticUnramifiedCoordinateExistence`. The class is then the cyclic class
  of a unit of order one, so arithmetic normalization applies.

## Scope and provenance

Provenance is derived. This is the classical computation that the Weil group
extension class of an unramified extension of degree `n` is the cyclic class of a
uniformizer, at the arithmetic Frobenius. Its invariant is `1/n` (Tate, "Number
theoretic background" (1979), §1; Artin–Tate, Chapter XV; Serre, *Local Fields*,
Chapter XIII). The only hypothesis beyond the local data is the transfer
square `ExtensionWeilTransferReciprocityStatement`. It is the published
statement that geometric reciprocity carries the transfer `W_F → W_E^{ab}` to the
inclusion `Fˣ → Eˣ`, and it is passed as an explicit premise, not proved here.
Existence of Weil reciprocity for `F` and `E` is not assumed: the candidates and
their geometric relations are explicit inputs.
