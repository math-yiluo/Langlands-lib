# Small-universe tensor exhaustion for cuspidal standard Levis

Author: Worker 82.

`Langlands.CuspidalSupport.padicLeviCuspidalFactorization.{uF,uW,uV}`
proves exactly the published proposition
`Langlands.CuspidalSupport.PadicLeviCuspidalFactorizationStatement.{uF,uW,uV}`.
For the supplied topology on an actual p-adic field in `uF`, every
irreducible cuspidal smooth representation of a positive-rank ordered
standard Levi with carrier in `uW` is equivalent to the actual block tensor
of irreducible supercuspidal representations with carriers in `uV`.
All three universes are independent. The one-block case is included.

## Provenance and imported results

This proof is derived composition of the Library results below. The
[target's source correspondence](LeviTensorFactorizationStatement.md)
records the original mathematical context: Flath's two-factor existence,
Bernstein–Zelevinsky's standard Levis and cuspidality, and Zelevinsky's
factorwise quasicuspidality. The change of carrier universe is additional
derived mathematics, as explained in that target and in the small-realization
proof. The present module imports the proofs by Lean name and does not repeat
their arguments.

- `padicLeviAdmissibleFactorization.{uF,uW}`, from
  [LeviAdmissibleFactorizationProof](LeviAdmissibleFactorizationProof.md),
  by Worker 161, gives admissible irreducible smooth block factors in `uW`
  and an actual representation equivalence to their block tensor.
- `padicLeviTensorSupercuspidalReflection.{uF,uW}`, from
  [LeviTensorReflectionProof](LeviTensorReflectionProof.md), by Worker 158,
  deduces supercuspidality of every irreducible admissible factor from
  quasicuspidality of the actual block tensor. Its conclusion includes
  vanishing for conjugates of proper standard unipotent radicals.
- `Langlands.padicIrreducibleSmoothSmallRealization.{uF,uW,uV}`, from
  [SmallRealizationProof](../Smooth/SmallRealizationProof.md), by Worker 273,
  constructs an irreducible smooth representation in independently
  prescribed `uV` and an equivalence from the original representation.
  Its proof obtains a countable spanning orbit and basis, then reindexes
  the basis into a carrier in the requested universe.

The target and every pair it imports remain unchanged.

## Tensoring the factor equivalences

The private construction `blockTensorEquiv` accepts a family of actual
representation equivalences between block actions on carriers in `uW`
and `uV`. Its underlying complex-linear equivalence is
`PiTensorProduct.congr` applied to the factor linear equivalences.

To prove equivariance, the implementation fixes a tuple of block matrices
and checks the required linear-map equality on pure tensors.
`BlockShape.blockTensor_tprod` describes the coordinatewise action, while
`PiTensorProduct.congr_tprod` describes the tensor equivalence on generators.
The equality in each slot is the factor equivalence's intertwining identity
evaluated on that slot's vector. Thus this is an equivalence of the actual
block representations, including across different carrier universes.

## Closing proof

The theorem introduces the prime, field, supplied topological data, positive
rank and block shape, and installs `T.topology`. Given the source `σ`,
irreducibility and `IsLeviCuspidal B σ.representation`, it proceeds as follows.

1. The admissibility component of cuspidality and the source irreducibility
   let `padicLeviAdmissibleFactorization` produce factors `A`, their
   factorwise irreducibility and admissibility, and an equivalence `efactor`
   from the source to their block tensor.
2. `isLeviQuasicuspidal_iff_of_equiv B efactor` transfers the source's
   quasicuspidality to that tensor. Apply
   `padicLeviTensorSupercuspidalReflection` using this fact and the two
   factorwise properties. This gives supercuspidality of every `A i`.
3. Apply `padicIrreducibleSmoothSmallRealization` to each `A i`.
   Classical choice selects a smooth representation `C i` in `uV`,
   its irreducibility proof, and a representation equivalence from `A i`.
   `GeneralLinear.isSupercuspidal_of_equiv` transfers supercuspidality along
   that equivalence. Package these data as `SupercuspidalRep.{uF,uV}`
   objects `D i`.
4. Apply `blockTensorEquiv` to the chosen factor equivalences. Compose it
   with `efactor` and package the result in `Nonempty`. This is exactly
   the target's equivalence to `B.blockTensor` of the actions of `D`.

Every existence input in this argument is a proved imported theorem.
There is no extra factorization, smallness, cardinal bound, shrinking
equivalence, or universe-identification hypothesis. The implementation
uses no proof holes or new axioms. The conclusion is exhaustion; it
asserts neither uniqueness of the factors nor a classification of supports.
