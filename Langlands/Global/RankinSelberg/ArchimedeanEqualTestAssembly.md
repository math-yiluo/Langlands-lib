# Assembly with prescribed finite local Fourier partners

This internal module constructs the global test function and its two exact
product formulas from archimedean Schwartz functions and finite local Fourier
pairs. The entry proposition is
`Langlands.Global.RankinSelbergGlobal.EqualSchwartzTensor.LocalFourierTestAssemblyReductionStatement`,
proved by `localFourierTestAssemblyReduction`. It retains
`RectangleTateStatement` as an explicit premise. The unconditional equal-rank and
full archimedean factorization targets remain open.

This is derived implementation infrastructure for the test-function clauses of
the published target. Its provenance is the existing tensor construction, local
test-function and Fourier-pair definitions, and the conditional Fourier formula
in `ArchimedeanSchwartzFourier`. It claims no new direct literature translation.
All unqualified names below are in the namespace
`Langlands.Global.RankinSelbergGlobal.EqualSchwartzTensor`.

## Local adapters

`padicRowFourier_of_isRowFourierPair` identifies the wrapped p-adic row integral
with any recorded Fourier partner. Its proof uses the defining equality of
`Langlands.HarmonicAnalysis.IsRowFourierPair` in the reverse direction.
`padicRowFourier_testData` specializes this to `EqualLocalTestData`: the local
integral of `D.Φ` at a row is exactly `D.Φhat` at that row, by `D.isFourierPair`.
Both lemmas use the canonical topology and its Borel measurable space. Neither
chooses a new measure or assumes a new Fourier identity.

`finiteRowTest F n v` abbreviates the existing Schwartz–Bruhat test space on the
local row space with the canonical p-adic topology. The adelic tensor API instead
uses the native topology of the completion `FiniteCompletion F v`.
`completion_row_topology_eq` lifts the published
`CompletionPadic.completion_topology_eq` through the finite function-space
constructor. `finiteRowTest_locallyConstant` and
`finiteRowTest_hasCompactSupport` transport the two test-function properties
along this equality. The underlying functions are unchanged.

`extendFiniteRowTests` extends a family of tests indexed by the subtype of a
finite place set `S` to a family of functions at all finite places. At `v ∈ S` it
uses the supplied test, and otherwise it is zero. The external indicator in the
restricted tensor separately supplies the integral condition outside `S`.
`extendFiniteRowTests_apply` proves the restriction back to `S` is the original
family, and `extendFiniteRowTests_test` proves local constancy and compact support
at every place in `S` for the native completion topology.

## Conditional assembly result

Assume the published `RectangleTateStatement`. As in the tensor Fourier formula,
let `F` be a number field with compact adelic quotient and `ψ` a unitary additive
character trivial on `F`. Let `S` satisfy `FiniteAdditiveSupport ψ S`. Supply its
real and complex additive scales with their component equalities, canonical
finite components `ψv`, and measures `νv` self-dual for these components.

For any natural number `n`, supply archimedean Schwartz functions `ΦR`, `ΦC` and
two finite families `f`, `g`, each indexed by `S`, in `finiteRowTest F n v`.
Require `IsRowFourierPair (ψv v) (νv v) (f v) (g v)` at every place in `S`. Then
there exists an actual function `Φ : RowVector F n → ℂ` such that:

- `Φ` belongs to `schwartzBruhat F n` and is standard outside `S`;
- `Φ` is exactly the `integralOutside F n S` indicator times the product of the
  given real, complex and finite functions at the corresponding coordinates;
- its defined global Fourier transform is exactly the same indicator times the
  product of the specified real and complex self-dual Fourier transforms and
  the finite functions `g v` at the corresponding coordinates.

Both function equalities have scalar one. The statement permits empty real,
complex and finite indexing sets and `n = 0`. In particular `n = r + 1` includes
the `r = 0` equal-rank case. No test function is required to be nonzero here.

The implemented witness is the previously defined `restrictedTensor`, using
`extendFiniteRowTests f`. Its Schwartz–Bruhat membership follows from
`extendFiniteRowTests_test` and `restrictedTensor_mem_schwartzBruhat`, and its
standardness and ordinary formula follow from the published assembly results.
For the Fourier formula, `restrictedTensorFourierReduction` supplies the product
of local row integrals conditional on the rectangular measure comparison. The
recorded local Fourier-pair equalities replace those integrals by `g v`.

## Scope

This proves the test-function assembly step under the explicit measure
premise `RectangleTateStatement`, which the Library proves in `RectangleTateProof`. It does not construct Whittaker functions or compatible quotient
measures, prove a pointwise global Whittaker product, or establish any of the
nonvanishing clauses. Those obligations in `EqualPointwiseFactorizationStatement`
and the unconditional proof of `ArchimedeanFactorizationStatement` remain open. The result adds
no convergence assertion beyond the definitions and its explicit premises.
