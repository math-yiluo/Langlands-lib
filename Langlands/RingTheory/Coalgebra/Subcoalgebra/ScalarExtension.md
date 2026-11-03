# Scalar extension of field subcoalgebras

Worker 16 constructs this interface using the carrier coalgebra of
`Langlands.RingTheory.Coalgebra.Subcoalgebra.Basic`, authored by Worker 321.
The range-closure argument adapts the argument in the registered Apache-2.0
TauCeti source `tauceti-subcoalgebra-basic-map-8428d621`, file
`TauCeti/Algebra/Coalgebra/Subcoalgebra/Map.lean`, declaration
`TauCeti.Subcoalgebra.map`, at commit
`8428d6217f74afa72531df0bc85d7b57ab72810f`. The carrier coalgebra maps,
equivalences and scalar extension here are new derived constructions.

The mathematical convention is Milne, *Algebraic Groups* (2017), printed
pp. 236–238, especially the definition of a finite-dimensional subcoalgebra
in the proof of Theorem 12.18 on p. 237 (PDF pages 252–254). The registered
source is `milne-2017-algebraic-groups`, content SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The official errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02` has no correction to this
passage. These constructions implement the usual subspace condition
Δ(D) ⊆ D ⊗ D. Scalar extension and its structural laws are derived here;
the source does not state this bundled API.

All universes are arbitrary and independent. Let `k : Type u` be a field.
Let `C : Type v` and `E : Type w` have additive commutative groups,
`k`-module structures and actual Mathlib `Coalgebra k` structures.
No cocommutativity or finite-dimensionality is assumed.

For every coalgebra homomorphism `f : C →ₗc[k] E`,
`Langlands.Subcoalgebra.range f` has underlying submodule
`LinearMap.range f.toLinearMap`. Membership is existence of a preimage.
Its closure proof sends Δ(c) through the tensor square of the linear map
from `C` to this range, then uses the compatibility of `f` with
comultiplication. Thus the carrier coalgebra is obtained from closure by
the construction in `Basic`; it is not supplied as extra data.

For a subcoalgebra `D` of `E` containing every `f c`, `codRestrict D f h`
is a coalgebra homomorphism to its carrier, with underlying function
`c ↦ ⟨f c, h c⟩`. Its counit equality follows by restriction. Its
comultiplication equality is checked after the injective tensor square
of the inclusion of `D` into `E`; flatness over the field makes this
test injective. `subtype_comp_codRestrict` identifies its composite
with inclusion with `f`. Specializing gives the surjective
`rangeRestrict f`; if `f` is injective, `equivRange f hf` is a coalgebra
equivalence from `C` to `range f`.

Now let `K : Type x` be any field with an `Algebra k K` structure.
There is no algebraicity, separability, finiteness or universe restriction
on `K/k`. For any `D : Langlands.Subcoalgebra k C`:

- `baseChangeMap K D : K ⊗[k] D →ₗc[K] K ⊗[k] C` is Mathlib's
  tensor product of the identity coalgebra map on `K` and the inclusion
  `D.subtype`. Its underlying `K`-linear map is exactly
  `D.toSubmodule.subtype.baseChange K`, and it sends `a ⊗ d` to
  `a ⊗ (d : C)`. It is injective because tensoring an injective
  `k`-linear map with the flat `k`-module `K` preserves injectivity.
- `baseChange K D` is the range subcoalgebra of that map in the
  actual Mathlib tensor-product coalgebra on `K ⊗[k] C`. Its underlying
  submodule is exactly `D.toSubmodule.baseChange K`. Membership means
  being the image of some tensor in `K ⊗[k] D`, and every pure tensor
  `a ⊗ c` with `c ∈ D` belongs.
- `toBaseChange K D` is the canonical coalgebra map to this image
  carrier. It is bijective and compatible with its inclusion into
  `K ⊗[k] C`.
- `baseChangeEquiv K D : K ⊗[k] D ≃ₗc[K] baseChange K D` is the
  resulting coalgebra equivalence; its homomorphism is `toBaseChange`.
  The application and pure-tensor lemmas identify its composite with
  inclusion with `baseChangeMap K D`.
- Scalar extension preserves the zero and whole subcoalgebras and
  is monotone for inclusion.
- If the carrier `D` is finite dimensional over `k`, the instance
  `instFiniteDimensionalBaseChange` makes the carrier of `baseChange K D`
  finite dimensional over `K`. This follows from Mathlib's
  `Module.Finite.base_change` and surjectivity of `toBaseChange`.
  The argument includes `D = ⊥`.

Every displayed coalgebra map preserves both counit and comultiplication
as part of its Mathlib type. The finite-dimensional instance imposes
no finite-dimensionality on the ambient coalgebra `C`.
This file makes no assertion that finite-dimensional subcoalgebras cover
`C` and proves no descent, dual base change, or group-like spanning result.
