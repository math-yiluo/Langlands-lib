# Local finite dimensionality of arbitrary field coalgebras

`Langlands.Subcoalgebra.LocalFinitenessStatement.{u,v}` is the following
Prop-valued definition, with independent universes `u` and `v`:

```lean
∀ (k : Type u) [Field k] (C : Type v) [AddCommGroup C] [Module k C]
  [Coalgebra k C] (c : C),
  ∃ D : Langlands.Subcoalgebra k C, c ∈ D ∧ FiniteDimensional k D
```

Thus every element of every coalgebra over any field belongs to a
finite-dimensional subcoalgebra. This is the fundamental theorem of coalgebras.
The ambient coalgebra can have arbitrary dimension, including dimension zero.
There is no cocommutativity, algebra or Hopf structure, nonzero-carrier,
characteristic, perfectness, splitting, or local-finiteness hypothesis, and the
universes of the field and coalgebra need not agree.

The statement imports the published bundled interface
`Langlands.RingTheory.Coalgebra.Subcoalgebra.Basic`. Its witness
`D : Langlands.Subcoalgebra k C` is a submodule closed under ambient
comultiplication into its tensor square. The expression `FiniteDimensional k D`
uses Mathlib's actual finite-dimensionality class on the actual subtype carrier,
with the additive group and module instances supplied by `Basic`. That module
also constructs the carrier coalgebra and the inclusion coalgebra homomorphism
from closure. This statement introduces no replacement subcoalgebra bundle or
additional carrier certificate.

The source correspondence is derived from J. S. Milne, *Algebraic Groups*
(2017), registered as `milne-2017-algebraic-groups`, content SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
Proposition 4.7, printed p.86 (one-based PDF page 102), is stated for
`O(G)`-comodules. Its proof expands a coaction in a vector-space basis of the
coalgebra and uses coassociativity to obtain a finite-dimensional subcomodule
containing a chosen element. The argument uses only the coalgebra and comodule
axioms, so it applies to an arbitrary counital coassociative field coalgebra,
without the algebra or group structure of `O(G)`.

Section 9.d, printed pp.174–175 (one-based PDF pages 190–191), defines general
coalgebras and comodules and describes their coefficient subcoalgebras. To
derive the present statement, give `C` its regular right comodule structure
with coaction `Δ : C → C ⊗ C`. The preceding argument yields a
finite-dimensional subcomodule `V ⊆ C` containing `c`. For a finite basis
`v₁,…,vₙ` of `V`, write
`Δ(vⱼ) = ∑ᵢ vᵢ ⊗ cᵢⱼ`. Coassociativity gives
`Δ(cᵢⱼ) = ∑ₗ cᵢₗ ⊗ cₗⱼ`, so the span of the finitely many coefficients is a
finite-dimensional subcoalgebra `C_V`. Applying the ambient counit to the first
tensor factor gives `vⱼ = ∑ᵢ ε(vᵢ)cᵢⱼ`; consequently `V ⊆ C_V` and `c ∈ C_V`.
The restricted counit and tensor-square closure agree with the imported bundle.

The proof of Theorem 12.18, printed pp.237–238 (one-based PDF pages 253–254),
uses these coefficient subcoalgebras to express `O(G)` as their union. That
coordinate-coalgebra application alone is not the unrestricted statement above;
the regular-comodule derivation explains the general scope here. The registered
official errata snapshot `milne-2017-algebraic-groups-errata-2026-11-02` has no
correction to Proposition 4.7, these passages of §9.d, or Theorem 12.18.

This module states the proposition. The mathematical derivation explains its
provenance; it is not a Lean proof of `LocalFinitenessStatement`. Proving that
exact proposition is a separate proof task.
