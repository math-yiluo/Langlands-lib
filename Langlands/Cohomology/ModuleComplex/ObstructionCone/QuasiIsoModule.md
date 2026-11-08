# Bounded flat quasi-isomorphisms after tensoring with a module

Module `Langlands.Cohomology.ModuleComplex.ObstructionCone.QuasiIsoModule`, namespace of the
same name. This is an internal helper for
`Langlands.Cohomology.ModuleComplex.ObstructionCone.openStatement`.

The published `Langlands.Cohomology.ModuleComplex.boundedFlatQuasiIsoBaseChange` keeps a
bounded quasi-isomorphism of complexes of flat modules a quasi-isomorphism after base change
to any commutative `A`-algebra. This module derives the same conclusion for `- ⊗[A] N` with
`N` an arbitrary `A`-module, in positive degrees.

## Construction

- `opModule N` is the right action of `Aᵐᵒᵖ` on `N` through `RingEquiv.toOpposite`, and
  `opCentral N` records that the two actions agree. Both are local instances only. They
  supply the hypotheses of Mathlib's commutative ring structure on the trivial square-zero
  extension.
- `Ext A N` abbreviates `TrivSqZeroExt A N`, the ring `A ⊕ N` with `N² = 0`. It is an
  `A`-algebra.
- `incl N X : X ⊗[A] N → Ext A N ⊗[A] X` is `TensorProduct.comm` after
  `TrivSqZeroExt.inrHom ⊗ X`. `retr N X : Ext A N ⊗[A] X → X ⊗[A] N` is
  `TrivSqZeroExt.sndHom ⊗ X` after `TensorProduct.comm`.
- `retr_incl` says `retr ∘ incl = id`. `baseChange_incl` and `retr_baseChange` say both maps
  commute with `f.baseChange (Ext A N)` and `f.rTensor N` for every linear `f : X → Y`.
  All three are proved on pure tensors with `TensorProduct.inductionOn`.

## Main theorem

`rTensor_quasiIso` takes exactly the hypotheses of `BoundedFlatQuasiIsoBaseChangeStatement`:
- bounded complexes `(K, δ)` and `(C, d)` of flat modules indexed by `ℕ`;
- a chain map `φ` that is injective and surjective on cohomology in the elementwise form used
  there.

It then proves, for every `A`-module `N` and every `i`:
- if `x ∈ K (i+1) ⊗ N` is a cycle and `φ x` is a boundary, then `x` is a boundary;
- every cycle `y ∈ C (i+1) ⊗ N` is `φ x` up to a boundary, for some cycle `x`.

Proof: apply `boundedFlatQuasiIsoBaseChange` with the algebra `Ext A N`, push elements in
with `incl`, and pull the resulting witnesses back with `retr`, using the three identities
above.

## Provenance

Internal. The retract `N → A ⊕ N → N` is a standard device; no external source is used.
