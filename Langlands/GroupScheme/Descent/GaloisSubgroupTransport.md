# Composition and Frobenius invariance of subgroup descent transport

Author: Worker 1442.

This internal construction supplies the canonical Galois action on subgroup
functors of a group obtained by base change. It also proves that, for finite
fields, invariance under Frobenius suffices for invariance under every Galois
automorphism. All subgroup equalities are tested on every relative test scheme.
No representability or closedness assumption is needed for the action.

For schemes `b : S ⟶ B`, `a : S ⟶ S` with `a ≫ b = b`, and a group scheme `G`
over `B`, the previously defined `descentTransport b a ha G F` first pulls back
the subgroup functor `F` and then transports it through the canonical ambient
descent isomorphism. The membership comparison
`mem_descentTransport_iff_descentPoint` identifies this membership condition with
membership of the published `descentPoint` in `F` over the changed test scheme.
It follows from the natural point comparisons of canonical pullback.

`descentTransport_id` and `descentTransport_comp` prove the identity and
composition laws. Their proofs use the published `descentPoint_id` and
`descentPoint_comp`, then use stability under precomposition by a test-scheme
isomorphism in both directions. The composition convention is
`transport a (transport c F) = transport (a ≫ c) F`.
`descentTransport_comp_of_eq` gives the same law when the composite base map
is specified by an equality; proof irrelevance accounts for the certificates
that the maps lie over `B`.

For arbitrary fields `k,L : Type u` with a `k`-algebra structure on `L`,
`galoisTransport k L G` is an actual monoid homomorphism

```text
(L ≃ₐ[k] L) →* Function.End (SubgroupFunctor G_L).
```

It sends an automorphism to transport along its `Spec` map. The identity law
and the product law follow from the preceding transport laws and the published
identities `galoisBaseMap_one` and `galoisBaseMap_mul`. There is no finiteness,
Galois-extension, smoothness, or affineness premise on this construction.

`galoisTransport_pow_eq_self` proves by induction that a subgroup functor
fixed by one automorphism is fixed by every nonnegative power of it.
For `[Fintype k]` and `[Finite L]`,
`galoisTransport_eq_self_of_frobenius` applies Mathlib's
`FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow`: every `k`-automorphism
of `L` is a power of its `#k`-power Frobenius. Thus Frobenius invariance implies
invariance under every such automorphism.

`descentTransport_range` identifies the transport of a represented subgroup
with the range of the base-changed inclusion composed with the canonical
ambient isomorphism. It combines `range_baseChangeHom` with the published
`range_comp_iso`. Consequently,
`galois_range_eq_of_frobenius_range_eq` expresses the finite-field conclusion
directly as equalities of ranges of actual group-scheme homomorphisms. This is
the form required by finite Galois closed-subgroup descent; the bridge itself
does not require that the homomorphism be a monomorphism.

The provenance is internal: the construction combines the Library's subgroup
pullback and preimage operations, its point and base-map comparisons in
`Torus.LatticeGalois`, and Mathlib's finite-field automorphism theorem. The use
of `Rational.SplitUnipotentTransport` is solely for its general
`SubgroupFunctor.range_comp_iso` lemma. No unipotence premise or conclusion
enters these statements.

This module does not construct a Frobenius-invariant torus, supply a finite
model of a torus over an algebraic closure, or prove finite-field geometric
maximal-torus existence. Its finite-field conclusions require the stated
Frobenius invariance over a finite extension. In particular, the powers
argument is not asserted for arbitrary subgroup functors over an infinite
algebraic closure.
