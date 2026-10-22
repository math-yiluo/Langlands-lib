# Compactness of the actual absolute Galois group

Author: Worker 160.

`Langlands.GaloisRepresentation.AbsoluteGaloisGroupCompactness` is the
proposition that, for every field `K : Type u` in an arbitrary universe,
`Field.absoluteGaloisGroup K` is a compact space in its existing topology.
Mathlib defines this group as the `K`-algebra automorphisms of
`AlgebraicClosure K`, with the Krull topology. The statement uses precisely that
group and topology, without constructing a replacement or assuming a
topological equivalence to another model.

There is no perfect-field, characteristic-zero, or local-field assumption.
In particular, over an imperfect field the full algebraic closure need not be
separable. One cannot discharge this statement merely by applying Mathlib's
compactness instance for `Gal(L/K)` under the hypothesis `IsGalois K L`.

## Source and derived formulation

Serre, *Local Fields* (1979), Chapter X, Section 3, printed page 154
(PDF page 160), describes the Galois group of an infinite Galois extension
as a compact totally disconnected group obtained as the inverse limit of its
finite Galois groups. Registered source: `serre-1979-local-fields`, SHA-256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

The present assertion extracts compactness and expresses it for Mathlib's
full-algebraic-closure model. This is a derived formulation: for imperfect
fields the cited Galois-extension statement does not apply directly to the
full closure. A proof must justify compactness in this model, for example by
proving the topological comparison with the separable-closure automorphism
group or by a direct compactness argument using finite sets of conjugates.
No such comparison or proof is supplied in this statement module.

The statement is a topology prerequisite for applying compact-group
continuous-cohomology results to the closure-choice comparison over arbitrary
fields. It proves neither compactness nor a cohomology or local invariant
theorem. It does not assert additional topological properties.
