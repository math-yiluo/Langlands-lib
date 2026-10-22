# Canonical realization compatibility target

`Langlands.PadicField.CanonicalCompatibilityStatement` is a proposition
definition for arbitrary `p : Nat` with `[Fact p.Prime]` and arbitrary carrier
universe `u`. Its main quantifier ranges over every `F : PadicField.{u} p`.
It uses the actual `F.canonicalTopologicalData` constructor; no realization,
existence assertion, normality, Galois, ramification, or degree restriction is
an additional hypothesis.

Write `T = F.canonicalTopologicalData`. The first conjunct states all of the
following for each `F`:

1. `T.topology = F.canonicalTopology`, where the right side is the accepted
   finite-dimensional module topology.
2. `T.topology` is also the topology of the explicit
   `F.canonicalNormedField`.
3. For every `x`, the real coercion of `F.canonicalValuation x` equals
   `F.canonicalNorm x`.
4. With `T.valuativeRel` installed, that numerical valuation has Mathlib's
   `Valuation.Compatible` certificate.
5. For every `x,y`, the selected comparison `x ≤ᵥ y` holds exactly when
   `F.canonicalNorm x ≤ F.canonicalNorm y`.
6. For every `a : Padic p`, the norm of `algebraMap (Padic p) F.Carrier a`
   is the usual p-adic norm of `a`.
7. The norm of the integer `p` in the carrier is `(p : Real)⁻¹`.
8. For every `a,b : Padic p`, comparison of their images in the selected
   valuative relation is equivalent to
   `Padic.mulValuation a ≤ Padic.mulValuation b`.
9. With the explicit canonical normed field installed, its uniform space
   is complete and its metric space is proper.
10. With `T.topology` and `T.valuativeRel` installed, the carrier is locally
    compact, its Mathlib valuation integer ring is compact and a discrete
    valuation ring, the valuative relation is discrete, and its residue
    field is finite.

The remaining two conjuncts concern `rational p`, the accepted degree-one
example whose carrier is `Padic p`. They assert equality of the topology of
its canonical realization with `(rationalTopologicalData p).topology`, and
equivalence of their valuative comparisons for every pair of elements.
They compare the mathematical topology and relation, not the full instance
packages.

## Instance selection and scope

The statement names the topology and relation explicitly. Its complete/proper
clause uses `letI := F.canonicalNormedField`, fixing the uniform and metric
structures as well as the topology. Its local-field clause separately installs
the selected topology and relation. Thus its compactness and finiteness claims
refer to the integer and residue rings associated with that same relation.
The statement does not install global instances.

The notation `𝒪[F.Carrier]` and `𝓀[F.Carrier]` is Mathlib's existing valuation
integer ring and residue field, enabled by `open scoped ValuativeRel`.
`ValuativeRel.IsDiscrete` describes the value group of the relation. It does
not assert discreteness of the ambient `NNReal` codomain. These conclusions
reuse the existing nonarchimedean local-field interfaces; the statement adds
no alternative ring or residue-field construction.

The numerical normalization is the norm extending the usual norm on
`Padic p`. In particular `|p| = p⁻¹`. Serre's normalized absolute value,
which assigns `q⁻¹` to a uniformizer for residue cardinality `q`, is a
different numerical convention in general. No conversion formula,
ramification-degree formula, field-norm formula, or integral-closure
identification is part of this target.

## Sources and correspondence

This is a derived compatibility interface for the explicit construction.
Its conjunction packaging and the class-valued conclusions are internal
formalization choices.

- Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur
  un corps p-adique* (2000), Section 1.1, printed page 439, first two
  sentences (PDF page 1), fixes an arbitrary prime and an arbitrary finite
  extension of `Q_p`. The target retains exactly this scope.
  Source `henniart-2000-simple-proof`, SHA256
  `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`,
  file
  `C:/Central-Library/Henniart--Une preuve simple des conjectures de Langlands pour GL(n) sur un corps p-adique--2000.pdf`.
- Serre, *Local Fields*, 1979 English translation, Chapter II Section 1,
  printed pages 26-28, gives the valuation topology and local compactness
  criterion, including Proposition 1 and the `Q_p` example. The normalization
  preceding Proposition 2 uses the residue cardinality. Section 2,
  Proposition 3 and Corollary 2, printed pages 28-29, identifies the
  finite-extension topology with the finite-dimensional product topology
  and gives completeness and uniqueness of prolongation; page 30 discusses
  absolute values. These are PDF pages 34-38.
  Source `serre-1979-local-fields`, SHA256
  `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`,
  file `C:/Central-Library/Serre--Local Fields--1979.pdf`.

Worker 26 read these original passages and checked both source hashes.
The norm and relation clauses record the chosen Mathlib implementation of
prolongation, including zero arguments in all comparisons. The topology
clauses identify its topology with the canonical module topology. Completeness,
properness, discreteness, integer-ring compactness, and finite residue field
are existing Mathlib consequences for the selected structures. The rational
clauses express compatibility with the existing base example.

## Dependencies and status

The sole direct import is `Langlands.LocalField.Canonical`. The constructor
is accepted definition artifact `c342ec21-e5ee-4ba4-aec6-b4c1b1e2b629`,
version 1, published at commit
`9db46907db3181b0c1dfd287b8ab2f1f02054cab` with independent receipt
`24df660d770545809d3f2ad0d607c9bb` and effective snapshot
`bdbf7a14a6a5d5800958d1d758d3a90273f129253b41a85d6bca034255b7abb9`.
Its accepted Lean and Markdown hashes are respectively
`e702bb7808fc344bda47a3093d9438d5cda71dcb165be7110be7b393f61d7c48`
and `94a7a93a2ac19a6c106542cd76530caf8244892f29b98eea8755b031ec7e872d`.

Its underlying interface is accepted definition
`ac4cb7d5-5dd1-44b6-9d56-f0ec6c70bce0`, version 1,
`Langlands.LocalField.Definitions`, publication commit
`1fe07fd211e579cc430734fd96ce959aadb7663d`, independent receipt
`203bba66-269f-46f4-984c-71531a4963c2`, and effective snapshot
`7dd12688f9e4cc615cd460940f0a82295c62729f3d59bb86304e3627c6831512`.
The accepted Lean and Markdown hashes are respectively
`8d9cc8aa128861b13b4f96d38bf95be46844d2eaad28aa3cbb654b070ee0e517`
and `6cfb939cf42a71a81fa648b77bd4bab1076bffe0d62519181f7dc7db742124bf`.
Both exact versions were freshly verified as accepted, published, and current,
with no missing or changed files or unavailable dependencies. The local pairs
match these effective published hashes.

Environment `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1, pins
Lean 4.34.0 at `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b` and Mathlib
at `5ed2965256430c3649e86755f9576b54eca72435`.

Worker 26 authored this proposition and its Markdown. The proposition and a
complete proof compile without errors or warnings in the pinned native
environment. Development diagnostic
`9f2f1577-2ae5-4c0e-956f-b5a1446b310f` compiled the three dependency-first
modules with no warnings or errors and confirmed that the declaration returns
`Prop`, with universe parameter `u` and checked target fingerprint
`31cf58218ce1e184e0f1463a4413ee1703b7ae569e191bc4a046c0896b001df8`.
The checked Lean sources and accepted dependency bytes are unchanged.

This is development evidence, not proof acceptance. The target requires its
own independent semantic review and publication. A proof contribution must
then be bound to this target's exact accepted version and pass registered
independent proof checking and independent semantic review before publication.
