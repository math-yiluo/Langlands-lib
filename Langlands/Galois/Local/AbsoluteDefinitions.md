# The absolute residue action of a supplied local-field realization

Author: Worker 9.

For a characteristic-zero nonarchimedean local field \(K\), this file constructs
an actual homomorphism
\[
 \rho_K:\operatorname{Gal}(\operatorname{AlgebraicClosure}K/K)
 \longrightarrow
 \operatorname{Gal}(\operatorname{AlgebraicClosure}k/k),
 \qquad k=\mathcal O_K/\mathfrak m_K.
\]
The field \(k\) is the residue field of the supplied `ValuativeRel K`, with its
usual algebraic structure. Both groups have Mathlib's existing Krull topology.
No residue homomorphism, closure property, lifting theorem, continuity certificate
or surjectivity certificate is accepted as input data.

## Norm and valuation choices

`localRankOne` chooses an ordered embedding of the supplied rank-one value group
into the nonnegative reals. `localNormedField` uses Mathlib's valued-field norm
construction with the original additive uniformity. Its construction lemmas
certify completeness, the ultrametric inequality, the unchanged topology, and
equality of its unit ball with the original integer ring. This norm need not have
a specified numerical normalization. Its order relation is the supplied
valuation relation.

`localClosureValuation` is the spectral extension of that norm to the actual field
`AlgebraicClosure K`. The extension instance is proved for the original
`ValuativeRel.valuation K`, so it extends the supplied valuation up to the natural
equivalence of value groups. `closureIntegers` is its valuation subring and
`localIntegerMap` embeds the original integer ring into it. The construction
never assumes the algebraic closure is complete or locally compact.

## Residue closure and its base field

Write \(A\) for the norm's unit ball, \(B\) for `closureIntegers`, and \(k_B\) for
the residue field of \(B\). Equality of \(A\) with the supplied integer ring
induces `localResidueEquiv`, a ring equivalence \(k_A\simeq k\).
The imported spectral proof establishes that \(k_B/k_A\) is an algebraic closure.
`localResidueClosureEquiv` then uses Mathlib's `IsAlgClosure.equivOfEquiv` to choose
a ring equivalence
\[
 e:k_B\simeq\operatorname{AlgebraicClosure}k
\]
compatible with this base-field equivalence.

`standardResidueAlgebra` transports the base algebra along \(k_A\simeq k\).
`localResidueClosureAlgEquiv` is the same \(e\) as a \(k\)-algebra equivalence.
The proof contribution explicitly verifies algebraic-closure status for this
algebra and compatibility with reduction of elements of the original integer
ring. No canonical choice of \(e\) independent of closure presentations is claimed.

## Automorphisms, inertia and finite levels

`semilinearAutCongr` conjugates actual field automorphisms through compatible
equivalences of base fields and extension fields.
`localResidueTransport` applies it to \(k_A\simeq k\) and \(e\).
`absoluteResidueHom` composes this conjugation with the constructed spectral
residue homomorphism:
\[
 \rho_K(\sigma)(e(\bar x))=e(\overline{\sigma x})\quad(x\in B).
\]
`absoluteInertia` is the spectral inertia subgroup, with its ordinary inherited
subgroup topology. The proof target requires its equality with the kernel of
this transported map and with field-theoretic inertia.

For every intermediate field \(E\subseteq\operatorname{AlgebraicClosure}K\),
`integerInclusion` uses equality of spectral norms in a tower to embed its
integer ring into \(B\). A proved local-hom instance permits reduction to the
residue-field embedding `residueInclusion`. Restriction compatibility is a
separate proof target; in particular it covers all finite Galois levels.

The namespace `Langlands.PadicField` provides `residueField`, `closureIntegers`,
`absoluteResidueHom`, and `absoluteInertia` for every `F : PadicField p` and every
explicit `T : F.TopologicalData`. Each definition installs the instances supplied
by that particular \(T\). No new `TopologicalData` constructor is assumed.

## Sources, dependencies and scope

The original source is Serre, *Local Fields*, English 1979:
Chapter II, §2, Proposition 3 and Corollaries 2–3, pp. 28–29 (PDF 36–37);
Chapter I, §7, Propositions 20–22 and the inertia definition, pp. 20–23
(PDF 28–31); and Chapter III, §5, Theorems 2–3 and Corollaries 1–3, pp. 54–55
(PDF 61–62). These pages were read in the original retained file
`C:/Central-Library/Serre--Local Fields--1979.pdf`.
Registered source: `serre-1979-local-fields`, SHA-256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

This is a derived formal construction, making all closure and valuation choices
explicit. Its project dependencies are:

- `Langlands.Galois.Local.SpectralProof`, artifact
  `de8e50b8-25a2-4fca-a86d-6060f5f92d9e`, version 1. This proof is independently
  accepted and published at commit
  `843c574c920aa9926ab56adf662c74b3cd4ed0e1`, integration
  `a66b589278454a6e80ce8c23373b1280`. It supplies
  `residueExtension_isAlgClosure` and the other proved spectral interfaces
  used here. Its effective Lean SHA-256 is
  `0ec2c48c4e49e166a62db849a3f5a2f5b65dac72a9f23e28984d2a3a880e3c14`.
- That proof's exact proposition is `SpectralResidueExactness`, statement
  `c9ec9a6a-5b72-444a-bfb0-7c5406d5950d`, version 1, with checked target
  `94c3c18f724e4ee46b15aa630d07da23acf68bfe8fde21c9cebf23b1e9422c89`.
  Its definitions are `SpectralDefinitions`, artifact
  `82bd181d-11b1-4000-afb6-1acdb762dd32`, version 1.
- `Langlands.LocalField.Definitions`, artifact
  `ac4cb7d5-5dd1-44b6-9d56-f0ec6c70bce0`, version 1, supplies `PadicField`
  and the explicit `TopologicalData` interface.

All these dependencies were verified accepted, published, currently available,
and byte-identical to the imported files before submission. The environment is
`2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1: Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. The imported proof retains
Worker 9's original mathematics and Worker 38's submission attribution.

This definition pair does not by itself prove the residue exact sequence.
`AbsoluteStatement` specifies all arithmetic, topology and compatibility
conclusions for separate proof acceptance. The output here is a
homomorphism to the actual residue absolute Galois group. An identification of
that group by finite-field Frobenius, and a local Weil-group construction, are
separate downstream work.
