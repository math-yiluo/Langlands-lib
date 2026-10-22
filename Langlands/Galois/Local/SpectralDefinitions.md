# Residue reduction for an algebraic extension of a complete valued field

Author: Worker 9.

This file constructs the residue action from field automorphisms. Let \(K\) be a
complete, nontrivially normed ultrametric field, and let \(L/K\) be an algebraic
field extension. Neither a residue homomorphism nor its surjectivity is supplied
as data. No topology, completeness, or local compactness assumption is placed on
\(L\).

The namespace is `Langlands.LocalGalois`. The two field universes are independent.
The constructions are noncomputable because Mathlib's spectral norm is
noncomputable.

## The valuation rings

`spectralValuation K L` is the multiplicative valuation with values in
\(\mathbb R_{\geq 0}\) whose value at \(x\) is `spectralNorm K L x`.
Mathlib proves that this function is multiplicative and nonarchimedean and
restricts to the original absolute value of \(K\). The instance
`spectralValuation_extends` records that restriction as `Valuation.HasExtension`.
Thus

\[
 A=\texttt{baseIntegers K}=\{a\in K:\lVert a\rVert\leq 1\},\qquad
 B=\texttt{extensionIntegers K L}=\{b\in L:\lVert b\rVert_{\rm sp}\leq 1\}
\]

are actual valuation subrings. The existing extension API supplies the local
ring map \(A\to B\), and hence the residue-field algebra
\(k_A\to k_B\), where \(k_A=A/\mathfrak m_A\) and \(k_B=B/\mathfrak m_B\).
The identification of \(B\) with the integral closure of \(A\) is a separate
proposition target, not an assumption of these definitions.

## The homomorphism and inertia

For \(\sigma\in\operatorname{Aut}_K(L)\), `integerAut K L σ` restricts \(\sigma\)
to an \(A\)-algebra automorphism of \(B\). Its well-definedness uses Mathlib's
proved invariance of the spectral norm under \(K\)-algebra equivalences.
`ResidueField.mapAlgEquiv'` then induces the \(k_A\)-algebra automorphism of \(k_B\).
These induced automorphisms form the explicitly constructed homomorphism

\[
 \texttt{residueHom K L}:
 \operatorname{Aut}_K(L)\longrightarrow\operatorname{Aut}_{k_A}(k_B),
 \qquad
 \overline b\longmapsto\overline{\sigma b}.
\]

Its group laws are checked on residue representatives. `inertia K L` is its
kernel, with the normal-subgroup instance supplied by the kernel construction.
`decompositionHom K L` regards every \(K\)-automorphism as an element of Mathlib's
`ValuationSubring.decompositionSubgroup`: every such automorphism stabilizes
\(B\). This gives a comparison map for the separate proposition identifying this
kernel with Mathlib's valuation-subring inertia.

The Galois groups use Mathlib's existing Krull topologies. Inertia uses the
ordinary subgroup topology inherited from the source Galois group. There is no
new topology on either group in this file. Continuity, surjectivity, closedness,
openness, and the topological quotient equivalence are separate proposition and
proof contributions. In particular, this definition artifact alone does not
establish an exact sequence.

## Sources and correspondence

The source is Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay
Greenberg, Graduate Texts in Mathematics 67, Springer, 1979:

- Chapter II, §2, Proposition 3 and Corollaries 2–3, printed pp. 28–29
  (PDF pages 36–37), for extension of the absolute value from a complete field
  and invariance under conjugacy.
- Chapter I, §7, Proposition 20 and the definition of the inertia group,
  printed pp. 20–22 (PDF pages 28–30), for the induced residue action and its
  kernel.

Registered source: `serre-1979-local-fields`.
Retained file: `C:/Central-Library/Serre--Local Fields--1979.pdf`.
SHA-256: `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
The cited pages were read in the retained original.

This is a derived formulation: Serre's finite-extension definitions are expressed
using Mathlib's spectral norm on an arbitrary algebraic extension. The formula
for residue action is unchanged; the infinite-extension exactness and topology
require additional proofs. In particular, the current definitions do not claim
that an arbitrary abstract group is an absolute Galois group.

## Dependencies and specialization boundary

The Lean file imports only the pinned Mathlib environment (Lean 4.34.0, Mathlib
commit `5ed2965256430c3649e86755f9576b54eca72435`). It has no project definition
dependencies and introduces no axioms.

For the local absolute-Galois application, a later construction must realize the
supplied local-field valuation by a compatible norm, choose an actual algebraic
closure \(L\), identify \(k_B\) as an algebraic closure of \(k_A\), and transport
its automorphism group to a chosen closure if that presentation is desired.
Those requirements, as well as finite-level compatibility and the exactness
proofs, remain part of the local residue-sequence task. No finite-field Frobenius
identification or local Weil-group identification is asserted here.
