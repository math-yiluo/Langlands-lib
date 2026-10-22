# Exactness and topology of spectral residue reduction

Author: Worker 9.

`Langlands.LocalGalois.SpectralResidueExactness` is a proposition definition,
universally quantified over two independent field universes. Its fields \(K,L\)
have these hypotheses: \(K\) is a complete nontrivially normed ultrametric field,
\(L/K\) is Galois in Mathlib's algebraic sense, and the residue field of
\(A=\texttt{baseIntegers K}\) is finite. There is no finite-degree assumption on
\(L/K\), nor any topology or completeness hypothesis on \(L\).

Let \(B=\texttt{extensionIntegers K L}\), let \(k_A,k_B\) be their residue fields,
and let \(\rho=\texttt{residueHom K L}\) and \(I=\texttt{inertia K L}\).
These are the explicitly constructed valuation ring, residue action and kernel
from `SpectralDefinitions`, not extra input data. The proposition states:

1. An element of \(L\) lies in \(B\) exactly when it is integral over \(A\).
2. If \(L\) is algebraically closed, \(k_B\) is an algebraic closure of \(k_A\)
   with the already constructed residue-field algebra structure.
3. For every automorphism \(\sigma\) and every \(x\in B\),
   \(\rho(\sigma)(\overline{x})=\overline{\sigma x}\).
4. \(\rho:\operatorname{Gal}(L/K)\to\operatorname{Gal}(k_B/k_A)\) is continuous,
   surjective and open for the existing Krull topologies.
5. Membership in \(I\) is equivalent to fixing the residues of every element of
   \(B\). This subgroup equals the inverse image of Mathlib's
   `ValuationSubring.inertiaSubgroup` under `decompositionHom`.
6. \(I\) is normal and closed. Its inherited subgroup topology is compact and
   totally disconnected. Hausdorffness and the topological-group structure are
   the existing subtype instances, so this is the inherited profinite topology.
7. There exists a topological group equivalence
   \(\operatorname{Gal}(L/K)/I\simeq\operatorname{Gal}(k_B/k_A)\), using the
   quotient topology, that sends the class of each \(\sigma\) to
   \(\rho(\sigma)\).

The last representative identity is part of the target: the claimed equivalence
must be induced by this particular residue homomorphism. No surjective map,
residue closure, quotient equivalence or inertia identification is a hypothesis.
This file defines the target and contains no proof of it.

## Provenance and scope

This is a derived infinite-extension formulation of the residue exact sequence.
The original source is Jean-Pierre Serre, *Local Fields*, English translation
by Marvin Jay Greenberg, Springer GTM 67, 1979:

- Chapter I, §7, Proposition 20 and the inertia definition, printed pp. 20–22
  (PDF pages 28–30): reduction of field automorphisms, surjectivity in the finite
  normal setting, and inertia as the kernel.
- Chapter II, §2, Proposition 3 and Corollaries 2–3, printed pp. 28–29
  (PDF pages 36–37): extension of the valuation from a complete base and
  conjugacy invariance.
- Chapter III, §5, Theorems 2–3 and Corollaries 1–3, printed pp. 54–55
  (PDF pages 61–62): finite residue lifting and the maximal unramified extension's
  relation to the residue Galois group.

The source is registered as `serre-1979-local-fields`, retained at
`C:/Central-Library/Serre--Local Fields--1979.pdf`, with SHA-256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
Those pages were read in the original. Serre's cited finite discrete-valuation
results are not asserted to have the full formal target's generality.
The arbitrary algebraic-extension construction uses Mathlib's proved spectral
norm; the infinite surjectivity and topology conclusions require additional
arguments with the Krull topology.

In the planned proof, a residue conjugate is lifted to a conjugate root of an
integral polynomial. Primitive elements of finite residue extensions turn this
into density, and compactness of the Galois group turns density into surjectivity.
This route supplies the lifting needed for exactness without a separate
formalization of the classification of all unramified extensions.

The exact project definition dependency is the accepted and published
`SpectralDefinitions` artifact `82bd181d-11b1-4000-afb6-1acdb762dd32` version 1.
Its publication commit is `9db46907db3181b0c1dfd287b8ab2f1f02054cab`;
the integrated Lean and Markdown files have SHA-256
`7b05ea4f6904f852d6870c3c323a42939d98c8e03bfc08fb7aa37a58d46e8d9a` and
`ff8291f7b724341fb7e2c9fd358cea67aeed1fc9710bbefcdc17aa69fa0f997f`.
Both files match the dependency used here, and current Library membership was
verified before submission. The remaining dependencies are in environment
`2ecc41bc-2901-4e34-96c5-6d98fbb3c74d` version 1 (Lean 4.34.0; Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`).

The full local task additionally requires specialization to each supplied
`PadicField.TopologicalData`, comparison with its residue field, closure
transport, and finite-level compatibility. This generic exactness statement
does not claim that those specialization steps are already complete.
