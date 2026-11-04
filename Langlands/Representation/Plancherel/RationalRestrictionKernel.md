# The actual split-center restriction kernel

Author: Worker 200.

This derived construction compares the actual restriction maps with the
published abstract-subgroup restriction kernel. It contributes to
J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)* (2003), I.1, printed p.239 (PDF p.5), source ID
`waldspurger-2003-plancherel`, SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
That passage states finite kernel for restriction of unitary unramified
characters from \(G\) to \(A_G\). The present unit proves the kernel comparison
and deduces finiteness under an explicit finite-index premise about the
actual central valuation image.

The finite quotient used here is the quotient step of Renard,
*Représentations des groupes réductifs p-adiques*, 9 July 2026 edition,
V.2.6, printed p.108 (PDF p.114), source ID
`renard-2026-representations-groupes-reductifs-padiques`, SHA-256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The preceding actual-image finite-index assertion remains a separate proof
obligation. No representation-theoretic or analytic conclusion is assumed.

## Actual pointwise comparison

Let \(F:\mathrm{Type}\ u\) have `Field`, `ValuativeRel`,
`TopologicalSpace` and `IsNonarchimedeanLocalField`. The objects \(G,H\) are
the shared actual affine `GroupScheme (Spec (CommRingCat.of F))`.
Each rational-point group has exactly its canonical
`rationalPointTopology F _.X`. Write
\[
 \nu_G(\psi)=\operatorname{rationalNormCharacters}(G,\psi),\qquad
 N_G=\operatorname{rationalCommonNormKernel}(G).
\]
Here the positive character family is understood using `.toMul` as in the
published definitions. The groups \(X(G)\) and \(\operatorname{Im}X(G)\)
are the existing continuous unramified and unitary unramified character
subgroups for this actual family, with their compact-open subspace topologies.

For any actual morphism \(f:H\to G\),
`mem_rationalUnramifiedCharacterRestrict_ker` proves
\[
 \chi\in\ker(X(G)\to X(H))
 \quad\Longleftrightarrow\quad
 \forall h\in H(F),\ \chi(f(F)(h))=1.
\]
`mem_rationalUnitaryUnramifiedCharacterRestrict_ker` gives the same criterion
for the unitary restriction. Both proofs evaluate an equality with the
trivial character in one direction, and use subtype and continuous-character
extensionality in the other.

`rationalUnramifiedCharacterRestrict_ker` identifies the complex kernel,
as a subgroup of the existing \(X(G)\), with
`centralTrivialUnramifiedCharacters ν_G (rationalPoints.map f).range`.
The latter is the published subgroup of characters trivial on every element
of the specified point subgroup. A range witness converts one pointwise
condition into the other; evaluating at the canonical range element gives
the converse. This comparison does not require centrality, injectivity,
finite type, reductivity, or any finite quotient.

## Conditional finite kernel and norm one

Let \(T\) be an affine commutative group scheme and \(s:T\to G\) an actual
morphism with `hs : GroupScheme.IsCentral s`. Set \(A=s(T(F))\), the actual
point-map range. The remaining explicit premise is
`hindex : (RenardCartan.splitValuationImage s).FiniteIndex`.
The subgroup in this premise is the published range of the composite
\[
 T(F)\longrightarrow G(F)
 \longrightarrow \operatorname{rationalCharacterValuationImage}(G).
\]
It is neither a chosen lattice nor an asserted rational-point lift.

`hs.range_le_center` makes \(A\) normal. The imported conditional theorem
`finite_rationalCentralQuotient s hs hindex` makes
\(G(F)/(N_G\vee A)\) finite; \(N_G\) is definitionally the common kernel
used in the generic restriction-kernel results.

`finite_rationalUnramifiedCharacterRestrict_ker` rewrites the actual kernel
by the proved subgroup equality and applies
`finite_centralTrivialUnramifiedCharacters`.
The latter injects characters into the character group of the finite quotient,
which is finite.
`rationalUnramifiedCharacterRestrict_ker_norm_eq_one` uses the same equality
and finite quotient to apply
`centralTrivialUnramifiedCharacter_norm_eq_one`.
Every value of a descended character has finite order, hence complex norm one.
Thus every character in the complex restriction kernel is already unitary.

`rationalUnramifiedRestrictKernelEquivUnitary` constructs the multiplicative
equivalence from the complex restriction kernel to the unitary restriction
kernel. Its forward map supplies the proved norm-one property; its inverse
forgets that property. The pointwise kernel criteria prove membership in
both directions. Both maps retain the same continuous character. Subtype
extensionality proves the inverse and multiplication laws, and the `_apply`
theorem gives equality of their values at every \(g\in G(F)\).
`finite_rationalUnitaryUnramifiedCharacterRestrict_ker` transfers the
proved finiteness of the complex kernel through this equivalence.

## Scope

The field universe is arbitrary, with no characteristic restriction. The
construction requires no connectedness, reductivity, finite type or torus
structure. Its intended application takes \(T=A_G\) and the actual split-center
inclusion, but finite index of that actual valuation image remains explicit.
The unit supplies no proof of that premise, surjectivity or character extension,
topological or manifold structure on the kernel, Haar normalization,
stabilizer or orbit-family finiteness, spectral finiteness or Plancherel identity.

Local instances use explicit module-specific names to prevent generated-name
collisions under joint imports. Their types, bodies and local scope are
unchanged.
