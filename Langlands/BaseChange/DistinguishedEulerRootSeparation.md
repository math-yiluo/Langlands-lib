# Separated standard Euler factors at a distinguished completion

Let `E/F` be a finite extension of nonarchimedean local fields with `F` of
characteristic zero and with the `F`-module topology on `E`. Fix an
`F`-algebra automorphism `σ` of `E`. A smooth determinant character invariant
under every power of `σ` twists the full normalized `σ`-orbit product
into the full normalized orbit product of the twisted first block. The
equivalence with the orbit product uses the supplied rank reindexing. The
first block remains irreducible and supercuspidal, so
`orbitStandardFactorSeparation` gives separation of the forward and reflected
dual standard Euler roots of the twisted representation.

A bicontinuous field isomorphism to a finite completion, with its canonical
p-adic topology, takes this separation to the standard factors of the actual
finite component in rank at least two. The supplied `FinitePairFactorChoice`
uses actual irreducible admissible finite components of the cuspidal
presentation and its contragredient presentation. The second representation
is the rank-one constant presentation. The proof pulls back the additive
character and its self-dual measure from this factor choice. The transported
JPSS certificates give both polynomials at the completion because inverse
transpose commutes with the field map and the additive character scaled
by minus one also pulls back. The standard polynomial comparison uses the
contragredient condition to identify the dual component with the smooth
dual and identifies the two certificates with the chosen polynomials. The
isomorphism preserves the residue cardinality and therefore the reflection
`x ↦ q⁻¹ / x`.

`DistinguishedEulerRootSeparationOfUnramifiedOrbitStatement` combines the
two steps when the actual finite component is an unramified determinant
twist of the transported orbit product. An unramified character factors
through the normalized order. Its pullback is smooth and invariant under
the local Galois action because both the completion isomorphism and the
automorphisms of the original field preserve that order.

This is the upper local factor step in the completed-equation approach to
Arthur–Clozel, Chapter 1, Proposition 6.9(ii), printed pp. 69–70 (PDF
pp. 83–84), literature ID `arthur-clozel-1989-base-change`, SHA-256
`c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
