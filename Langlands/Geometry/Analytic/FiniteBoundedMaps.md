# Automatic bounded maps from finite Banach algebras

Author: Worker 36.

This derived construction reuses the published theorem
`FiniteBanachAlgebra.exists_norm_bound` by Worker 56.
Let `f : A → B` and `g : A → C` be actual bounded maps of normed commutative
`K`-algebras. Assume `K` is nontrivially normed, `A` and `B` are complete,
and the exact ring map underlying `f` is module-finite. No completeness of
`K` or `C` is required.

`BoundedAlgHom.ofFiniteTriangle` constructs a bounded map from every algebraic
`K`-algebra map `h : B → C` satisfying `h ∘ f = g`. The underlying map remains
`h`, and the bounded base triangle is proved. `finiteTriangleEquiv` gives the
actual equivalence between the compatible algebraic maps and compatible
bounded maps, with both inverse identities.

If `C` is complete and `e : B ≃ₐ[K] C` satisfies the same base triangle,
`BoundedAlgEquiv.ofFiniteTriangle` constructs bounds in both directions.
Module finiteness of the map `A → C` is derived from that of `A → B` and
surjectivity of `e`; it is not an additional hypothesis. The inverse base
triangle follows from the original triangle and the inverse identities.
Applying the bounded-map construction to both triangles gives the actual
bounded equivalence with underlying algebraic equivalence `e`. The existing
`toHomeomorph` and `spectrumHomeomorph` then give homeomorphisms of the norm
topologies and of the actual bounded multiplicative spectra. The spectrum
evaluation lemma verifies that the latter sends a seminorm `x` to
`b ↦ x (e b)`, so its direction is contravariant.

The proof installs the algebra structures induced by `f` and `g`, together
with their compatible scalar towers. The triangle equation makes `h` an
`A`-algebra map. The published finite Banach theorem proves a global norm
bound from continuity of the two bounded base maps; its nonnegative bound
is enlarged to a positive bound for `BoundedAlgHom`. Thus continuity and
boundedness of `h` are constructed, rather than supplied as an assumption.

The motivating source is Berkovich, *Non-archimedean analytic spaces*
(Trieste lectures, 2009), Definition 2.1.1 and the following Banach openness
paragraph on printed/PDF p. 7. That paragraph explains why surjective bounded
maps between Banach spaces over a nontrivially valued field are admissible.
The implemented finite Banach continuity theorem uses that open mapping
argument on the actual finite coefficient map. The present triangle
construction is a derived consequence, rather than a verbatim statement of
Definition 2.1.1.

Registered source: `berkovich-2009-trieste-analytic-spaces`, retained PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.

This local construction does not establish rational base-change finiteness,
analytic finiteness on all affinoid domains, or an analytic site.
