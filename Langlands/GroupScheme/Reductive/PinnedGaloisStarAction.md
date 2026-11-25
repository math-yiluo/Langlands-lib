# The star action of an actual pinned Galois twist

For any `GaloisTorusSolution p ρ` over a finite Galois extension `K/k`,
this module computes the star action on the actual descended Galois
pinning data. The comparison is the actual base-preserving root
equivalence `s.rootEquiv`.

`torusSolution` retains the torus part of the effective solution,
including compatibility with its prescribed Čech datum.
`torusIso_semilinear` uses the exact finite overlap components to
identify the semilinear transport of the descended torus with the
torus part of the prescribed pinned semilinear isomorphism.

`galoisRepresentation_rootEquiv` computes the action on every
character: canonical descent transport of the pullback along the
torus comparison equals that pullback applied after the supplied
based action. It follows by cancelling the semilinear comparison
isomorphisms and applying `semilinearPinnedIso_character`.
`galoisAction_eq_conjAut` extends this equality to the full root datum,
using determination of root-datum equivalences by their weight maps.

The transported action preserves the base, so the Weyl correction
in the star action is trivial. `starAction_intertwine` concludes
`s.rootEquiv ∘ ρ(σ) = μ_s(σ) ∘ s.rootEquiv` for every `σ ∈ Gal(K/k)`.

The provenance is internal: this computes the action on the actual
effective torus and group constructed in the imported modules. No
finite field or prescribed Frobenius value is assumed or constructed.
