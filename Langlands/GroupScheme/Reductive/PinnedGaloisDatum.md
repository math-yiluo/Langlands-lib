# Actual finite Galois descent from a supplied pinning

This is an internal specialization of the actual finite-component descent
constructor and the coherent semilinear pinned lifts. Let `k` and `K` be fields
in an arbitrary universe `u`, with a supplied `k`-algebra structure on `K`.
Let `G` be an actual affine group scheme over `Spec K`, let `p` be a supplied
complete split pinning of `G`, and let
`ρ : (K ≃ₐ[k] K) →* p.basedRootDatumAut` be a supplied homomorphism. Its target
is the based automorphism group of the full integral root datum of `p`.

`SplitPinning.galoisSemilinearIso` is the ambient group-scheme isomorphism
`σ*G ≅ G` obtained from the semilinear pinned lift of the ring equivalence
underlying `σ` and the based automorphism `ρ σ`. This definition and its
composition laws require no finiteness or Galois hypothesis.

`galoisSemilinearIso_mul` proves the actual tower law. Here
`galoisBaseMap σ = Spec.map σ.toRingHom`; it does not use the inverse
automorphism. Multiplication `σ * τ` applies `τ` first and then `σ`.
Consequently `τ.toRingEquiv.trans σ.toRingEquiv` equals the ring equivalence
underlying `σ * τ`, and the actual scheme base maps satisfy
`b σ ≫ b τ = b (σ * τ)`. Through the canonical actual pullback comparison,
the lift for `σ * τ` is the `b σ` pullback of the lift for `τ`, followed by
the lift for `σ`. The proof specializes the complete pinned composition
theorem with the ring equivalences in the order `τ, σ` and the based
automorphisms in the order `ρ τ, ρ σ`, then uses the homomorphism law of `ρ`.
A private helper transports the ring-equivalence equality while keeping the
dependent comparison witness as an explicit argument.

Now suppose `K/k` is finite dimensional and Galois. The finite component
index type is `Fin (Module.finrank k K)`. `Descent.finiteGaloisIndexMul`
transports multiplication through the existing equivalence
`galoisIndexEquiv` from this small type to the Galois group.
`galoisIndexEquiv_mul` and `finiteGaloisBaseMap_comp` record the resulting
index and actual scheme-map formulas. The equality-parametrized
`galoisSemilinearIso_mul_of_eq` and its finite-index specialization express
the same tower law with a supplied product index.

`SplitPinning.galoisDatum` constructs a genuine
`Descent.Datum (fieldMap k K) G`. It uses the actual finite-Galois overlap
components `finiteGaloisComponent`: their first projection is the identity
of `Spec K`, their second projection is the appropriate `galoisBaseMap`,
and their coproduct is isomorphic to the actual double overlap. Applying
`SemilinearComponents.datumOfSemilinear` to these components and the proved
tower law assembles the actual overlap isomorphism and proves its cocycle
on the actual triple overlap.

`pullIso_galoisDatum` gives exact recovery on each component. The recovered
map is `baseChangeIdIso G` followed by the inverse of the corresponding
`galoisSemilinearIso`. This is the orientation of the descent datum from the
first-projection pullback to the second-projection pullback.

The provenance is the internal derivation just described from the imported
pinning and finite-component constructions. This unit assumes the finite
Galois extension, complete split pinning, and based action. It does not
construct those inputs or a preserved-Borel descent datum, effective
descent solution, adjoint quotient, or inner discrepancy cocycle. In
particular, it is a supporting construction for the unconditional
quasi-split inner-form existence target, which remains a separate proof
obligation.
