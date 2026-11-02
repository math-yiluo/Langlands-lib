# Effective flat descent of actual groupoid coactions

This internal construction supplies the actual descent equivalence and
degree-one vanishing for an effective ring relation. It is derived from the
published tensor-coordinate, invariant-counit, and Amitsur constructions,
together with Mathlib's preservation of kernels and injections under flat
tensor extension. No geometric affine-descent conclusion is used.

Let `B` and `C` be commutative rings in an arbitrary universe `u`, with the
specified source algebra structure `B → C`, target map `t : B →+* C`, and
`hE : RingEtaleEquivalenceRelation t`. Write `A = invariantRing t`, the
actual equalizer of the source and target maps. Let `M : Type (max u v)`
be a `B`-module with an actual `GroupoidCoaction t M`, denoted `θ`. The
independent universe `v` permits coefficient modules larger than the rings.

Assume a `B`-algebra equivalence `e : C ≃ₐ[B] B ⊗[A] B` satisfying
`e (t b) = 1 ⊗ b`. The first factor on the right carries the specified
`B`-algebra structure. The canonical map

`ε = invariantCounit θ : B ⊗[A] θ.invariantSubmodule →ₗ[B] M`

sends `b ⊗ m` to `b • m`. The invariant module has its canonical
`A`-module structure.

The preliminary `presentationTensorEquiv_target_smul` works over any
compatible base ring `A`. Inverse tensor coordinates send `d ⊗ m` to
`t(d) ⊗ m`; induction on these coordinates shows that multiplication by
`t(b)` becomes multiplication by `b` on the first tensor factor.
Consequently the coordinate coaction `δ = presentationCoaction θ e ht`
satisfies `δ(bm) = b δ(m)`, using the original coaction's target
semilinearity. Applying this formula to invariant elements gives

`δ (ε x) = (B ⊗ inclusion) x`.

This identity does not require flatness.

For `invariantCounit_bijective_of_flat_presentation`, assume only
`Module.Flat A B`. Put `η(m) = 1 ⊗ m` and `d = δ - η`. The published
fixed-element comparison identifies the kernel of `d` with the invariant
submodule, so the sequence

`θ.invariantSubmodule → M → B ⊗[A] M`

with maps inclusion and `d` is exact. Flat tensor extension preserves
this exactness and the injectivity of the inclusion. If `ε x = ε y`,
the displayed identity gives `(B ⊗ inclusion) x = (B ⊗ inclusion) y`;
tensor injectivity yields `x = y`. For surjectivity, the published
coordinate coassociativity says `(B ⊗ d)(δ m) = 0`. Tensor exactness
therefore supplies `x` with `(B ⊗ inclusion) x = δ m`. The identity
above and the published injectivity of `δ`, which uses the relation's
identity point, imply `ε x = m`.

`flatPresentationInvariantEquiv` is the resulting `B`-linear equivalence,
constructed by `LinearEquiv.ofBijective`. Its forward map is exactly `ε`,
as the application lemma records.

The general helper `IsHom.linearEquiv_symm` proves that the inverse of an
equivariant linear equivalence is equivariant: apply the injective tensor
extension of the forward equivalence, rewrite forward equivariance, and
cancel the two inverse maps.

For `oneCohomologyVanishes_of_faithfullyFlat_presentation`, strengthen
flatness to `Module.FaithfullyFlat A B`. The published counit
equivariance makes `flatPresentationInvariantEquiv` an equivalence from
the induced coaction on `B ⊗[A] θ.invariantSubmodule` to `θ`. Its inverse
is equivariant by the preceding helper. The published faithfully flat
Amitsur theorem proves degree-one vanishing for that induced coaction,
and the published retract theorem transports it to `θ`.

Finally, `isAcyclic_of_faithfullyFlat_presentation` applies the published
implication from degree-one vanishing to the invariant-lifting predicate
`θ.IsAcyclic`. The required source flatness of `C` over `B` follows from
`hE.etale_algebraMap`.

The scope is conditional on the effective presentation and faithful
flatness over the actual invariant ring. This construction assumes no
module finiteness, Noetherianity, or acyclicity. It does not prove the
main finite-cover acyclicity theorem; producing suitable covering
modules and the support induction remains separate work.
