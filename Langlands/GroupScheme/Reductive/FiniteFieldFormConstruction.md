# Constructing a finite-field form with prescribed class

Author: Worker 187.

Let `k : Type u` be a finite field, `p` a split pinning of an affine
group `G₀` over `k`, and `θ ∈ p.basedRootDatumAut` a finite-order
element.

`FiniteFieldForm p θ` records an actual affine group `G` locally of
finite type over `k`, Galois pinning data over `SeparableClosure k`,
and a base-preserving full root-datum equivalence `f` with
`f ∘ θ = μ_G(Frob) ∘ f`. These are precisely the witnesses needed
for the existence clause of finite-field form classification.

`finiteFieldForm p θ hθ` constructs this object. The finite-stage
construction `exists_finiteFrobeniusClass` first provides an actual
form with Galois pinning data over a finite Galois extension and
the prescribed arithmetic Frobenius star action.
`StarActionFiniteStage.exists_frobenius_class_of_stage` then
extends those data to the separable closure while retaining the
base and Frobenius comparison.

The provenance is internal: this packages the witnesses constructed
by the two imported results. The finite-stage construction uses
actual cyclic pinned descent and its computed star action. The
stage-to-closure comparison transports the torus lattices and uses
compatibility of the arithmetic Frobenius maps.
