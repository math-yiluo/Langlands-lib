# Regular cochains with quasi-coherent module coefficients

Let `R` be a commutative ring, `H` an actual group scheme over `Spec R`, and `M` an arbitrary `R`-module in the fixed universe. `ModulePoints M A` is `A ⊗[R] M` for an affine test algebra `A`. `modulePointMap` extends coefficients along an algebra homomorphism; the module proves its formula on pure tensors and its identity and composition laws. No finite generation, freeness, projectivity or smoothness hypothesis is imposed on `M` or `H`.

`ModuleRepresentation M H` consists of an action of `H(A)` by `A`-linear automorphisms of `A ⊗[R] M` on every affine test algebra, natural under all algebra homomorphisms. `OneCochain M H` and `TwoCochain M H` are families of maps from one or two actual `H(A)`-points to `A ⊗[R] M`, again natural in `A`. Thus these are regular cochains on the affine-point functor, not arbitrary abstract group cochains at a fixed ring.

For such an action `ρ`, the one-cocycle equation is

`c(hk) = c(h) + ρ(h)c(k)`.

Its coboundary predicate requires an element `m ∈ M` with

`c(h) = ρ(h)(1 ⊗ m) − 1 ⊗ m`

on every affine test. The two-cocycle equation is

`c(h,k) + c(hk,l) = ρ(h)c(k,l) + c(h,kl)`.

Its coboundary predicate requires a natural one-cochain `b` with

`c(h,k) + b(hk) = ρ(h)b(k) + b(h)`.

These equations use the inhomogeneous differential convention of Conrad, *Reductive group schemes* (2014), Appendix B.2, p.284. No normalization at the identity is required. A zero-cochain is represented by an actual base-module element; its value over `A` is the tensor `1 ⊗ m`.

`HasVanishingLowDegreeCohomology H` says that every regular one- and two-cocycle with every such quasi-coherent module action is a coboundary. It is a proposition definition only. This module neither proves its vanishing for multiplicative-type groups nor constructs a derived-functor cohomology group or proves a comparison theorem with it.

Provenance: this is a derived affine-test interface for the functorial cochains and linear quasi-coherent actions in Conrad, Appendix B.2, pp.283–284. Over an affine base the quasi-coherent module attached to `M` has the stated tensor-product values on affine tests. The implementation uses the Library's actual `GroupScheme.affinePoints` and coefficient-extension maps, together with Mathlib tensor-product linear maps. It introduces no additional vanishing assertion from the literature.
