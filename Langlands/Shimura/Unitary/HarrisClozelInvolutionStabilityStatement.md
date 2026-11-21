# Stability of the Harris division transfer under Clozel's involution

This module states Clozel's Corollary 3.4 for the division group of
`Langlands.Shimura.HarrisClozel.HarrisClozelGlobalJLStatement`.

## Definitions

`divisionAdelicInvolution D` is the automorphism `x ↦ σ(x)⁻¹` of the actual
adelic points of the unit group `divisionGroup` of `A` over its CM center `E`.
Here `σ` is the second-kind involution of the datum `D`. It is `E₀`-linear but
semilinear over `E`, so it is applied after the actual comparison
`Adeles E₀ ⊗[E₀] A ≃ Adeles E ⊗[E] A`. That comparison is built from the
balanced tensor identities and `numberFieldAdeleTensorEquiv`. The map is
`id ⊗ σ` on `Adeles E₀ ⊗[E₀] A`, that is `s ⊗ a ↦ s ⊗ σ(a)`
(`AlgebraInvolution.baseChange`), composed with inversion in the unit group
(`inverseUnits`).
Because `σ` is an anti-automorphism, this composite is a group automorphism.
It sends the factor at a place `w` of `E` to the factor at the conjugate place.

`IsInvolutionStable D π` asks for an isometric linear equivalence intertwining
the pullback `π ∘ θ` with `π` on the same space. It does not ask `θ` to fix any
chosen vector.

`IsFiniteConstituent π v X τ` says that `τ` is an irreducible admissible
representation of the actual local points at `v`. It also asks for an injective
intertwining map from `τ` into the restriction of `π` along
`AdelicGroupPoints.ofPlace`.

## Statement

`HarrisClozelInvolutionStabilityStatement` concerns the actual data of the
global transfer:

- a CM field `E` over its totally real subfield `E₀`;
- a datum `D` of degree `r+1` whose algebra is a division algebra;
- a cuspidal realization `S` of `GL_(r+1)` over `E` whose isomorphism class is
  conjugate self-dual, with a spectral presentation `P` whose local components
  are irreducible and admissible at every finite place;
- a closed irreducible summand `T` of the canonical positive split-center
  quotient `L²` of the unit group of `A`.

Suppose that outside a finite set of finite places, `T` has a finite constituent
identified with the source component `P.localComponent p` by an actual matrix
chart (`IsSplitLocalTransfer`). Then `T` is isometrically stable under
`divisionAdelicInvolution D`.

The global transfer statement supplies this hypothesis for its own `T`: there
the two division places are the only exceptions. Any chart may be used, since
two charts differ by an inner automorphism (Skolem–Noether).

## Source and expected proof

The argument is Clozel 1991, *Représentations galoisiennes associées aux
représentations automorphes autoduales de GL(n)*, §3.1, Corollary 3.4, p. 108.
Clozel works with the algebra of Proposition 2.3, ramified at two or four
places (pp. 106–107), and with the target `τ_c` of the all-place transfer of
Theorem 3.3(i). He applies the uniqueness of Theorem 3.3(ii) relative to that
transfer. The present proposition extends this argument. It allows any CM
division datum and any closed irreducible summand `T` whose components match
the source at almost all finite places. The multiplicity-one input in this
generality is Badulescu 2008, *Global Jacquet–Langlands correspondence,
multiplicity one and classification of automorphic representations*,
Theorem 5.1(b)–(c), p. 413 (LaTeX source lines 1960–1980). It gives
multiplicity one and strong multiplicity one for the discrete series of
`GL_n(D)` over a global field of characteristic zero, when `D` is split at all
infinite places (§4, pp. 408–409; LaTeX source lines 1636–1650). Over the CM center `E` every infinite
place is complex, so this hypothesis holds.

Expected proof. In a matrix chart, `θ` is, up to an inner automorphism, the
composite of the Galois action of `E/E₀` with `g ↦ ᵗg⁻¹`. It sends the factor at
`p` to the factor at the conjugate place. The contragredient of an irreducible
admissible representation of `GL_n` is its composite with `g ↦ ᵗg⁻¹`
(Gelfand–Kazhdan), and the source is conjugate self-dual. Hence at every `p`
with `p` and its conjugate outside the finite exceptional set, the component of
`T ∘ θ` at `p` is the source component at `p`, which is the component of `T`.

The operator `U`, with `(Uφ)(x) = φ(θ x)`, is unitary on the quotient `L²`: `θ`
is an involution preserving the rational points, the Haar measure and the
positive diagonal split center (inverting each of its elements). `U` maps `T`
onto a closed irreducible summand `U(T)` isometrically equivalent to `T ∘ θ`.
Strong multiplicity one shows that `U(T)` and `T` have the same components
everywhere. Multiplicity one in the discrete spectrum then gives `U(T) = T`. In
the quotient by the positive diagonal this follows from the statement for each
central character, since the remaining center is compact.

## Boundary

This is a statement only. It does not prove multiplicity one or strong
multiplicity one for the division group, the Gelfand–Kazhdan identity or the
local conjugate-duality transport, which are the inputs of the expected proof. It does not assert stable
descent to the unitary group. The arithmetic fields and representation carriers
are in `Type 0`, as in the global transfer statement.
