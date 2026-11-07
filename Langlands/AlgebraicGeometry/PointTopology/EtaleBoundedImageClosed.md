# Étale maps are closed on locally bounded sets of rational points

Author: Worker 105.

This module translates the algebraic clustering theorem of `AffineEtaleBoundedCluster` into
a statement about rational points of affine schemes. It serves the total disconnectedness
part of Proposition 5.4 of Brian Conrad, *Weil and Grothendieck approaches to adelic
points* (December 31, 2011), printed p.15 (source
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`).

- `isClosed_image_of_locallyBounded`: let `K` be a henselian ultrametric valued field and
  `p : W → V` a morphism of affine `K`-schemes with `Etale p.left`. Rational points carry
  the Library's affine point topology (`affineSchemePointHomeomorph`, global-section
  evaluation). Let `S ⊆ W(K)` be closed, and assume `S` is locally bounded over `V`: every
  `v ∈ V(K)` has a neighbourhood `N` such that every global function of `W` is bounded on
  the points of `S` lying over `N`. Then the image `p(S)` is closed in `V(K)`.

  Proof. Let `v` be in the closure of `p(S)`. The filter `comap p (𝓝 v) ⊓ 𝓟 S` is
  nontrivial. Its image in the `K`-points of `Γ(W)` is bounded on every element. Its
  restrictions along `Γ(p)` converge to the point `v` of `Γ(V)`, by the naturality
  `affineSchemePointEquiv_natural`. `Γ(p)` is étale: Mathlib's
  `HasRingHomProperty.iff_of_isAffine` applied to `Etale`. So
  `EtaleBoundedCluster.exists_tendsto_of_bounded` produces a limit point `φ₀` restricting
  to `v`. It lies in the image of `S` because `S` is closed. Its scheme point `w₀` lies in
  `S` and maps to `v`.
