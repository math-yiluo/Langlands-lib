# Extending stable images by unramified twists

Author: Worker 4803. Module `Langlands.Correspondence.HenniartExtension`,
namespace `Langlands.Henniart.Extension`.

Henniart (2000), §4.4, printed p. 453 (PDF p. 15): for an irreducible `σ`,
choose an unramified `χ` such that `σ (χ ∘ rec)⁻¹` has determinant of finite
order. Put `π(σ) = π(σ (χ ∘ rec)⁻¹) χ`. By Théorème 4.2 b) this does not depend
on the choice of `χ`. This module implements that definition on the actual basis
of continuous irreducible Weil classes of a p-adic field `K`. The universes are
`uK` (field), `uW` (Weil carriers), `uV` (supercuspidal carriers) and `uE`
(local constants of the stable images), all independent.

## Stable decompositions

`IsStableDecomposition K b z b₀ π₀` means that the twist of the unitary class
`b₀` by `Weil.Local.localUnramifiedCharacter K z` is `b`, and that the generator
of the unitary supercuspidal class `π₀` is a stable image of `b₀`.
`IsStableDecomposition.eq_twist_inv` rewrites the first condition in the form
`b₀ = weilUnramifiedTwist K z⁻¹ b` used by the published
`UnramifiedTwistIndependenceStatement`.

`exists_stableDecomposition`: assume `StableCorrespondenceStatement` (stable
images in every rank). Every class `b` has a stable decomposition. The published
`LocalWeil.unramifiedTwistFiniteFactoring` writes `b` as a twist of a unitary
class `b₀` factoring through a finite quotient. `StableExistsAt` in the rank of
`b₀` gives a stable image. `IsStableImage.exists_generator` shows that it is a
generator.

## The extended map

`extensionBasis K hSC b` is the published unramified twist
`PadicSupercuspidal.unramifiedTwistBasisEquiv K z π₀.val` for a chosen stable
decomposition. `extensionBasis_spec` records the choice.

`extensionBasis_eq`: with `UnramifiedTwistIndependenceStatement`, the value is
the same for every stable decomposition. For two decompositions `(z₁, b₁, π₁)`
and `(z, b₀, π₀)`, the independence statement gives equality of the two twisted
lattice elements. Including unitary generators and twisting generators gives
generators, and `Finsupp.single_left_injective` identifies the basis classes.

`extensionBasis_rank`: the extension preserves rank, since twisting, stable
images and the reduction all preserve rank.

`rankCast` reads a basis class of rank `n` in the class space of rank `n`.
`extensionMap K hSC : SupercuspidalMap K` is the extension in each rank.
`sigma_extensionMap` identifies the pair `⟨n, extensionMap n σ⟩` with
`extensionBasis ⟨n, σ⟩`.

`extensionMap_agrees`: on a unitary class `σ` factoring through a finite
quotient, the extension is the stable image. Take the decomposition with `z = 1`
and `b₀ = σ`, and use `extensionBasis_eq`. This is the agreement clause of the
published `HenniartConstructionStatement`.
