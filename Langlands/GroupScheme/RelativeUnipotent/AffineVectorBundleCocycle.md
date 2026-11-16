# Affine cocycles in vector-bundle groups

Let `S` be an affine scheme in an arbitrary universe `u`, let `M` be a quasi-coherent sheaf of modules on `S`, and let `U → S` be an affine, flat, surjective morphism. The module of global sections of `M` need not be free, projective, finite or flat.

`SectionCocycle M U` is a natural additive cocycle on all test schemes over `S`. For every pair of morphisms `a,b : Z → U`, its value is a global section of the pullback of `M` to `Z`. Naturality uses the canonical `RelativeUnipotent.sectionPullback`, including its comparison isomorphisms for composition of sheaf pullback. The cocycle identity is `α(a,c) = α(a,b) + α(b,c)`.

`SectionCocycle.exists_coboundary` constructs a single section `β` of the pullback of `M` to `U` such that, on every test scheme `Z`,

`α(a,b) = sectionPullback M a β - sectionPullback M b β`.

The tests `Z` in this conclusion need not be affine. Neither the base nor the cover is assumed noetherian, local, connected, or of finite presentation.

`cocycle_isTrivial` specializes this result to an actual group scheme `V` satisfying `IsVectorBundleAdditive V`. Given its natural all-test group identifications with the additive sections of one finite locally free sheaf, any `Cocycle V U` is trivial in the published `Cocycle.IsTrivial` sense: there is one group point `f : U → V` for which `ξ(a,b) = (a ≫ f) * (b ≫ f)⁻¹` on every test scheme. Local basis data give a locally free, hence quasi-coherent, sheaf. The sizes of the local bases may vary with the base; no global choice of rank or basis is made. The affineness and smoothness conditions included in `IsVectorBundleAdditive` are retained in that hypothesis, although the proof only uses its sheaf and natural coordinates.

## Implemented proof

Write `A = Γ(S, ⊤)`, `B = Γ(U, ⊤)` and `N = GlobalSections M`. On a spectrum `Spec C → S`, the published `AffineSectionCoordinates.equiv` identifies pullback sections with `Γ(Spec C, ⊤) ⊗[A] N`. `specOver_appTop` verifies the compatibility of the actual structural map with `Scheme.ΓSpecIso`. Using this identity, `algebraCoordinates` converts the preceding tensor product to `C ⊗[A] N` with the supplied algebra structure on `C`. Its naturality follows from the naturality of `ΓSpecIso` and tensor induction.

`algebraFun` evaluates a section cocycle on the spectrum points induced by two algebra maps from `B`. The canonical section-coordinate naturality and the spectrum map comparisons prove its naturality. Additivity of both coordinate equivalences gives its cocycle law. These facts define `SectionCocycle.algebraCocycle`, an instance of the `AffineModuleCocycle.Cocycle` interface.

Affineness, flatness and surjectivity imply that `B` is faithfully flat over `A`. `AffineModuleCocycle.Cocycle.exists_coboundary`, derived from arbitrary-module Amitsur degree-one exactness, therefore supplies one element of `B ⊗[A] N`. Its inverse spectrum coordinates, restricted along `U → Spec Γ(U, ⊤)` and then mapped by `toSection`, define `β`.

For any test scheme `Z`, first use the algebraic primitive on `Γ(Z, ⊤)`. Applying the affine section coordinates gives the desired equality on `Spec Γ(Z, ⊤)`. Pulling back along `Z → Spec Γ(Z, ⊤)` gives the equality on `Z`. The naturality of `toSpecΓ` and `tensorPullback_comp` identify the two terms with the restrictions of the same section `β`. Inverse tensor coordinates are used only on affine schemes.

Finally, apply the supplied group-coordinate equivalences to a group-valued cocycle. Multiplication and inverse become addition and negation of sections. The section primitive maps back to the required group point by the inverse coordinate equivalence over `U`.

## Provenance and scope

This is internal derived content. Its inputs are the published canonical affine section comparison, the arbitrary-module algebraic cocycle theorem, Mathlib's spectrum/global-function adjunction, and the locally free implies quasi-coherent instance. The formulas above explain the constructions and proof; no additional geometric vanishing principle is assumed.

The result supplies vector-bundle cocycle vanishing for the relative unipotent route. It does not construct a vector-bundle filtration, prove vanishing for every group with such a filtration, identify the torsor of Levi subgroups, or prove `RelativeLeviAffineExistenceStatement`.
