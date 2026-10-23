# Relative derivations on fibre products

This helper module proves that a relative derivation on a fibre product of
schemes is zero once it kills the sections pulled back along both
projections. The proof of additivity of the relative Lie differential in
[LieAdditivityProof.md](../AbelianScheme/LieAdditivityProof.md) uses it.
Worker 270 wrote the Lean code and this explanation.

All results are in the namespace `Langlands.Scheme.RelativeDerivation`. They
are about the published `RelativeDerivation π M` of
`Langlands.AlgebraicGeometry.RelativeDerivations`. Here `π : X ⟶ S` is any
morphism of schemes and `M` is any sheaf of `𝒪_X`-modules. Such a
derivation has components `d.app U : Γ(X, U) → Γ(M, U)`. These are additive,
satisfy the Leibniz rule `app_mul`, are compatible with restriction
(`app_restrict`) and kill the sections pulled back from the base
(`app_base`). The module imports only that file and
`Mathlib.AlgebraicGeometry.Morphisms.Flat`, which supplies the affine
fibre-product facts used below. No hypothesis on `π`, the schemes or `M` is
added anywhere.

## Kernel of a derivation

- `app_one`: `d.app U 1 = 0`, from the field `d_one` of the underlying
  derivation.
- `kerSubring d U`: the sections `a : Γ(X, U)` with `d.app U a = 0` form a
  subring of `Γ(X, U)`. Closure under products is the Leibniz rule
  `d(ab) = a • d b + b • d a`. Closure under sums and negatives is
  additivity. It contains `1` by `app_one`.
- `app_eq_zero_of_local`: suppose every point of `U` has an open
  neighbourhood `V ≤ U` on which the restriction of `a` is killed. Then
  `d.app U a = 0`. This follows from the sheaf property of `M`
  (`section_ext`), because `app_restrict` identifies the restriction of
  `d.app U a` to `V` with `d.app V` of the restricted section.
- `app_basicOpen_eq_zero`: let `U` be an affine open such that `d` kills
  every section over `U`. Then `d` kills every section over each basic open
  `X.basicOpen r` of `U`. The proof uses Mathlib's
  `IsAffineOpen.isLocalization_basicOpen`: `Γ(X, D(r))` is the localization of
  `Γ(X, U)` at the powers of `r`. So a section `b` over `D(r)` has the form
  `mk' a s`, and `IsLocalization.mk'_spec` gives `b · s = a` in `Γ(X, D(r))`,
  where `a` and `s` stand for their images in `Γ(X, D(r))`. These images are
  restrictions of sections over `U`, so `d` kills them. Applying `d` and the
  Leibniz rule gives `s • d b = 0`. Since `s` is a unit in `Γ(X, D(r))`,
  `d b = 0`.

## Fibre products

Fix a pullback square `H : IsPullback g iY iX f`, with `g : Y ⟶ X`,
`iY : Y ⟶ T`, `iX : X ⟶ B` and `f : T ⟶ B`, so `Y` is the fibre product
`X ×_B T`. Fix any `π : Y ⟶ S`, a sheaf of modules `M` on `Y` and
`d : RelativeDerivation π M`. The two hypotheses are

- `hX : ∀ U a, d.app (g ⁻¹ᵁ U) (g.app U a) = 0`, and
- `hT : ∀ U a, d.app (iY ⁻¹ᵁ U) (iY.app U a) = 0`.

They say that `d` kills every section pulled back along either projection.

- `app_eq_zero_of_isAffineOpen`: take affine opens `UB` of `B`, `UT ≤ f ⁻¹ᵁ UB`
  of `T` and `UX ≤ iX ⁻¹ᵁ UB` of `X`. Then `d` kills every section over
  `W = g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT`. By `hX`, `hT` and `app_restrict`, the ring maps
  `g.appLE` and `iY.appLE` into `Γ(Y, W)` both land in the subring
  `K = kerSubring d W`. Their corestrictions `φX` and `φT` agree on
  `Γ(B, UB)`, by the commutativity `H.w` of the square
  (`Scheme.Hom.appLE_comp_appLE`). So `pushout.desc φX φT` is a map from the
  pushout `Γ(X, UX) ⊗_{Γ(B, UB)} Γ(T, UT)` to `K`. Composed with the inclusion
  of `K` it equals Mathlib's comparison map `pushoutSection H`, checked on
  both coprojections. Mathlib's `isIso_pushoutSection_of_isAffineOpen` says
  `pushoutSection H` is an isomorphism for affine opens. Hence every section
  over `W` is the image of a pushout element, so it lies in `K`.
- `app_eq_zero_of_isPullback` (the main result): `d.app V b = 0` for every
  open `V` of `Y` and every section `b`. By `app_eq_zero_of_local` it is
  enough to work near a point `y ∈ V`. The proof chooses an affine open `UB`
  around `iX (g y)` (`exists_isAffineOpen_mem_and_subset`). It then chooses
  affine opens `UX ≤ iX ⁻¹ᵁ UB` around `g y` and `UT ≤ f ⁻¹ᵁ UB` around
  `iY y`. The second choice uses `f (iY y) = iX (g y)`, which comes from `H.w`.
  The intersection `W = g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT` is affine. Indeed
  `Scheme.Hom.isPullback_resLE` shows that it is a fibre product of the
  affine schemes `UX` and `UT` over `UB`. `IsAffineOpen.exists_basicOpen_le`
  gives `r` with `y ∈ D(r) ≤ V`, where `D(r)` is a basic open of `W`. On `W`,
  `d` kills all sections by `app_eq_zero_of_isAffineOpen`. So on `D(r)` it
  kills all sections by `app_basicOpen_eq_zero`.

Basic opens are needed because products of affine opens of the two factors
need not form a basis of the topology of `Y`. The intersection `W` is affine,
however, and its basic opens do form a basis.

## Provenance

This is an internal helper with no single literature counterpart. It is the
sheaf-level form of a standard fact of commutative algebra. On affine
pieces, the tensor product `A ⊗_C B` is generated as a ring by the images of
`A` and `B`. Hence a derivation that kills both images is zero, and the
differentials of `X ×_B T` are generated by those pulled back from the two
factors. The Lean statement is general: it allows any pullback square, any
base `π` of the derivation and any module sheaf. Its only use in the Library
is the square of an actual group-scheme product `H ⊗ H` over `S`, in
`cotangentMap_fst_snd_ext`.
