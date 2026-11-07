# Equivariant scheme sections of torus-equivariant extensions by vector groups

This module averages a scheme section over a split torus to make it equivariant. A split
torus acts compatibly on a group scheme `E`, on a quotient `q : E ⟶ H`, and on the kernel
`N` of `q`, which is a vector group with linear coordinates. If `q` has a section as a
morphism of schemes, it then has a torus-equivariant section as a morphism of schemes. The
section need not be a group homomorphism. No assumption is made on the characteristic or
on the weights, and `N` need not be central.

Provenance: this is an internal construction. It adapts the exponent-zero Laurent averaging
of the published module `GroupScheme/Rational/SplitTorusVectorExtension` to the equivariance
defect of a section. That module averages the Hochschild two-cocycle of a section of a torus
quotient; here the averaged cocycle is a crossed homomorphism. As context only: the
underlying fact is the vanishing of Hochschild cohomology `Hⁿ(G, V)`, `n > 0`, for groups `G`
of multiplicative type (Milne, *Algebraic groups*, 2017, Remark 15.17, which deduces it from
linear reductivity), applied to the functions from `H` to `N`. The Lean proof does not use
this result. The intended application is the Heisenberg normal form of a multipliable
relative root group, which this module does not treat.

## Setting

The declarations of the first part live in namespace `Langlands.GroupScheme.splitTorus`.
The field `k` and the scheme universe `u` are arbitrary. `I` is a finite type with
decidable equality, and `𝔻 = splitTorus (Spec k) I`. The data are:

- group schemes `E`, `H` and `N` over `Spec k`, with automorphic actions `cE`, `cH` and
  `cN` of `𝔻`;
- a homomorphism `i : N ⟶ E` that is a monomorphism of schemes, and a homomorphism
  `q : E ⟶ H`;
- `hker`: on every test scheme `T`, a point `g` of `E` lies in the range of `i` exactly
  when `g ≫ q = 1`;
- `hq`: `q` intertwines `cE` and `cH`, i.e. `cE.act t g ≫ q = cH.act t (g ≫ q)`;
- `hi`: `i` intertwines `cN` and `cE`, i.e. `cE.act t (w ≫ i) = cN.act t w ≫ i`;
- a morphism of schemes `s : H.X ⟶ E.X` with `s ≫ q = 𝟙` (hypothesis `hs`);
- natural coordinates `e` on `N` with `he : IsLinearVectorCoordinates cN e`, so that each
  torus point acts linearly over the ring of global functions of the test scheme. This is
  used from `act_actionAveragePoint` on.

`H` and `N` are assumed affine over `Spec k` where needed.

## Definitions

- `actionDefectUniversal`, `kernelActionDefect` and `actionDefect t x`. On points, the
  equivariance defect of `s` at a torus point `t` and a point `x` of `H` is
  `δ(t, x) = (t · s(x)) · s(t · x)⁻¹`. It lies in the kernel (`actionDefectUniversal_mem`),
  so it is the image under `i` of a unique point of `N`: `actionDefect_comp`.
- `actionAverageVector x` and `actionAveragePoint x` (written `ρ(x)`), for an affine point
  `x` over a `k`-algebra `A`. Over the Laurent algebra `A[I → ℤ]`, take the universal torus
  point `t` (the published `laurentPoint`) and the constant point `x`. Then `ρ(x)` is the
  point of `N` whose coordinates are the exponent-zero coefficients of the coordinates of
  `t⁻¹ · δ(t, x)`.
- `equivariantSectionPoint x = i(ρ(x))⁻¹ · s(x)`, and `equivariantSection`, the morphism of
  schemes `H.X ⟶ E.X` with these values on affine points (published `homOfAffinePoints`).

## Statements

- `points_mul_comm`: points of a split torus commute.
- `comp_actionDefect`: the defect is natural in the test scheme.
- `actionDefect_mul` (crossed homomorphism): `δ(t r, x) = t · δ(r, x) · δ(t, r · x)`.
- `actionAverageVector_translate`: replacing the universal point `t` by `r t` for a constant
  point `r` does not change the average. This is `coeff_zero_laurentTranslation`, applied
  after naturality of the defect.
- `coeff_zero_laurentConst_kernel` and `coeff_zero_kernelAct`: exponent-zero coefficients of
  constant points, and of the action of a constant torus point.
- `act_actionAveragePoint` (coboundary): `r · ρ(x) = δ(r, x) · ρ(r · x)` for affine points
  `r` of `𝔻` and `x` of `H`.
- `act_equivariantSectionPoint`: `r · σ(x) = σ(r · x)` on affine points.
- `actionAverageVector_naturality`, `actionAveragePoint_naturality`,
  `equivariantSectionPoint_naturality`, `comp_equivariantSection`: compatibility with
  every change of coefficients `A →ₐ[k] B`, and `x ≫ equivariantSection = σ(x)`.
- `equivariantSection_comp`: `equivariantSection ≫ q = 𝟙 H.X`.
- `act_equivariantSection`: for every test scheme `T`, torus point `t` and point `x` of `H`,
  `cE.act t (x ≫ equivariantSection) = cH.act t x ≫ equivariantSection`.
- `IsSplitTorus.exists_equivariantSection` (namespace `Langlands.GroupScheme`). Let `D` be
  any group scheme with `IsSplitTorus D` acting on `E`, `H` and `N` as above, with `H` and
  `N` affine over `Spec k`. The hypotheses are `hker`, `hq`, `hi` and `hs`, together with
  linear coordinates on `N`. The conclusion is: there is `σ : H.X ⟶ E.X` with
  `σ ≫ q = 𝟙` and `cE.act t (x ≫ σ) = cH.act t x ≫ σ` for every test scheme `T`,
  `t : T ⟶ D.X` and `x : T ⟶ H.X`.

## Proofs

**Crossed homomorphism.** Write `δ(t, x)` through `i` and expand both sides using the action
laws `act_mul_left` and `act_mul_right`, the identity `act_inv`, and `hi`. The identity then
holds in the group of points of `E`.

**Coboundary.** Work over `L = A[I → ℤ]` with the universal point `t₀`, the constant
points `r_L` and `x_L`, and apply the crossed homomorphism law at `(t₀, r_L, x_L)`. Act on
both sides by `r_L · (r_L t₀)⁻¹ = t₀⁻¹`; this uses commutativity of torus points. The
result is

`r_L · ((r_L t₀)⁻¹ · δ(r_L t₀, x_L)) = δ(r_L, x_L) · t₀⁻¹ · δ(t₀, (r · x)_L)`.

Take exponent-zero coefficients of the coordinates. On the left, the translation lemma
identifies the inner average with `ρ(x)`, and the action of the constant point `r_L`
commutes with taking coefficients (`coordinateAction_coeff` and
`IsLinearVectorCoordinates.coordinateAction_eq`). On the right, the coordinates of the
constant point `δ(r, x)` are their own exponent-zero coefficients. The second term is the
average at `r · x`. Coordinates are injective, so this is the claimed identity.

**Equivariance.** The coboundary identity, `hi` and the formula for `δ(r, x)` give
`r · σ(x) = σ(r · x)` by a group calculation. This extends to all test schemes by testing the
universal pair on the affine scheme `𝔻 × H` (`affine_hom_ext`). The section property
follows because `i ≫ q = 1`.

**Arbitrary split tori.** Choose an isomorphism `f : D ≅ 𝔻`, restrict the three actions
along `f⁻¹`, apply the construction, and use `f ≫ f⁻¹ = 𝟙` to recover points of `D`.

## Scope

The module constructs an equivariant section of schemes only. It does not make the section a
group homomorphism, does not prove existence of the original section `s`, and does not
treat root groups.
