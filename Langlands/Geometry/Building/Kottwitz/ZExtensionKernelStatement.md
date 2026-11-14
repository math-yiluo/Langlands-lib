# Surjectivity on Kottwitz kernels for z-extensions

`ZExtensionKottwitzKernelSurjectivityStatement` states the kernel clause of
Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), Proposition 11.5.3,
printed page 431, PDF page 462 (source ID
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`). The
authors' corrections of 1 November 2024 (source ID
`kaletha-prasad-2024-corrections`, SHA256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`) change only
Section 11.7 in Chapter 11 and leave this proposition unchanged. The file is a
statement awaiting a proof.

## The source statement

In Chapter 11 (opening, printed page 420, PDF page 451) the base field `k` has
a normalized discrete valuation, a Henselian valuation ring and a perfect residue
field, `K` is its maximal unramified extension, `I` is the
inertia group and `Γ = Gal(K/k)`. For a connected reductive `k`-group `G`, the
Kottwitz homomorphism on `G(k)` is the restriction of `κ_{G_K} : G(K) → π₁(G)_I`,
with values in `(π₁(G)_I)^Γ`. Proposition 11.5.3 reads: let
`1 → Z → G̃ → G → 1` be a z-extension; the maps `G̃(k) → G(k)` and
`ker(κ_G̃) → ker(κ_G)` are surjective.

This declaration states only the second map, as an equation for the actual
image of the kernel of `κ_G̃`. The equation `ker(κ_G̃).map p = ker(κ_G)` says both
that `p` maps the kernel of `κ_G̃` into the kernel of `κ_G`, so that the kernel map
of the proposition is defined, and that this map is surjective.

## The Lean statement

Here `F` is any nonarchimedean local field in universe `u`, of either
characteristic, `K = UnramifiedClosure F` is its maximal unramified extension
inside `E = SeparableClosure F`. This specializes the source's base field; the
residue field of `F` is finite, hence perfect, and its valuation ring is complete,
hence Henselian. A z-extension
`z : ZExtension G` is the Library's actual structure: an induced torus `z.Z`, a
closed central embedding `z.i : z.Z → z.H` and a homomorphism `z.p : z.H → G`
that is the fppf quotient by its image, with `z.H` connected reductive with
simply connected derived subgroup. No map on points, kernel or Kottwitz
homomorphism is supplied with it.

The first conjunct concerns points with coefficients in `K`. Its field `k` is
the field of definition of `G`: `G` and `z` are group schemes over `Spec k`, and
their points are taken with coefficients in `K` through the given `k`-algebra
structure. The hypotheses are those of `ReductiveKottwitzExistenceStatement`:
compatible maps `k → K → E`, `E` a separable closure of `k`, and `K/k` normal. They
include `k = F` and `k = K`. The fundamental groups are formed over `E`, and
the inertia group is the kernel of restriction from `Aut_k(E)` to `Aut_k(K)`.
For every connected reductive `G` over `k` and every z-extension `z` of `G`, the
conjunct asserts that the image of the kernel of
`reductiveKottwitz F k z.H : z.H(K) → π₁(z.H)_I` under
`z.H.affinePointsTarget z.p (CommAlgCat.of k K) : z.H(K) → G(K)` is the kernel
of `reductiveKottwitz F k G hG : G(K) → π₁(G)_I`. Mathematically this is the
source proposition for the base field `K`, which again has a Henselian discrete
valuation and a perfect residue field, and over which `Γ` is trivial. It is
applied to `G_K` and to the base change of `z`, which is a z-extension of `G_K`
because the base change of an induced torus is induced. For `k = K` no base
change is needed. Every compatible `k` is
retained, as in `ReductiveKottwitzExistenceStatement`, so that the statement
applies to groups defined over `F` with their `K`-points.

The second conjunct concerns `F`-rational points. For every connected reductive
`G` over `F` and every z-extension `z` of `G` over `F`, the image of the kernel of
`reductiveKottwitzRational F z.H : z.H(F) → (π₁(z.H)_I)^Γ` under
`rationalPoints.map z.p : z.H(F) → G(F)` is the kernel of
`reductiveKottwitzRational F G hG : G(F) → (π₁(G)_I)^Γ`. This is the source
proposition for the base field `F`.

The maps are the constructed homomorphisms of
`Langlands.Geometry.Building.Kottwitz.ReductiveMap`, chosen by classical epsilon.
`reductiveKottwitz` is selected by its squares with every z-extension, and
`reductiveKottwitzRational` as the invariant-valued restriction of the `K`-point map
for `k = F`. Their characterizing properties are the separate unproved targets
`ReductiveKottwitzExistenceStatement` and `ReductiveKottwitzDescentStatement`.
This statement assumes neither one, and no other premise. When the restriction
property holds, the injectivity of the inclusion `A^Γ → A` makes the kernel of
`reductiveKottwitzRational` the preimage in `G(F)` of the `K`-point kernel, which is
the source's `ker(κ_G) = ker(κ_{G_K}) ∩ G(k)`.

## Scope

The statement assumes no identification of a Kottwitz kernel with a zero
subgroup `G(k)^0`. In the source, Proposition 11.5.3 precedes and is used in
the proof of Proposition 11.5.4 (`G(k)^0 = ker κ_G`). So a proof of this
statement can serve as an input to that proof, which is
`Langlands.Geometry.Building.Kottwitz.ZeroKernelStatement` in the Library.

The point-surjectivity clause of Proposition 11.5.3 is not restated here. Over
`K` it is already included in `ReductiveKottwitzExistenceStatement`, which asserts
surjectivity of `z.H(K) → G(K)` for every z-extension. Its rational version,
surjectivity of `z.H(F) → G(F)`, is not stated in this file.

## Source proof route

This describes the intended source argument, not a proved fact of this file.
Since `Z` is induced, the sequence `1 → Z(k) → G̃(k) → G(k) → 1` is exact.
Taking `I`-coinvariants is right exact, and the torsion-freeness of `X_*(Z)_I`
makes `0 → X_*(Z)_I → π₁(G̃)_I → π₁(G)_I → 0` exact, as in the proof of Lemma
2.5.20. Since `X_*(Z)_I` is an induced `Γ`-module, taking `Γ`-invariants keeps
the sequence exact. The torus Kottwitz map `Z(k) → (X_*(Z)_I)^Γ` is surjective
by Corollary 11.1.9. The snake lemma then gives surjectivity of the kernel map.
The Library's elementary `map_kernel_eq_of_kernel_lift`, in
`Langlands.Geometry.Building.Kottwitz.KernelTransport`, is the group-theoretic
form of this last step.
