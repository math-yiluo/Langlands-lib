# Factorization of a global Whittaker function at one unramified place

`Langlands.Global.RankinSelbergGlobal.UnramifiedWhittakerFactorizationStatement` is a
Prop-valued statement. Take a cusp form that is spherical at a finite place `v` where
everything is unramified. The statement says that its global Whittaker function, as a
function of the `v`-component alone, is its value at the other components times the
normalized spherical Whittaker function of Shintani. This is the local factor at one
place of the factorization `W_φ(g) = ∏_v W_(φ_v)(g_v)` used in Cogdell 2004, §2.2.
Nothing here proves the statement.

## Sources

* J. W. Cogdell, *Analytic theory of L-functions for GL_n*, in Bernstein–Gelbart (eds.),
  *An Introduction to the Langlands Program* (2004), registered as
  `cogdell-2004-analytic-theory-gln` (PDF SHA-256 `8117f145…`, PDF page = printed page + 3).
  * §2.2, printed p.206 (PDF p.209): for a factorizable cusp form `φ = ⊗ φ_v` there is a
    choice of local Whittaker models with `W_φ(g) = ∏_v W_(φ_v)(g_v)`. This is a
    consequence of the uniqueness of Whittaker models.
  * printed p.215 (PDF p.218), before Theorem 3.3: if `π_v` and `ψ_v` are unramified, the
    Whittaker model has a unique `GL(𝒪_v)`-fixed Whittaker function `W_o` with
    `W_o(e) = 1`. There is an explicit formula for it in terms of the Satake parameter,
    due to Shintani.
* T. Shintani, *On an explicit formula for class-1 "Whittaker functions" on GL_n over
  P-adic fields*, Proc. Japan Acad. 52 (1976), 180–182, registered as
  `shintani-1976-class-one-whittaker`. p.180 characterizes the class-1 Whittaker function
  by `N`-equivariance, the Hecke eigen-equations and `W(1) = 1`. p.181 gives the explicit
  formula.

## The statement

Let `F : Type u` be a number field with `[CompactSpace (AdeleQuotient F)]`. Let
`ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)` be trivial on `F`. Let `T` be
an actual cuspidal realization of `GL_(r+1)` and `P` a spectral presentation of `T`
(universe `uQ` for its local factors). Let `S` be a finite set of finite places with
`P.exceptional ⊆ S` and `FunctionalEquationComparison.FiniteAdditiveSupport ψ S`: at every
finite `w ∉ S` the canonical local component of `ψ` exists and has conductor `𝒪_w`
(additive conductor `0`). These are the hypotheses of `UnequalEulerFactorizationStatement`.

Let `x : T.Space` satisfy `IsSphericalOutside F T S x`, i.e. `x` is fixed by
`GL_(r+1)(𝒪_w)` at every finite `w ∉ S`. Fix:

* a finite place `v ∉ S`;
* `ψv : Correspondence.NontrivialAdditiveCharacter (padicField v)` with
  `IsCanonicalFiniteAdditiveComponent ψ v ψv`, i.e. `ψv(y) = ψ(ι_v y)` for `y ∈ F_v`, where
  `ι_v y` is the adele with `y` at `v` and `0` elsewhere;
* a unit `ϖ` of `F_v` that is a uniformizing element for the canonical valuation of
  `padicField v` (`GeneralLinear.Iwasawa.IsUniformizingElement`);
* a tuple `a : Fin (r + 1) → ℂˣ` with `Unramified.Eigenvalues.ofTuple a` equal to the
  spectrum `P.spectralSystem.eigenvalues v _` that `P` gives at `v`. So `a` is any ordering
  of the Satake parameter of `T` at `v`.

Then for every adelic point `g : Points F (r + 1)` whose `v`-component is `1`
(`finiteComponent F (r + 1) v g = 1`) and every `h : FiniteLocalGL F (r + 1) v`, i.e.
`h ∈ GL_(r+1)(F_v)`, both of the following hold:

1. `cuspWhittaker F T ψ.complex x (g * ι_v h) =
   cuspWhittaker F T ψ.complex x g * sphericalWhittaker hϖ θ q a h`;
2. `cuspWhittaker F T ψ.complex⁻¹ x (g * ι_v h) =
   cuspWhittaker F T ψ.complex⁻¹ x g * sphericalWhittaker hϖ θ⁻¹ q a h`.

The symbols are as follows.

* `ι_v h` is the adelic point with component `h` at `v` and `1` at every other place,
  finite or archimedean. The statement writes it out in full:
  `(GeneralLinearGroupPoints.adelicEquiv F (r + 1)).symm (AdelicGL.ofFinite F (r + 1)
  (FiniteAdelicGL.localInclusion F (r + 1) v h))`. `localInclusion` puts `h` at `v` in the
  finite adelic group. `ofFinite` adds the identity at the archimedean places.
  `adelicEquiv.symm` turns the result into a point of the group scheme.
* `cuspWhittaker F T χ x` is the global `χ`-Whittaker function of the cusp form of `x`
  (module `Langlands.Global.RankinSelberg.UnequalIntegrals`), for `χ = ψ.complex` and
  `χ = ψ.complex⁻¹`.
* `θ = Whittaker.standardCharacter ψv r` is the character
  `u ↦ ψv(u_(0,1) + u_(1,2) + ⋯ + u_(r−1,r))` of the upper unipotent group `N_(r+1)(F_v)`.
  `θ⁻¹ = Whittaker.inverseStandardCharacter ψv r` is its inverse. These are the
  restrictions to `N_(r+1)(F_v)`, embedded at `v`, of the generic characters of `ψ` and
  `ψ⁻¹` that define `cuspWhittaker`. The canonical topology of `padicField v` is passed
  explicitly (`@…`). The carrier `v.adicCompletion F` also has its completion topology,
  which is equal to it but not definitionally equal.
* `q` is `(padicField v).canonicalTopologicalData.residueCardinality`, the size of the
  residue field of `F_v`.
* `GeneralLinear.Spherical.sphericalWhittaker hϖ θ q a` is the explicit spherical
  Whittaker function of Shintani (module `Langlands.Representation.Whittaker.Spherical`).
  For upper unipotent `u`, `k ∈ GL_(r+1)(𝒪_v)` and `λ_0 ≥ ⋯ ≥ λ_r`, its value at
  `u · diag(ϖ^(λ_0), …, ϖ^(λ_r)) · k` is `θ(u) δ_B^(1/2)(ϖ^λ) s_λ(a)`, where `s_λ` is the
  Schur polynomial. It vanishes on the other cells. Here `ψv` has conductor `𝒪_v`, so `θ`
  is trivial on `N_(r+1)(𝒪_v)`, and then its value at `1` is `1`
  (`GeneralLinear.Spherical.sphericalWhittaker_one`).

## Relation to the sources

Let `φ = ⊗ φ_w` be a pure tensor with `φ_v` spherical, and `g_v = 1`. Cogdell's
factorization gives `W_φ(g · ι_v h) = W_(φ_v)(h) ∏_(w ≠ v) W_(φ_w)(g_w)` and
`W_φ(g) = W_(φ_v)(1) ∏_(w ≠ v) W_(φ_w)(g_w)`. With the normalization `W_(φ_v) = W_o`,
`W_o(e) = 1` (p.215), this is item 1 for `φ`, once `W_o = sphericalWhittaker` (Shintani's
formula). Item 2 is the same for the `ψ⁻¹`-Whittaker model.

The statement is the intrinsic form of this local factor. Fix `g`. The function
`h ↦ W_x(g · ι_v h)` is `θ`-equivariant on the left and right invariant under
`GL_(r+1)(𝒪_v)`, and it lies in the `θ`-Whittaker model of the unramified local component
`π_v` of `T`. Uniqueness of the Whittaker model and the one-dimensionality of the
spherical line of `π_v` make it a multiple of `W_o`. Its value at `h = 1` is `W_x(g)`. So
the statement needs neither the factorization `T ≅ ⊗' π_w` nor that `x` be a pure tensor.

**Satake parameters.** The tuple `a` comes from the presentation's spectra. These are
normalized by the spherical Hecke equations `T_i f = q^(i(r+1−i)/2) e_i(a) f`
(`Unramified.standardHeckeScalar`, module
`Langlands.Representation.Unramified.HeckeOperators`). This is the normalization of the
Markdown of `UnequalEulerFactorizationStatement`. Under it, the Shintani function with
parameter `a` satisfies the same Hecke equations. That is Shintani's characterization
(p.180), and the Library proves it as
`Conductor.sum_sphericalWhittaker_mul_labelledRep` in
`Langlands.Representation.Conductor.UnramifiedSphericalWhittaker`.

**Conductor of `ψv`.** `FiniteAdditiveSupport ψ S` gives, at `v ∉ S`, a canonical
component of conductor `𝒪_v`. `IsCanonicalFiniteAdditiveComponent ψ v` fixes every value
of a component, so that component is the `ψv` of the statement. This is the source's
hypothesis that `ψ_v` is unramified.

## Deviations from the sources

* The statement concerns any vector `x` that is spherical outside `S`, not only pure
  tensors. It has no restricted tensor product decomposition of `T` (see above).
* Both sides use the global Whittaker function, so no choice of local Whittaker models
  appears. Instead, the local function is the explicit `sphericalWhittaker`, with
  `W_o(e) = 1`.
* The statement holds for every uniformizer `ϖ` and every ordering `a` of the Satake
  parameter. The source fixes one uniformizer and one parameter.
* `g` is any adelic point with `g_v = 1`. This covers the source's factorization at `v`
  for every value of the other components.

## Provenance

This is a derived statement. It is the factor at one unramified place of Cogdell's
factorization (p.206), with Cogdell's normalization `W_o(e) = 1` (p.215) and Shintani's
explicit formula. It is written in a form that the Library's objects can state: the actual
cuspidal realization, its spectral presentation and the global Whittaker function
`cuspWhittaker`. It is the local input for a proof of
`UnequalEulerFactorizationStatement` and its dual and equal-rank companions. Those proofs
apply it at each place `v ∉ S` to the vectors `x` and `x'`, then compute the unramified
local integral.
