# Points supported at one finite place and the unequal-rank Whittaker kernel

Module `Langlands.Global.RankinSelberg.UnequalKernelLocalPoint`, namespace
`Langlands.Global.RankinSelbergGlobal`.

## Content

Let `F` be a number field, `v` a finite place and `F_v = FiniteCompletion F v`. Write
`ι_v(h) = localPoint F m v h` for the actual adelic point of `GL_m(𝔸)` whose component at
`v` is `h ∈ GL_m(F_v)` and whose other components are `1`. The definition `localPoint` and
the basic lemmas `localPoint_mul`, `localPoint_mul_comm`, `finiteComponent_localPoint`,
`adelicEquiv_localPoint`, `infinite_ofFinite`, `finite_ofFinite`, `detNorm_localPoint` are
in module `Langlands.Global.RankinSelberg.LocalPointFactorization`, which this
module imports. This module adds the following lemmas.

**Points supported at one place.**

- `adelicGL_ext_infinite_finite`: an adelic point of `GL_m` is determined by its infinite
  and finite parts.
- `localPoint_one`, `localPoint_inv`: `ι_v(1) = 1` and `ι_v(h⁻¹) = ι_v(h)⁻¹`.
- `adelicEquiv_localPoint_apply_of_eq`: if the `(i, j)` entry of `h` equals the `(i, j)`
  entry of the identity matrix, then so does the `(i, j)` entry of the adelic matrix of
  `ι_v(h)`. The proof compares the infinite part, which is `1`, and every finite component.
  The component at `v` is `h` and the others are `1`.
- `localPoint_mem_unipotentAdelic`: if `u ∈ GL_m(F_v)` is upper unitriangular, then
  `ι_v(u) ∈ N_m(𝔸)`. This follows from the previous lemma and
  `Unfolding.mem_unipotentAdelic_iff`.

**Padding.** `padGL` is the embedding `g ↦ diag(g, 1_(n-m))`. Its adelic analogue is
`pad F hle`.

- `localProjection_padGL`, `finite_padGL`, `infinite_padGL`: padding commutes with taking
  the component at a finite place, the finite part and the infinite part. Each is an
  entrywise computation from `padGL_apply`.
- `finiteComponent_pad`: `(diag(g, 1))_v = diag(g_v, 1)`.
- `pad_localPoint`: `diag(ι_v(h), 1) = ι_v(diag(h, 1))`.
- `padGL_mem_localIntegral`: padding maps `GL_m(𝒪_v)` into `GL_n(𝒪_v)`. Both `k` and
  `k⁻¹` have integral entries, and the padding entries `0` and `1` are integral.

**Torus conjugation.** `isUnitriangular_torus_conj`: for any field `K`, any unit `ϖ` and
any `λ ∈ ℤ^m`, the conjugate `ϖ^λ u ϖ^(-λ)` of an upper unitriangular `u` is upper
unitriangular. Here `ϖ^λ = torus ϖ λ = diag(ϖ^(λ_1), …, ϖ^(λ_m))`. Its `(i, j)` entry is
`ϖ^(λ_i) u_(ij) ϖ^(-λ_j)`.

**The kernel.** Let `t < r`, `W : GL_(r+1)(𝔸) → ℂ`, `W' : GL_(t+1)(𝔸) → ℂ`, and let
`K(g) = Unfolding.ordinaryKernel F h W W' s g = W(diag(g, 1)) W'(g) |det g|^(s - (r-t)/2)`
be the integrand of the unequal-rank global Whittaker integral. Suppose that `W` and `W'`
factor at `v` through local functions `φ` and `φ'`:
`W(g ι_v(k)) = W(g) φ(k)` whenever `g_v = 1`, and likewise for `W'` and `φ'`.

- `ordinaryKernel_mul_localPoint`: if `g_v = 1`, then
  `K(g ι_v(k)) = K(g) · φ(diag(k, 1)) φ'(k) |det ι_v(k)|^(s - (r-t)/2)`.
  The proof uses `pad_localPoint`, `finiteComponent_pad`, the two factorizations and the
  multiplicativity of `detPower`.
- **`ordinaryKernel_localPoint_mul`** (pointwise factorization). Assume in addition that
  `φ` and `φ'` are right invariant under `GL(𝒪_v)` with `φ(1) = φ'(1) = 1`, and that `K` is
  left `N_(t+1)(𝔸)`-invariant. Let `d ∈ GL_(t+1)(F_v)` normalize the upper unitriangular
  matrices, and let `g_v ∈ N_(t+1)(F_v) GL_(t+1)(𝒪_v)`. Then
  `K(ι_v(d) g) = φ(diag(d, 1)) φ'(d) |det ι_v(d)|^(s - (r-t)/2) · K(g)`.

  *Proof.* Write `g_v = u k⁻¹` with `u` upper unitriangular and `k ∈ GL(𝒪_v)`, which is
  possible by `IsUnipotentIntegral`. Put `g' = ι_v(g_v)⁻¹ g`, so `g'_v = 1`. For every `e`,
  `ι_v(e) g = ι_v(e u e⁻¹) · g' · ι_v(e k⁻¹)`. This uses that `ι_v(e k⁻¹)` commutes with
  `g'` (`localPoint_mul_comm`). If `e u e⁻¹` is upper unitriangular, then `ι_v(e u e⁻¹)` lies
  in `N(𝔸)` and drops out by the left invariance of `K`. `ordinaryKernel_mul_localPoint` and
  the right `GL(𝒪_v)`-invariance of `φ`, `φ'` then give
  `K(ι_v(e) g) = K(g') φ(diag(e, 1)) φ'(e) |det ι_v(e)|^(s') |det ι_v(k⁻¹)|^(s')`, where
  `s' = s - (r-t)/2`. Taking `e = 1` expresses `K(g)` in the same way. Taking `e = d` and
  comparing the two identities gives the claim.

## Provenance

This is internal supporting material for the proof of
`UnequalEulerFactorizationStatement`. The source is J. W. Cogdell, *Analytic theory of
L-functions for GL_n*, in Bernstein–Gelbart (eds.), *An Introduction to the Langlands
Program* (2004), registered as `cogdell-2004-analytic-theory-gln`: §2.2, printed p.206, and
Theorem 3.3, printed p.215. Cogdell factors the integrand of `Ψ(s; W, W')` over the places
and computes the unramified local integrals. The Library states the factorization with
partial integrals over `N(𝔸) \ GL(𝔸)` (module `PartialWhittakerIntegrals`). The step from
`S` to `S ∪ {v}` therefore needs the behaviour of the global kernel under left translation
by `ι_v(ϖ^λ)` on the classes whose `v`-component lies in `N(F_v) GL(𝒪_v)`. That behaviour is
`ordinaryKernel_localPoint_mul`. The other lemmas are the matrix bookkeeping it needs. The
lemmas introduce no new definitions. The module
`Langlands.Global.RankinSelberg.UnequalEulerFactorizationReduction` uses them.
