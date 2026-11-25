# Equivariance of archimedean restrictions of global Whittaker functions at a complex place

Module `Langlands.Global.RankinSelberg.ComplexPlaceWhittakerEquivariance`, namespace
`Langlands.Global.RankinSelbergGlobal`. It is a step towards the bridge premise of the
conditional reduction `complexPlaceFunctionalEquationReduction` (complex-place Rankin–Selberg
functional equation). Provenance: internal. Everything here is
proved; nothing is assumed.

Let `F` be a number field, `w` a complex place, and `ι_w : GL_n(ℂ) → GL_n(𝔸_F)` the
Library's `complexPlacePoint F n w` (the element `g` at `w`, the identity at the other places).
For a finite adelic point `b`, `finitePoint F n b` is `b` with archimedean component `1`. For an
actual cuspidal realization `T` and a vector `x`, `W_x = cuspWhittaker F T χ x` is the Library's
global Whittaker coefficient for an additive character `χ` of `𝔸_F`.

## Points

- `complexPlaceGL_entry`: the entry `(i, j)` of `ι_w(g)` (in the Library's mixed coordinates
  `ArchimedeanGL`) at a complex place `v` is the entry of `g` if `v = w` and of the identity
  otherwise. Proof: by definition (`rfl`).
- `toArchimedeanGL_complexPlaceFactor`: the archimedean matrix of the compact factor
  `complexPlaceFactor w l` of `l ∈ U(n)` is `complexPlaceGL w l`. Proof: compare entries, place
  by place, using `complexPlaceFactor_snd`.
- `complexPlaceCompactInclusion_val`: the infinite adelic element of the compact action of
  `l ∈ U(n)` at `w` is `ι_w(l)` in completion coordinates.
- `complexPlacePoint_mul_compact`: `ι_w(g) b · ι_w(k) = ι_w(g k) b` for `k ∈ GL_n(ℂ)`, written
  with the infinite adelic element of `ι_w(k)`. Proof: the adelic group is the product of its
  infinite and finite parts (`AdelicGL.split`), and `ι_w(k)` has finite part `1`.
- `complexPlacePoint_eq_ofInfinite`, `complexPlacePoint_mul`: `ι_w` is the image of an infinite
  adelic element and is multiplicative.
- `complexPlacePoint_entry`: the adelic entries of `ι_w(g)` are the pairs
  (infinite entry, entry of the identity at the finite places).
- `complexPlaceGL_entry_fst`, `complexPlaceGL_entry_eq_zero`, `complexPlaceGL_entry_eq_one`: the
  real-place entries of `ι_w(g)` are those of the identity, an entry of `ι_w(g)` is `0` if
  `i ≠ j` and `g_(ij) = 0`, and it is `1` if `i = j` and `g_(ii) = 1`.
- `complexPlacePoint_mem_unipotentAdelic`: for `u ∈ N_n(ℂ)` (upper unitriangular), `ι_w(u)` is
  upper unitriangular in `GL_n(𝔸_F)` (Library `Unfolding.mem_unipotentAdelic_iff`).

## The generic character at `ι_w(u)`

- `complexPlaceGL_superdiag_sum`: the superdiagonal sum `∑_i (ι_w(u))_(i,i+1)` in the infinite
  adele ring is `Pi.single w s'`, where `s'` corresponds to `s = ∑_i u_(i,i+1)` under the
  identification `F_w ≅ ℂ` (`ringEquivComplexOfIsComplex`). Proof: apply the Mathlib ring
  isomorphism `ringEquiv_mixedSpace` to mixed coordinates and compare at each real place (all
  zero) and each complex place (`s` at `w`, zero elsewhere).
- `adeles_sum_mk`: a finite sum of adeles given by components is the pair of the component sums.
- `genericCharacter_complexPlacePoint`: let `χ` be a character of `𝔸_F` whose values on
  `(Pi.single w y, 0)` are `ψ_c(y)` for `c ∈ ℂˣ`, where `ψ_c = complexScaledCharacter c`. Then
  the Library's generic character of `χ` (all coefficients `1`) at `ι_w(u)` is
  `complexWhittakerCharacter c u = ψ_c(∑_i u_(i,i+1))`. Proof: the argument of `χ` is the
  superdiagonal sum of `ι_w(u)`, which is `(Pi.single w s', 0)` by the previous items.
- `complexComponent_complex`: if the component of the unitary character `ψ` at `w` is `ψ_a`
  (`IsComplexAdditiveComponent`), the hypothesis above holds for `χ = ψ.complex` and `c = a`.
- `complexComponent_complex_inv`: it then holds for `χ = ψ.complex⁻¹` and `c = -a`, because
  `ψ⁻¹(x) = ψ(-x)` and `ψ_a(-z) = ψ_(-a)(z)` (`complexScaledCharacter_apply`: both are
  `e(Tr(-a z))`).

## The Whittaker restrictions

- `cuspFunction_complexPlaceCompact`, `cuspWhittaker_complexPlaceCompact`: the realized function
  and the Whittaker coefficient of the compact action at `w` of `l` on `y` are those of `y`
  right translated by the adelic element of `l`. These copy the Library's proofs for the finite
  action (`UnramifiedWhittaker.cuspFunction_finiteRepresentation`,
  `cuspWhittaker_finiteRepresentation`), using the Library's
  `evaluate_complexPlaceCompactRepresentation`.
- `complexPlaceRestriction_rightTranslation` (**`U(r+1)`-equivariance**): let `A` be a
  `(𝔤, K)`-map at `w` from the `U(r+1)`-finite standard module of `d` into `T`
  (`IsComplexPlaceMap`, module `ComplexPlaceIsotypic`). If `f'` is the right translate of `f` by
  `k ∈ U(r+1)`, then `g ↦ W_(A f')(ι_w(g) b)` is the right translate by `k` of
  `g ↦ W_(A f)(ι_w(g) b)`. Proof: `A f'` is the compact action of `k` at `w` on `A f`, which
  translates the Whittaker coefficient by `ι_w(k)`, and `ι_w(g) b ι_w(k) = ι_w(g k) b`.
- `complexPlaceRestriction_mul_left` (**`θ`-equivariance**): if `χ` is a standard additive
  character (`IsStandardAdditiveCharacter`) satisfying the hypothesis of
  `genericCharacter_complexPlacePoint` for `c`, then for `u ∈ N_(r+1)(ℂ)`,
  `W_x(ι_w(u g) b) = complexWhittakerCharacter c u · W_x(ι_w(g) b)`. Proof:
  `ι_w(u g) b = ι_w(u) (ι_w(g) b)`, `ι_w(u) ∈ N(𝔸)`, and the Library's
  `Unfolding.cuspWhittaker_mul_left` gives the generic character, which
  `genericCharacter_complexPlacePoint` evaluates.
