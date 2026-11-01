# The unipotent slice bound for matrix test functions

Module `Langlands.Representation.GodementJacquet.WhittakerSliceBound`,
namespace `Langlands.GodementJacquet.WhittakerTorus.Padic`.

Let `F` be a p-adic field with its canonical topological data
`T = F.canonicalTopologicalData` (topology, valuation, local field structure),
installed as local instances, and write `|x| = T.normalizedAbs x`. Write
`G = GL_(n+1)(F)` and `N` for its upper unipotent subgroup. Both carry their
Borel σ-algebras, and `du = unipotentHaar F.Carrier n` is the Library's Haar
measure on `N`, with mass one on the integral unipotent subgroup. A full-matrix
test function `Φ : MatrixTestFunction n F.Carrier` is a Schwartz–Bruhat
function on the space of `(n+1) × (n+1)` matrices.

## Source and provenance

The content is internal and derived. It is the bound for the integral over `N`
in the standard proof that the Godement–Jacquet type integrals
`∫ Φ(g) W(g) |det g|^s dg` converge for `Re s` large. That proof uses the
Iwasawa decomposition `G = N A K`, then this bound, then integrals over the torus
(Jacquet, Piatetski-Shapiro and Shalika, *Automorphic forms on GL(3) I* (1979),
printed page 186, cited by Jacquet, Piatetski-Shapiro and Shalika,
*Rankin–Selberg convolutions*, Amer. J. Math. 105 (1983), Section (5.2), printed
page 421). The literature does not state these lemmas separately, and no
literature statement is formalized here. Every declaration is unconditional: no
Whittaker hypothesis, no torus expansion and no Mellin statement is involved.

The declarations were split out unchanged, with the same names and namespace,
from the helper module `WhittakerMatrixConvergence` of the shared draft of task
`3225020b-dd52-4c21-8106-c073e41f30be`. That module imports this one and uses
these declarations for the convergence of full-matrix Whittaker integrals.

## Declarations

- `normBox F n ρ`: the box `{x ∈ F^(n+1) | |x_i| ≤ ρ for all i}`.
  `isClopen_normBox` (for `ρ > 0`) and `isCompact_normBox` (for every `ρ`)
  follow coordinatewise from the Library facts `JPSDilationAssembly.isClopen_le`
  and `JPSDilationAssembly.isCompact_le` for one coordinate, with
  `isClosed_set_pi`, `isOpen_set_pi` and `isCompact_univ_pi`.
- `boxTest F n hρ`: the characteristic function of `normBox F n ρ`, as a
  Schwartz–Bruhat function on `F^(n+1)` (`Hecke.TestFunction.characteristic`).
  `boxTest_apply_of_le`: it equals `1` at every `x` with all `|x_i| ≤ ρ`.
- `torusMonomial F e a = ∏_i |a_i|^(-e_i)` (written `(|a_i|⁻¹)^(e_i)`), a real
  number, for exponents `e : Fin (n+1) → ℕ` and `a : Fin (n+1) → Fˣ`.
  `torusMonomial_nonneg`: it is nonnegative.
- `measurable_matrixIntegrand hW Φ s`: for continuous `W : G → ℂ`, every
  `Φ` and every complex `s`, the integrand
  `GodementJacquet.Padic.matrixIntegrand F Φ s W`, that is
  `g ↦ Φ(g) W(g) |det g|^s`, is measurable. It is the product of the continuous
  functions `Φ ∘ val` and `W` and of `|det|` raised to the power `s`, and a
  continuous function is Borel measurable.
- `exists_slice_bound Φ k` (**slice bound**): for every `Φ` and `k ∈ G` there
  are reals `B` and `ρ > 0` and exponents `e` such that, for every
  `a : Fin (n+1) → Fˣ`,

  `∫⁻_N ‖Φ(u diag(a) k)‖ₑ du ≤ ofReal B · ofReal (∏_i |a_i|^(-e_i)) · ‖boxTest F n hρ a‖ₑ`,

  where `diag(a)` is the diagonal matrix with entries `a_i` and
  `boxTest F n hρ a` is evaluated at the vector of the `a_i`. In particular
  the integral is `0` unless every `|a_i| ≤ ρ`.

## Proof of the slice bound

`Φ` is continuous with compact support, so `|Φ| ≤ B₀` everywhere for some
`B₀ ≥ 0`. Let `L` be the image of `tsupport Φ` under the continuous map
`M ↦ M k⁻¹`; it is a compact set of matrices. If `Φ(u diag(a) k) ≠ 0`, then
`u diag(a) k ∈ tsupport Φ`, so `u diag(a) ∈ L`. Hence `‖Φ(u diag(a) k)‖ₑ` is at
most `B₀` times the indicator of `E_a = {u | u diag(a) ∈ L}`, and the integral is
at most `B₀ · du(E_a)` (`lintegral_mono`, `lintegral_indicator_const_le`).

Apply `RankinSelberg.unipotentHaar_mul_diagonal_le` (module
`Langlands.Representation.RankinSelberg.UnipotentDiagonalVolume`) to `L`. It
gives a unit `r`, a real `C` and exponents `e` such that, for every `a`, the set
`E_a` is empty unless every `|a_i| ≤ |r|`, and `du(E_a) ≤ C ∏_i |a_i|^(-e_i)`.
Take `ρ = |r| > 0` and `B = B₀ |C|`.

- If every `|a_i| ≤ ρ`, then `boxTest F n hρ a = 1`, and
  `B₀ · du(E_a) ≤ B₀ · C ∏_i |a_i|^(-e_i) ≤ B₀ |C| ∏_i |a_i|^(-e_i)`.
- Otherwise `E_a` is empty, so the bound `B₀ · du(E_a)` is `0`.
