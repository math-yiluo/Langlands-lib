# Moderate growth of weighted square-integrable automorphic functions: proof

Module `Langlands.Global.WeightedSquareIntegrableModerateGrowthProof` proves

`weightedSquareIntegrableModerateGrowth : WeightedSquareIntegrableModerateGrowthStatement`

(module `AdelicSpectralWitnessReduction`).

## The statement

Let `F` be a number field and `G` a connected reductive group over `F` (`IsConnectedReductive G`),
smooth of relative dimension `d ∈ ℕ` with a differential commutator `hcalc` (through which the centre
`𝔷` acts), and let `K` be a maximal compact subgroup of `G(𝔸)` with archimedean part
`K_∞ = K.comap (ofInfinite F G)`. Let `N` and `m` be natural numbers and
`rho : MatrixRepresentation G (Fin N)` a homomorphism of group schemes from `G` to `GL_N` that is
a closed immersion of the underlying schemes (`IsClosedSubgroup rho`), and suppose there is a
minimal parabolic subgroup `P₀` with `K` an Iwasawa compact subgroup for it. Let `μG` be the
quotient on `[G] = G(F) \ G(𝔸)` of the Haar measure of `G(𝔸)`
(`LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F G) _ Measure.haar`) and
`σ_{[G]} = rationalLogHeight F G rho`. If `Φ : G(𝔸) → ℂ` is left `G(F)`-invariant, smooth,
`K_∞`-finite and `𝔷`-finite and `y ↦ Φ(y.out) / σ_{[G]}(y)^m` lies in `L²([G], μG)`, then `Φ`
has moderate growth (`HasModerateGrowthFunction F G rho Φ`): there are a real `C > 0` and a real
`r` with `‖Φ g‖ ≤ C ‖g‖^r` for every `g ∈ G(𝔸)`, where
`‖g‖ = RepresentationGrowth.adelicSourceNorm F G rho g`. No central character is assumed. The
proof uses neither the minimal parabolic subgroup nor its Iwasawa compact subgroup.

## Proof (as implemented)

The theorem is the term

`weightedSquareIntegrableModerateGrowth_of_reduction adelicReproducingKernel
adelicRationalConjugateCountingAllPoints.{0}`,

which combines three results of the Library.

- `weightedSquareIntegrableModerateGrowth_of_reduction` (module
  `AdelicWeightedModerateGrowthReduction`) derives the statement from
  `AdelicReproducingKernelStatement` and `AdelicRationalConjugateCountingAllPointsStatement.{0}`;
  see [the reduction](AdelicWeightedModerateGrowthReduction.md).
  - If `N = 0`, the closed immersion `rho` induces a closed embedding of `G(𝔸)` into the adelic
    matrix group `GL_0(𝔸)` (`RepresentationGrowth.isClosedEmbedding_adelicMatrix`), which is
    injective; as `GL_0(𝔸)` is trivial, `G(𝔸)` is a subsingleton, and the bound holds with
    `C = ‖Φ 1‖ + 1` and exponent `r = 0`. Neither premise is used in this case.
  - If `N > 0`, it follows the proof of Mœglin–Waldspurger I.2.5, Lemma (b), with the
    square-integrable function with a unitary central character replaced by the weighted function
    `f(y) = Φ(y.out) / σ_{[G]}(y)^m` on the full quotient `[G]`. Write
    `ht = RepresentationGrowth.adelicHeight F G rho`. The reproducing kernel gives
    `Φ(x) = ∫ Φ(x a) A(a) da` with `A` continuous and compactly supported; let `C` be the support
    of `A` and `L ≥ 1` a bound of `ht` on `C`. On `x C` the weight satisfies
    `σ_{[G]}(q(x a)) ≤ L ht(x)` (`q` the quotient map), so
    `‖Φ(x a)‖ ≤ (L ht(x))^m ‖f(q(x a))‖`. The point count, applied to the compact set `C C⁻¹`,
    gives `B ≥ 0` with `#(G(F) ∩ x C C⁻¹ x⁻¹) ≤ B ht(x)^e` for every `x`; hence the image under
    `a ↦ q(x a)` of the Haar measure restricted to `C` is at most `B ht(x)^e · μG`. The
    Cauchy–Schwarz inequality on `[G]` then gives
    `‖Φ(x)‖ ≤ (L ht(x))^m ‖A‖₂ √(B ht(x)^e) ‖f‖₂`, where `‖A‖₂` is the `L²` norm of `|A|` for
    the Haar measure and `‖f‖₂` that of `|f|` for `μG`. Since `ht(x) ≥ 1` and
    `ht(x) = N^s ‖x‖` with `s` the sum of the multiplicities of the infinite places of `F`
    (`RepresentationGrowth.adelicHeight_eq_scalar_mul_sourceNorm`), this gives the bound with
    real exponent `r = m + e`.
- `adelicReproducingKernel` (module `AdelicReproducingKernelProof`) proves
  `AdelicReproducingKernelStatement`: every left `G(F)`-invariant, smooth, `K_∞`-finite and
  `𝔷`-finite `Φ` satisfies `Φ g = ∫ a, Φ (g * a) * A a ∂Measure.haar` for every `g`, for a
  continuous compactly supported `A`, without a growth hypothesis (Harish-Chandra 1966, §8,
  Theorem 1, in adelic form). See [the reproducing kernel proof](AdelicReproducingKernelProof.md).
- `adelicRationalConjugateCountingAllPoints` (module
  `AdelicRationalConjugateCountingAllPointsProof`) proves
  `AdelicRationalConjugateCountingAllPointsStatement.{u}`, used at universe `0` (the target has
  `F : Type`). For an affine group `G` over `F` and a closed immersion
  `rho : MatrixRepresentation G (Fin N)` with `N > 0`, it gives a natural number `e`, chosen
  before the compact set, such that for every compact `C ⊆ G(𝔸)` there is a real `B(C) ≥ 0` with
  `G(F) ∩ x C x⁻¹` finite and `#(G(F) ∩ x C x⁻¹) ≤ B(C) ht(x)^e` for every `x ∈ G(𝔸)`, the finite
  component of `x` being unrestricted (Mœglin–Waldspurger I.2.4, Lemma (a)(i), with `y = x`). The
  constant `B(C)` cannot be dropped: for `G = GL₁` over `ℚ` with the identity embedding,
  `ht(1) = 1`, while `G(ℚ) ∩ C` has two elements for `C = {1, −1}`. See
  [the counting proof](AdelicRationalConjugateCountingAllPointsProof.md).

The theorem uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Sources

- Harish-Chandra, *Discrete series for semisimple Lie groups II*, Acta Math. 116 (1966), §8,
  Theorem 1, pp. 18–19.
- C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein series*, Cambridge
  University Press, 1995, I.2.4, Lemma (a)(i), pp. 25–26, and the proof of I.2.5, Lemma (b),
  pp. 26–27.
