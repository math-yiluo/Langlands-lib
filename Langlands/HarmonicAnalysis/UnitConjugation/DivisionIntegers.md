# The integer ring of a division algebra over a local field

The module `Langlands.HarmonicAnalysis.UnitConjugation.DivisionIntegers` constructs compact open
orders: one in every finite-dimensional algebra over a nonarchimedean local field, and the
integer ring of a finite-dimensional division algebra. All declarations are in the namespace
`Langlands.HarmonicAnalysis.UnitConjugation`. Throughout, `F` is a nonarchimedean local field
(`[Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]`, any
characteristic) and `valuation F` the valuation of its valuative relation; compact open orders are
`IsCompactOpenOrder F R` (module `OrderLevels`): compact open subrings stable under the integers
of `F`.

## A compact open order in every finite-dimensional algebra

`exists_isCompactOpenOrder F A`: a finite-dimensional `F`-algebra `A` with its module topology has
a subring `R` with `IsCompactOpenOrder F R`. Proof: in the coordinates
`finiteDimensionalCoordinates F A` (module `Langlands.HarmonicAnalysis.Bicharacter.SelfDual`) take
a box `B = {x | valuation F (x_i) ≤ valuation F s for all i}` containing `1`
(`SelfDual.Internal.mem_some_box`); it is a compact open additive subgroup stable under the
integers of `F`. Its left order `R = {x | x B ⊆ B}` is a subring containing `1`, stable under
the integers, contained in `B` (as `x = x · 1`) and closed, hence compact; and it is open,
because by compactness of `B` (`IsCompact.eventually_forall_of_forall_eventually` for
multiplication) all `x` near `0` satisfy `x B ⊆ B`.

## The integer ring of a division algebra

Let `D` be a division ring with `[Algebra F D] [FiniteDimensional F D]` (not necessarily central).

- `valuation_regularNorm_add_le`: `valuation F (N(x + y)) ≤ max (valuation F (N x))
  (valuation F (N y))` for the regular norm `N = Algebra.norm F` (determinant of left
  multiplication). Proof: the Library's `Langlands.CentralDivision.norm_regularNorm_add_le`
  (module `Langlands.Algebra.DivisionNormValuation`) for the normed field structure
  `Langlands.LocalGalois.localNormedField F`, transferred to `valuation F` by
  `Langlands.LocalGalois.localNormedField_le`.
- `divisionNormValuation D : Valuation D (ValueGroupWithZero F)`, `x ↦ valuation F (N x)`
  (`divisionNormValuation_apply`); `divisionNormValuation_algebraMap`: its value at
  `algebraMap F D c` is `valuation F c ^ finrank F D`.
- `divisionIntegers D : Subring D`, the integer ring `{x | valuation F (N x) ≤ 1}` of this
  valuation (`mem_divisionIntegers`); `smul_mem_divisionIntegers`: it is stable under the
  integers of `F`.

Now `D` carries its module topology (`[TopologicalSpace D] [IsModuleTopology F D]`).

- `continuous_regularNorm`: `N` is continuous, as the determinant of the matrix of left
  multiplication, whose entries are linear in `x` (`Continuous.matrix_det`).
- `isOpen_divisionIntegers`: the integer ring is an additive subgroup containing the
  neighbourhood `N⁻¹ {z | valuation F z < 1}` of `0`, hence open.
- `isCompact_divisionIntegers` proves compactness of the integer ring. Take a compact open order
  `R₀` of `D` (`exists_isCompactOpenOrder`), an element `ϖ ≠ 0` with `valuation F ϖ < 1`, and the
  compact "sphere" `S = R₀ \ ϖ R₀` (in the notation `orderLevel` of module `OrderLevels`). Its
  image under `N` is a compact set of nonzero values, so `valuation F (N y) ≥ γ` on `S` for some
  `γ > 0`. Choose `M : ℕ` with `(valuation F ϖ) ^ M < γ` (`exists_pow_lt₀`).
  For a nonzero integral `x`, let `h : ℕ` be least with `x ∈ ϖ ^ (-h) R₀`. If `h ≤ M`,
  the nesting of the levels gives `x ∈ ϖ ^ (-M) R₀`. If `h > M`, minimality at `h - 1` gives
  `y = ϖ ^ h • x ∈ S`. With `d = finrank F D ≥ 1`, integrality of `x` gives
  `γ ≤ valuation F (N y) = (valuation F ϖ) ^ (h · d) · valuation F (N x) ≤ (valuation F ϖ) ^ M < γ`,
  a contradiction. The level `ϖ ^ (-M) R₀` also contains zero, so the integer ring is a
  closed subset of this compact level.

## Source

André Weil, *Basic Number Theory*, second edition, Springer, 1973, source ID
`weil-1973-basic-number-theory`, Chapter I, §4, Theorem 6, printed pp. 12–13 (PDF pp. 29–30): for
a `p`-field `K` (commutative or not), `R = {x | mod_K(x) ≤ 1}` is the maximal compact subring.
For a finite-dimensional division algebra `D` over `F`, the module of left multiplication by `x`
on the `F`-vector space `D` is `mod_D(x) = mod_F(N_{D/F}(x))`, with `N_{D/F}` the determinant of
left multiplication, so `divisionIntegers D` is Weil's ring `R`. The implementation proves the ring property from the
Library's ultrametric inequality for the regular norm and the compactness by the sphere argument
above, and does not use Haar measure.
