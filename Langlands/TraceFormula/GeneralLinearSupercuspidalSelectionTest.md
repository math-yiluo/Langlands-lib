# The supercuspidal local selection test for `GL_n`

Lean module: `Langlands.TraceFormula.GeneralLinearSupercuspidalSelectionTest`, namespace
`Langlands.TraceFormula`.

`generalLinearSupercuspidalSelectionTest` proves
`GeneralLinearSupercuspidalSelectionTestStatement`: for a finite place `v` of a number field
`K` and `r : ℕ`, with `K_v` given its completion topology and the local-field structure of
`CompletionPadic.topologicalData v`, there is `φ ∈ C_c^∞(GL_{r+1}(K_v))` with the following
three properties. The field and representation carrier have independent universe levels.

1. `φ` has vanishing constant terms (`BaseChange.HasVanishingConstantTerms`). For every block
   shape with at least two blocks, every Haar measure on its unipotent radical `U` and all
   `x, y`, the translated function `u ↦ φ(x u y)` is integrable on `U` and its integral is `0`.
2. Let `π` be an irreducible admissible representation of `GL_{r+1}(K_v)` on a complex vector
   space with carrier in `Type uW`. If, for some Haar measure `μ`, the distribution character
   `Character.distribution μ π hπ` of `π` takes a nonzero value at `φ`, then `π` is
   supercuspidal (`GeneralLinear.IsSupercuspidal`).
3. There is a nonempty open set `U ⊆ GL_{r+1}(K_v)` such that `orbitalIntegral γ νγ φ ≠ 0` for
   every `γ ∈ U`. This holds for every Haar measure `μ` on `GL_{r+1}(K_v)`, every right Haar
   measure `μγ` on the centralizer of `γ` and every quotient measure `νγ` with
   `IsCompatible (glCentralizer γ) μ μγ νγ`.

**Proof.** `K_v` has characteristic zero, since `K → K_v` is an injective ring homomorphism
from a field of characteristic zero (`charZero_of_injective_algebraMap`). The statement is then
`Langlands.AffineGeneric.exists_supercuspidalSelectionTest` for `F = K_v` and `m = r`, proved in
`Langlands.Representation.AffineGeneric.SelectionTest`.

With `n = r + 1`, the test function constructed there is
`φ = Kl_n(ψ, A)⁻¹ Σ_{t ∈ kⁿ, t₁ ⋯ tₙ = 1} 1_{I⁺} · ψ(λ_t)`. Here `k` is the residue field,
`I⁺` is the pro-unipotent radical of the standard Iwahori subgroup, `ψ` is a nontrivial
additive character of `k` and `A ≠ 0` has nonzero Kloosterman sum `Kl_n(ψ, A)`. The form
`λ_t(g) = Σᵢ tᵢ aᵢ(g - 1)` uses the matrix coordinates `aᵢ(Y) = coord ϖ Y i` for a
uniformizer `ϖ`, with `groupCoord ϖ g i = aᵢ(g - 1)`. All `tᵢ` are nonzero because their
product is `1`.

- For `n ≥ 2` the `aᵢ` are the affine simple coordinates of `GL_n`. They are the residues
  of the superdiagonal entries and of `ϖ⁻¹` times the lower-left entry. Each summand restricts
  on `I⁺` to the affine generic character `ψ ∘ λ_t`.
- For `n = 1`, `I⁺ = 1 + 𝔭`, the only tuple is `t₀ = 1`, and `λ_t(g) = res(ϖ⁻¹ (g - 1))` is the
  principal-unit homomorphism `1 + 𝔭 → k`. The root system of `GL_1` is empty.

Each summand has vanishing translated constant terms. A Haar change of variables in the
unipotent radical multiplies the integral by a character value different from `1`.
[TestFunction](../Representation/AffineGeneric/TestFunction.md).

If the distribution character is nonzero at `φ`, it is nonzero on at least one summand.
The image of that summand's integrated action contains a nonzero `I⁺`-eigenvector. The
translates of this vector span the representation and map to zero in the Jacquet quotient
for every conjugate of a proper standard block unipotent radical.
[Supercuspidality](../Representation/AffineGeneric/Supercuspidality.md).

The open set is the locus in `I⁺` where `D(γ) = ∏ᵢ aᵢ(γ - 1)` equals `A`. On the orbit of
each such `γ`, the determinant formula for `D` and the Kloosterman identity give
`φ(x⁻¹ γ x) = 1_{I⁺}(x⁻¹ γ x)`. An Eisenstein argument makes `γ` regular elliptic, so
`Langlands.BaseChange.orbitalIntegralPositivity` applies to the indicator of `I⁺`.
[SelectionTest](../Representation/AffineGeneric/SelectionTest.md).
