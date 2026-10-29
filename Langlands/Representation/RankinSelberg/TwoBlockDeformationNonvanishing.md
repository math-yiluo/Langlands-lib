# A section with nonzero Jacquet value at the identity

Module `Langlands.Representation.RankinSelberg.TwoBlockDeformationNonvanishing`,
namespace `Langlands.RankinSelberg.TwoBlockDeformation`.

This is a helper module for the proof of
`Langlands.RankinSelberg.TwoBlockWhittakerDeformationStatement`. It shows that
the Jacquet integral `J(f)(1)` of JPSS (4.6.2) is not identically zero on the
actual lower induction of two smooth blocks. More precisely, it constructs one
section `f` whose restriction to the upper radical has compact support and for
which `J(f)(1) ≠ 0`. A corollary applies this to the deformed blocks `σ_u` at
every complex `u`. The module proves no convergence statement for other
sections and no statement about the Whittaker model.

## Provenance

JPSS (source ID `jpss-1983-rankin-selberg`), Section 4.6, printed pages
410–411 (one-based PDF pages 45–46), define sections `f` of the induced
representation, the covariance (4.6.1), and the function
`g ↦ ∫ ⟨f(u(x) g), ⊗ ℓ_i⟩ ψ(x) dx` of (4.6.2). On page 411 they assert that
this function lies in the Whittaker model of `σ_u` and that every element of
that model has this form. That use needs the functional `f ↦ J(f)(1)` to be
nonzero. The source does not state this nonvanishing as a separate lemma or
prove it. The statements and proofs in this module are internal. They use the
standard construction of a section supported on `Q̄ K` for a small compact open
subgroup `K` with an Iwahori factorization.

The Library objects are those of the published module
`Langlands.Representation.RankinSelberg.TwoBlockJacquetData`: `Sections`,
`sectionEval`, `upperRadical`, `integrand` and `jacquetFunction`. Its
Markdown file describes how they match (4.6.1) and (4.6.2), including the
positive character `ψ` of the corner entry `x_(m_0, 0)`.

## Setting

Let `p` be prime, `F : PadicField.{uF} p`, `T = F.canonicalTopologicalData`,
and give `F.Carrier` the topology `T.topology`. Let `m : Fin 2 → ℕ` and
`h : ∑ i, (m i + 1) = t + 1`, and let `B = succBlockShape m h` be the two-block
shape of `GL_(t+1)`. Let `W : Fin 2 → Type uW` be complex vector spaces carrying
representations `σ i` of `GeneralLinear (m i + 1) F.Carrier`. Let `ψ` be a
unitary additive character of `F.Carrier`. `Sections F h σ` is the space of
smooth sections of the actual lower induction `I(σ_1 ⊗ σ_2)` from the lower
parabolic `Q̄ = B.oppositeParabolic F.Carrier`, with the normalizing half
modulus. `upperRadical h F.Carrier x` is the matrix `[[1, x], [0, 1]]`. For
functionals `ℓ_i` on `W i` and a measure `μ` on the rectangular matrices
`Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier`,
`jacquetFunction ψ ell μ f g` is the Bochner integral
`∫ x, ⟨f(u(x) g), ℓ_1 ⊗ ℓ_2⟩ ψ(x_(m_0, 0)) ∂μ`.

## Results

### Helper lemmas

- `character_eq_one_mem_nhds F ψ`: the set `{y | ψ y = 1}` is a neighbourhood
  of `0` in `F.Carrier`.

  *Proof.* The preimage under `ψ` of the open arc of the circle of half-width
  `π/2` around `1` is a neighbourhood of `0`, since `ψ` is continuous. The
  topology of `F.Carrier` is linear over its valuation ring
  (`IsLinearTopology.hasBasis_open_submodule`). So the preimage contains an
  open submodule `S`. For `y ∈ S`, every multiple `n • y` lies in `S`. Hence
  every power `ψ(y)^n` lies in the arc, and
  `Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two` gives `ψ(y) = 1`.

- `eq_one_of_mem_oppositeParabolic_of_mem_unipotentSubgroup B R`: for any block
  shape `B` and commutative ring `R`, an element of `GL_n(R)` that lies both in
  the lower parabolic `B.oppositeParabolic R` and in the upper unipotent radical
  `B.unipotentSubgroup R` is `1`.

  *Proof.* Compare entries in block coordinates. Entries above the diagonal
  blocks vanish by the lower parabolic condition. Entries below vanish by the
  upper parabolic condition. The diagonal blocks are identity matrices by the
  unipotent condition. The proof reuses the published `BlockShape` lemma from
  `Langlands.Group.GL.OppositeBlockIntersection`.

- `oppositeUnipotentSubgroup_le_oppositeParabolic B R` and
  `leviSubgroup_le_oppositeParabolic B R`: the lower unipotent radical and the
  block-diagonal Levi subgroup lie in the lower parabolic.

- `mem_of_mem_unipotentSubgroup_of_mul_inv_mem B R K hK hy hl hyl`: let `K` be
  a subgroup of `GL_n(R)` whose ordered product map
  `(K ∩ Ū) × (K ∩ M) × (K ∩ U) → K` (`B.iwahoriProduct R K`) is surjective. If
  `y` lies in the upper radical `U`, `l ∈ K`, and `y l⁻¹ ∈ Q̄`, then `y ∈ K`.

  *Proof.* Write `l = a b c` with `a ∈ K ∩ Ū`, `b ∈ K ∩ M`, `c ∈ K ∩ U`. Then
  `y c⁻¹ = (y l⁻¹)(a b)` lies in `Q̄` and in `U`. By the previous lemma it is
  `1`, so `y = c ∈ K`.

- `upperRadical_mem_unipotentSubgroup h R x`: `upperRadical h R x` lies in the
  upper unipotent radical of `succBlockShape m h`. The proof checks the four
  block entries with the published `upperRadical_index_*` lemmas.

### Nonvanishing

- `exists_section_jacquetFunction_one_ne_zero F h ψ σ hσ ell hell`: assume
  every `σ i` is smooth (`IsSmooth`) and every `ℓ_i` is nonzero. Let `μ` be
  any additive Haar measure on the rectangular matrices, for any measurable
  structure on `F.Carrier` that makes the matrix space Borel. Then there is a
  section `f : Sections F h σ` such that
  `x ↦ sectionEval F h σ f (upperRadical h F.Carrier x)` has compact support
  and `jacquetFunction ψ ell μ f 1 ≠ 0`.

  *Proof.*
  1. Choose `v_i` with `ℓ_i(v_i) ≠ 0`. By smoothness, `v_i` has an open
     stabilizer `H_i`.
  2. The set of `q ∈ Q̄` whose Levi projection lies in `H_1 × H_2` and at
     which the half modulus is `1` is open in `Q̄`. It contains `1`. Write it
     as `O ∩ Q̄` for an open set `O` of `GL_(t+1)` (`isOpen_induced_iff`).
  3. The entry `g ↦ g_(m_0, 0)` in block coordinates (row `m_0` of the first
     block, column `0` of the second) is continuous and is `0` at `1`. By
     `character_eq_one_mem_nhds`, the set `C` of `g` with
     `ψ(g_(m_0, 0)) = 1` is a neighbourhood of `1`.
  4. `B.exists_compactOpenSubgroup_hasBlockIwahoriFactorization T` gives a
     compact open subgroup `K ⊆ O ∩ C` with a block Iwahori factorization.
  5. Every element of `Q̄ ∩ K` lies in `O`, so it fixes `v_1 ⊗ v_2` in the
     inducing representation of `Q̄`. Hence
     `Induction.compactDoubleCosetSection` at the point `1` with value
     `v_1 ⊗ v_2` is a section `f`. It is supported on `Q̄ K`, and
     `f(k) = v_1 ⊗ v_2` for all `k ∈ K`
     (`compactDoubleCosetSection_apply`).
  6. Let `L = {x | u(x) ∈ K}`. It is open and closed. It is compact, because
     it lies in the image of `K` under the continuous map that reads off the
     upper-right rectangle. It contains `0`.
  7. If `u(x) ∉ K`, then `f(u(x)) = 0`. Otherwise
     `compactDoubleCosetSection_support_subset` gives `l ∈ K` with
     `u(x) l⁻¹ ∈ Q̄`. Then `mem_of_mem_unipotentSubgroup_of_mul_inv_mem`
     (with the surjectivity part of the Iwahori factorization) gives
     `u(x) ∈ K`, a contradiction. So the restriction of `f` to the upper
     radical vanishes off the compact set `L` and has compact support.
  8. If `u(x) ∈ K`, then `f(u(x)) = v_1 ⊗ v_2`, and `ψ(x_(m_0, 0)) = 1`,
     because `K ⊆ C` and the corner entry of `u(x)` is `x_(m_0, 0)`
     (`upperRadical_index_zero_one`). Hence the integrand at `g = 1` equals
     the indicator of `L` times the constant `ℓ_1(v_1) ℓ_2(v_2)`.
  9. So `J(f)(1) = μ(L) ℓ_1(v_1) ℓ_2(v_2)` (`integral_indicator_const`, using
     the real measure of `L`). Here `0 < μ(L) < ∞`, since `L` is a nonempty
     open set and is compact. Both factors are nonzero.

- `isSmooth_twoBlockDeformedBlocks F ψ σ hσ u`: if every `σ i` has full
  standard Whittaker type
  (`IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i)`), then every
  deformed block `twoBlockDeformedBlocks F m σ u i` is smooth.

  *Proof.* Full Whittaker type includes admissibility, which includes
  smoothness. The deformed block is a twist by a determinant power with open
  kernel (`isOpen_ker_determinantComplexPower`), and `isSmooth_twist_iff`
  transfers smoothness.

- `exists_deformed_section_jacquetFunction_one_ne_zero F h ψ σ hσ ell hell u`:
  under the hypotheses of the previous lemma, for every complex `u` and every
  family of nonzero functionals `ℓ_i`, the statement of
  `exists_section_jacquetFunction_one_ne_zero` holds for the deformed blocks
  `twoBlockDeformedBlocks F m σ u`, that is, for sections of the deformed
  induction `ρ_u`.

  *Proof.* Combine the two previous results.

## Scope

The measure `μ` and the functionals `ℓ_i` are arbitrary, subject to the
stated hypotheses, and the section is chosen after `μ`. The module does not prove that `J(f)(g)` converges for
other sections, nor any statement about Whittaker models or the uniqueness of
Whittaker functionals.

The three block-subgroup facts listed above use the existing `Langlands.GeneralLinear.BlockShape` declarations from [OppositeBlockIntersection](../../Group/GL/OppositeBlockIntersection.md); this module defines no copies.
