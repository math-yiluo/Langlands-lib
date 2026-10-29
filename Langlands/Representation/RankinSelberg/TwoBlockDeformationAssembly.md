# Assembly of the entire deformation from the analytic input

Module `Langlands.Representation.RankinSelberg.TwoBlockDeformationAssembly`,
namespace `Langlands.RankinSelberg.TwoBlockDeformation`.

This is a helper module for the proof of
`Langlands.RankinSelberg.TwoBlockWhittakerDeformationStatement`. Its main
results depend on two hypotheses. The first is the proposition
`NormalizedProductWhittakerTypeStatement`, which is not yet proved in the
Library. The second is the analytic interface `FlatCoefficientDifferentiable`
of `TwoBlockDeformationAnalytic`. Given these, the module derives the four
clauses of the target. The second hypothesis is proved in
`TwoBlockDeformationAnalytic` (theorem `flatCoefficientDifferentiable`). The
last theorem of this module, `twoBlockWhittakerDeformationStatement_of_normalizedProduct`,
discharges it. That theorem is still conditional on
`NormalizedProductWhittakerTypeStatement`, so this module does not prove the
target.

## Provenance

The target is the lemma of JPSS 1983 (source ID `jpss-1983-rankin-selberg`),
Section (4.5), printed pages 408–409, in its inverse-character form. The
target's own Markdown file describes its conventions. JPSS use the Jacquet
integral (4.6.2), printed page 411, to produce the Whittaker functional on
`σ_u`. Their holomorphy argument refers to Casselman–Shalika (source ID
`casselman-shalika-1980-whittaker`), Section 2. This module does not formalize
any source proof directly. Its route is internal. It defines `J_u` as an
extension of the Jacquet integral from the compact-radical sections, made by
averaging over characters, and then combines the separately proved pieces
listed below.

## Notation

Let `T = F.canonicalTopologicalData` and give `F.Carrier` the topology
`T.topology`. Let `ρ_u = twoBlockDeformedInduced F m h σ u` be the actual
lower normalized induction of the deformed blocks
`σ_u = twoBlockDeformedBlocks F m σ u`. Its carrier is
`Sections F h σ_u`. Let `V'_u = compactRadicalSubmodule F h σ_u` be the
submodule of sections whose restriction `x ↦ f(u(x))` to the upper radical
has compact support (module `TwoBlockDeformationCell`). Let `N` be the upper
unipotent group of `GL_(t+1)`, and let `χ = inverseStandardCharacter ψ t`.

## `exists_jacquetFunctional`

Fix blocks `σ`, block functionals `ell i ∈ glInverseFunctionals ψ (m i) (σ i)`,
a measurable structure on `F.Carrier` with measurable addition and
multiplication, and a Borel additive Haar measure `μ` on the upper radical.
Make two assumptions:

- some compact-radical section `f` has `jacquetFunction ψ ell μ f 1 ≠ 0`;
- any two inverse-character functionals on `inducedRep F h σ` satisfy
  `φ.val = c • φ'.val` whenever `φ'.val ≠ 0`.

Then there is `J : glInverseFunctionals ψ t (inducedRep F h σ)` with three
properties. First, `J.val f = jacquetFunction ψ ell μ f 1` for every
compact-radical section `f`. Second, `J.val ≠ 0`. Third,
`relations (inducedRep F h σ) N χ ⊔ compactRadicalSubmodule F h σ = ⊤`.

Proof. Every compact-radical section has an integrable integrand
(`isAbsIntegrableAt_one_of_mem_compactRadicalSubmodule`). So the integral
defines a linear form `J' = compactRadicalJacquet` on `V'`. The submodule `V'`
is stable under `N` (`inducedRep_mem_compactRadicalSubmodule`), and `J'` is
`χ`-equivariant there (`compactRadicalJacquet_inducedRep`). The induced
representation is smooth (`isSmooth_normalizedOppositeParabolicInduced`), and
`χ` has open kernel (`isOpen_ker_inverseStandardCharacter`). The group `N` has
an increasing exhaustion by compact open subgroups
(`exists_upperUnipotent_exhaustion`). With these inputs, the
character-averaging results of `Langlands.Jacquet.Localization` (module
`Langlands.Representation.Jacquet.CharacterAveraging`) apply.
`apply_eq_zero_of_mem_relations` shows that `J'` vanishes on the relations
lying in `V'`. `exists_functional_extension` then extends `J'` to an
equivariant form `J` on the whole space. The assumed section gives `J ≠ 0`.
`relations_sup_eq_top` gives the spanning statement from the uniqueness
assumption and `J' ≠ 0`.

## `exists_deformation_of_functionals`

This is the purely algebraic step. Let `J u` be inverse-character functionals
on `ρ_u` for every `u : ℂ`, with `(J u).val ≠ 0` for all `u`. Assume that every
inverse-character functional `ℓ` on `ρ_0` satisfies `ℓ.val = c • (J 0).val`
for some `c`. Let `ℓ₀` be one with `ℓ₀.val ≠ 0`, and let `v₀` be a section of
`ρ_0`. Write `f_u = flatSection F h σ u v₀` for the flat family (module
`TwoBlockDeformationFlat`). Assume that `u ↦ (J u).val (ρ_u(g) f_u)` is
differentiable on `ℂ` for every `g`. Then the conclusion of the target holds
for `ℓ₀` and `v₀`.

Proof. Write `ℓ₀.val = c • (J 0).val`; then `c ≠ 0` because `ℓ₀.val ≠ 0`.
Set `W_u(g) = c · (J u).val (ρ_u(g) f_u)`. The four clauses follow:

1. `f_0 = v₀` (`flatSection_zero`), so `W_0(g) = ℓ₀.val (ρ_0(g) v₀)`.
2. At each `u`, the functional `c • J u` is nonzero and `W_u` is its
   coefficient at the vector `f_u`.
3. `exists_uniform_stabilizer` gives one compact open subgroup `K` that fixes
   every `f_u`. Since `ρ_u(g k) = ρ_u(g) ρ_u(k)`, this gives
   `W_u(g k) = W_u(g)` for all `u`, `g` and `k ∈ K`.
4. For each `g`, the function `u ↦ W_u(g)` is a constant multiple of a
   function differentiable on all of `ℂ`, so it is analytic at every point
   (`Differentiable.analyticAt`).

## `exists_deformation_of_differentiable`

Hypotheses: `H : NormalizedProductWhittakerTypeStatement.{uF,uW}`, blocks `σ`
of full standard Whittaker type,
`hA : FlatCoefficientDifferentiable F h σ ψ`, a nonzero inverse-character
functional `ℓ₀` on `ρ_0`, and a section `v₀`. The conclusion is the
target's existential statement for `ℓ₀` and `v₀`, with all four clauses.

Proof. Give `F.Carrier` its Borel structure. The canonical topology is second
countable, so the matrices of the upper radical have the product Borel
structure. Choose an additive Haar measure `μ` on them. For each block choose
a nonzero inverse-character functional `l i`
(`exists_block_inverse_functional`) and set `ell i = (l i).val`. The same
`ell i` is a functional for every deformed block
(`deformedBlockFunctional`). For each `u`,
`exists_deformed_section_jacquetFunction_one_ne_zero` supplies the nonzero
compact-radical section. `functional_eq_smul`, which uses `H`, supplies
uniqueness on `ρ_u`. So `exists_jacquetFunctional` gives `J u` with the three
properties above. These are exactly the hypotheses of `hA`, so `hA` gives the
differentiability of the flat coefficients.
`exists_deformation_of_functionals` then finishes, using `functional_eq_smul`
at `u = 0`.

## `twoBlockWhittakerDeformationStatement_of`

This theorem concludes the closed proposition
`TwoBlockWhittakerDeformationStatement.{uF,uW}`. It assumes `H` and, for every
prime `p`, field `F`, character `ψ`, rank data and blocks `σ` of full standard
Whittaker type, `FlatCoefficientDifferentiable F h σ ψ`. The proof introduces
the target's quantifiers and applies `exists_deformation_of_differentiable`.
The theorem is conditional; it does not discharge the target.

## `twoBlockWhittakerDeformationStatement_of_normalizedProduct`

This theorem concludes `TwoBlockWhittakerDeformationStatement.{uF,uW}` from
`H : NormalizedProductWhittakerTypeStatement.{uF,uW}` alone. It applies
`twoBlockWhittakerDeformationStatement_of H`, supplying the analytic
hypothesis by `flatCoefficientDifferentiable F h σ ψ` for each field,
character, rank data and blocks. The full-Whittaker-type premise on the blocks
is not needed for that step. Once a proof of `H` is published, the target is
this theorem applied to that proof. Until then, this theorem is conditional on
`H` and does not discharge the target.
