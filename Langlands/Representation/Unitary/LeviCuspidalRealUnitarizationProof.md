# Real unitarization of irreducible cuspidal product-Levi representations

Author: Worker 862.

`Langlands.leviCuspidalRealUnitarization` proves the published proposition
`Langlands.LeviCuspidalRealUnitarizationStatement.{uF,uV}`. Its type is
exactly that proposition, with the field universe `uF` and the carrier
universe `uV` independent. The proof takes only the statement's two
hypotheses, `Representation.IsIrreducible ρ` and
`CuspidalSupport.IsLeviCuspidal D ρ`. It produces a real exponent vector `t`
and an actual `InvariantPositiveForm` on the original carrier `V` for the
`+t` twist `T.leviRealPowerTwist D t ρ`. No hypothesis is added on `ρ`, `V`,
the central character, the coefficients or the exponent.

## Auxiliary results in this module

**Compact support modulo the center from a finite-index subgroup.**
`Langlands.UnitaryCentralCharacter.hasCompactSupport_coefficientNorm_of_finiteIndex`
is stated for an abstract topological group `G` with Hausdorff central
quotient `G ⧸ Z`, where `Z = Subgroup.center G`. It assumes a representation
`ρ` with a unitary central character `c`, a normal subgroup `H` such that
`H ⊔ Z` has finite index, and a functional `ℓ` whose coefficients
`h ↦ ℓ (ρ h w)` on `H` are compactly supported for every `w`. It concludes
that the descended coefficient norm `c.coefficientNorm ℓ v` on `G ⧸ Z` has
compact support for every `v`.

The proof picks a representative `r j` of every coset `j` of `N = H ⊔ Z`.
The candidate compact set `K` is the finite union, over `j`, of the images of
the topological supports of `h ↦ ℓ (ρ h (ρ (r j) v))` on `H` under the
continuous map `h ↦ [h * r j]`. Let `g` be any element and `j` its coset.
Normality of `H` writes `g = h' * r j * z` with `h' ∈ H` and `z ∈ Z`. The
published `norm_matrixCoefficient_mul_center` removes `z`, because the
central character is unitary. Then the value of the coefficient norm at
`[g]` is `‖ℓ (ρ h' (ρ (r j) v))‖`. If this value is nonzero, `h'` lies in
the `j`-th support and `[g] = [h' * r j]` lies in `K`. `HasCompactSupport.intro`
then gives compact support.

**Center of the product Levi.** In the namespace
`Langlands.LeviCuspidalRealUnitarization`:

- `blockScalarLevi_mem_center` and `exists_blockScalarLevi_eq_of_mem_center`
  identify `Subgroup.center (D.Levi F.Carrier)` with the block-scalar tuples
  `D.blockScalarLevi F.Carrier a`. They use Mathlib's `Subgroup.center_pi`
  and `Matrix.GeneralLinearGroup.center_eq_range_scalar` blockwise.
- The imported `Langlands.Parabolic.blockScalarCenter` from
  [BlockScalarCenter](../../Group/GL/BlockScalarCenter.md) is the codomain
  restriction of `D.blockScalarLevi` to the center. It replaces the identical
  local map. `continuous_blockScalarCenter` proves it continuous from the
  coordinatewise continuity of scalar matrices. Below, `blockScalarCenter`
  refers to this shared declaration.

**The twist on the determinant-unit subgroup.**
`leviRealPowerTwist_comp_determinantUnitInclusion` shows that restricting
`T.leviRealPowerTwist D t ρ` to `CuspidalSupport.determinantUnitSubgroup T D`
gives `CuspidalSupport.determinantUnitRestriction T D ρ`. On that subgroup
every block determinant is a unit. So the published
`normOneLevi_le_ker_leviRealPowerCharacter` makes the real character equal to
`1` there.

**Exponent choice.** `exists_leviRealPowerTwist_unitaryCentralCharacter`
takes a locally constant character `χ` of the center by which `ρ` acts. It
produces `t` and a `UnitaryCentralCharacter` of the `+t` twist. For each
block `i`, let `ψᵢ = χ ∘ blockScalarCenter ∘ Pi.mulSingle i`. This is a
character of `F.Carrierˣ` whose kernel is open, by local constancy of `χ`
and continuity. The published `smoothCharacterNormDecomposition` gives a
real `cᵢ` with `‖ψᵢ a‖ = |a|_F ^ cᵢ`. Set `tᵢ = -cᵢ / nᵢ`, where
`nᵢ = D.size i > 0`. The twisted central character is the restriction `ψt` of
`T.leviRealPowerCharacter D t` to the center, multiplied by `χ`. Its kernel
contains the intersection of two open kernels, so it is open.

For the norm, write a central `z` as `blockScalarLevi a`. Then
`coe_leviRealPowerCharacter_blockScalar` gives
`‖ψt z‖ = ∏ᵢ |aᵢ|_F ^ (nᵢ tᵢ)`, since every factor is nonnegative. The
homomorphism `χ ∘ blockScalarCenter` maps the commutative group
`Fin D.length → F.Carrierˣ` to `ℂˣ`, and `a = ∏ᵢ Pi.mulSingle i (aᵢ)`.
Hence `‖χ z‖ = ∏ᵢ |aᵢ|_F ^ cᵢ`. Each exponent `nᵢ tᵢ + cᵢ` is zero, so the
product of the norms is `1`. The action identity follows from the twist
formula and the scalar action of `χ`.

## The main proof

Fix `p`, `F`, `T`, `n`, `D`, `V` and `ρ` with the two hypotheses. The Levi
topology is the one the statement installs.

1. **Central character.** Admissibility gives smoothness. The published
   `admissibleSchur_centralCharacter` gives a locally constant `χ` on the
   center with `ρ z v = χ z • v`. The exponent lemma above gives `t` and a
   unitary central character `c` of `ω = T.leviRealPowerTwist D t ρ`.
2. **Properties of `ω`.** `isSmooth_leviRealPowerTwist_iff` gives
   smoothness of `ω`. The published `isIrreducible_twist_iff` gives its
   irreducibility.
3. **A nonzero smooth functional.** The Levi is nonarchimedean and locally
   compact, by `T.leviNonarchimedean D` and `T.leviLocallyCompactSpace D`.
   So `compactOpenSubgroupBasis` shows that compact open subgroups are
   cofinal among open subgroups. Then
   `exists_nonzero_smoothDual_of_irreducible_compact_cofinal` gives a
   nonzero smooth functional `ℓ` for `ρ`.
4. **Compact coefficients on the determinant-unit subgroup.** The published
   `CuspidalSupport.leviHarishChandraTheorem`, applied to `SmoothRep.of ρ`,
   turns quasicuspidality (`hcusp.2`) into compactly supported coefficients
   of `determinantUnitRestriction T D ρ` for every smooth dual vector.
   `isSmoothVector_comp` shows that `ℓ` stays smooth after restriction.
   By the twist-restriction lemma, the coefficients of `ω` restricted to the
   determinant-unit subgroup are compactly supported.
5. **Compact support modulo the center.**
   `CuspidalSupport.leviDeterminantUnitStructure` gives finite index of
   `determinantUnitSubgroup ⊔ center`. `glBlockCentralQuotientTopology`
   makes the central quotient `Q` a Hausdorff, locally compact topological
   group. The finite-index lemma then gives compact support of every
   coefficient norm `c.coefficientNorm ℓ v` on `Q`.
6. **The invariant form.** Give `Q` its Borel σ-algebra and the measure
   `μ = (Measure.haar).inv`. This measure is right invariant, positive on
   open sets and finite on compact sets. Each coefficient norm is continuous,
   by `continuous_coefficientNorm` and smoothness of `ω`, and has compact
   support. So `Continuous.memLp_of_hasCompactSupport` puts it in `L²(μ)`.
   The published `UnitaryCentralCharacter.coefficientProductForm` integrates
   coefficient products of the nonzero `ℓ` over `Q` against `μ`. It returns
   the required `InvariantPositiveForm ω` on `V`.

The right Haar measure avoids any unimodularity argument for the Levi or its
central quotient. The proof does not prove or use square-integrability as a
separate statement; compact support gives the `L²` bound directly.

## Scope and independence

The proof uses only proved Library theorems and Mathlib. Its `Langlands`
import closure contains none of the following: the positive-root unitary
cuspidal support target of task `9af5b508` or its parent statement, joint
support, regular head or exhaustion, tempered exhaustion, the
square-integrable or ordered-segment classifications, or any consumer of
this unitarization step. The only modules from `Classification` that it
imports are the low-level `Supercuspidal` definitions and their contragredient
statement and auxiliaries. They come in through `CuspidalSupport.LeviDefinitions`,
which the target statement itself imports, and through
`Smooth.SmallRealizationProof`. The statement pair is unchanged. The shared
block-scalar map was extracted unchanged into a group-level module, so its
reuse adds no Jacquet or classification dependency. The proof uses no `sorry`,
no proof holes and no new axioms.

## Provenance

The mathematical route is Casselman, *Introduction to the theory of
admissible representations of p-adic reductive groups* (1995; registered
`casselman-1995-admissible-representations`), adapted to the product Levi.
Lemma 5.2.5 (p.48) removes the norm of the central character by a positive
character; here this is the explicit block-scalar exponent choice. Theorem
5.2.1 (pp.46–47) gives compactness modulo the center of cuspidal coefficients;
here the Library's Harish-Chandra theorem gives compactness on the
determinant-unit subgroup, and the finite-index lemma passes to the center.
Proposition 2.5.4 (pp.28–29) builds the form by integrating coefficient
products over `G/Z`; here the published `coefficientProductForm` does this.
The finite-index passage, the blockwise description of the center and the
use of a right Haar measure are internal derivations, not text in the source.
