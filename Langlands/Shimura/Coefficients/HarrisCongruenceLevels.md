# Full Harris coefficient diagrams on CM-compatible levels

Author: Worker 57.

This module places the full coefficient reductions of
[HarrisReduction](HarrisReduction.md) on the actual CM-compatible topological
level tower of [HarrisLevels](../Unitary/HarrisLevels.md). The coefficient and
space diagrams use the same quotient-group functor. All levels, actions and
transitions are constructed from the original algebraic representation and
the original rational diagonal.

## Source and provenance

The original source is Michael Harris, *Galois properties of cohomological
automorphic forms on GL(n)* (1999), Section 3, printed pp. 306–308 (PDF
pages 8–10), and Section 4, printed pp. 308–310 (PDF pages 10–12).
Its registered ID is
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, with SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.
These passages were read.

Section 3 uses the whole coefficient algebra over a rational completion, a
stable integral lattice, finite coefficient modules and normal congruence
levels. Section 4 specifies the imaginary quadratic subfield, the induced
CM type and the unitary Shimura datum before discussing the particular
levels and uniformization (4.1)–(4.3). The constructions here are derived
algebraic and topological prerequisites, rather than a transcription of
the uniformization or the function-space comparison (3.8).

The module specializes the published constructions
`congruenceCoefficientDiagram`, `congruenceLevelTower`,
`congruenceLevelSpaces`, `congruenceLevelProjection` and
`congruenceContinuousLevelSpaces`. Their provenance and generic proofs are
in [CongruenceDiagram](CongruenceDiagram.md),
[CongruenceLevels](CongruenceLevels.md) and
[NormalLevelContinuous](../NormalLevelContinuous.md).

## Full coefficient and level diagrams

Fix a finite-dimensional rational algebra `A` with involution `σ`, a number
field `L`, a finite-dimensional `L`-module `W`, an algebraic representation
`ρ : (σ.baseChange L).AlgebraicRepresentation W`, a rational finite place
`p` and a compact open level `U` in `σ.FiniteAdelicPoints`. The types `A`,
`L` and `W` share a universe.

Write `R = HarrisCoefficientIntegers L p` for the actual product of completed
integer rings at all coefficient places above `p`, `Λ` for the constructed
full stable lattice, and `I = harrisCoefficientScalarIdeal L p m = (m)`.
For an exponent `n`, let `K_n` be the kernel of the original `U.subgroup`
action on `Λ / I^n Λ`. The shared group diagram
`harrisCongruenceGroups ρ p U m` has term `U.subgroup / K_n`; its maps are
induced by the identity on the original compact group.

`harrisCoefficientDiagram` is an `EquivariantDiagram` in `ModuleCat R` over
this group diagram. Its underlying module functor is exactly
`harrisTorsionSystem` followed by the original-action forgetful functor
(`harrisCoefficientDiagram_obj`). The action agrees on every element with
`harrisFiniteCoefficientAction`, retaining the integral scalar structure
(`harrisCoefficientDiagram_action`). The proof reduces a quotient-group
element to a representative, where the actions coincide. Every coefficient
transition is the actual surjective ideal-power reduction map
(`harrisCoefficientDiagram_transition_surjective`). Integral scalars give a
common module category across the different quotient coefficient rings.

For `m ≠ 0`, `harrisCongruenceLevels` constructs a functor from `ℕᵒᵖ` to
actual compact open adelic levels. Its term is the ambient subgroup image
of `K_n`; openness comes from the proved full-kernel openness theorem.
`harrisCongruenceLevels_obj_subgroup` identifies this subgroup.
For `g : U.subgroup`, `mem_harrisCongruenceLevels` proves that its ambient
image belongs to the new level exactly when it belongs to every component
coefficient kernel at every actual place above `p`. The proof combines
subgroup-image membership with the full-kernel characterization.
`harrisCongruenceLevelInclusion` is the actual ambient inclusion arrow
back to `U`. The level functor includes all natural-number exponents.

## Actual CM-compatible Harris spaces

Let `D : CentralSimpleUnitaryData E K A n`, with `E` totally real, `K`
totally complex and quadratic over `E`, and with the scalar towers stated
in the Lean file. Let `h : HasHarrisSignature D.toSecondKindInvolution n`.
Thus the original algebra has signature `(n-1,1)` at one real place and
`(n,0)` elsewhere. Let `F` be an actual imaginary quadratic field, with
an embedding `ιF : F →+* K` and a chosen complex embedding `τ₀`.
The `harrisCMSection` constructed from these embeddings determines the
CM-compatible signature charts used here.

`coefficientRationalFinite` proves `Module.Finite ℚ A` from the finite
dimension of `A` over the number field `K`, by transitivity of finite
dimension. The coefficient constructors explicitly request that typeclass;
this lemma supplies it from `D` without a new mathematical assumption.

For `ρ` a representation of the rational involution of `D`, define
`X` to be the `Domain` of
`HarrisSignatureCharts.ofSignature h (isCMSection_harrisCMSection E ιF τ₀)`.
`harrisCoefficientCongruenceSpaces` is an `EquivariantDiagram` in `TopCat`
over exactly the same `harrisCongruenceGroups`. Its term is the actual
double quotient of `X × G(𝔸_f)` by the rational group and the constructed
coefficient level, with its quotient topology and the original
`finiteAdelicDiagonal`. There is no arbitrary domain or diagonal argument
in this Harris specialization.

`harrisCoefficientCongruenceSpaces_obj` identifies the complete underlying
space functor with `harrisCongruenceLevels` followed by
`harrisUnitaryLevelTower D h ιF τ₀`. For `m ≠ 0`, the `_group_finite` and
`_coefficient_finite` lemmas prove that both the residual group and the
paired coefficient object are finite, using the full-lattice results.

For an inverse-index arrow from exponent `j` to exponent `i`, the space
transition sends `[x,a]` to `[x,a]` at the coarser level
(`harrisCoefficientCongruenceSpaces_map_mk`). The residual class of
`g : U.subgroup` acts by `[x,a] ↦ [x,a g⁻¹]`
(`harrisCoefficientCongruenceSpaces_action_mk`). This inverse right
translation is the geometric action convention. Equivariance of transitions
is part of the constructed `EquivariantDiagram`, proved by the generic
normal-level maps; it is not an extra hypothesis.

`harrisCoefficientCongruenceProjection` is a natural transformation to
the constant original Harris `U`-level. Each component is a continuous,
surjective forgetful map, and is invariant under the full residual
coefficient group. The `_surjective` and `_invariant` lemmas reuse the
proved generic normal-level projection identities.

`harrisCoefficientContinuousLevelSpaces` retains the original group
`U.subgroup` and constructs a functor to `ContAction TopCat U.subgroup`.
Joint continuity follows from the open normal kernels: their quotient
groups are discrete, so the residual actions by continuous maps are jointly
continuous; restriction along the continuous quotient homomorphism gives
the original compact-level action. Transitions are continuous equivariant
maps. Its `_obj` lemma identifies its underlying spaces with the preceding
actual Harris double quotients.

## Scope

The finite image groups act faithfully on the coefficient reductions by
the imported full-kernel theorem. No faithfulness or freeness of their
geometric actions is inferred. Rational stabilizers remain in the double
quotients. No separating or cofinal family of levels, finite fibers,
covering or torsor assertion follows from this construction. In
particular these coefficient kernels can contain a permanent representation
kernel and need not be Harris's independently chosen separating tower.
At exponent zero the coefficient module and image group are trivial and
the compact open level is the original level.

This module supplies the coherent actual coefficient and space diagrams
and their continuous actions. Associated local systems and their descent,
the function-space comparisons of Section 3, the special local factors of
(4.1)–(4.2), uniformization (4.3), scheme levels and canonical models remain
separate obligations of their assigned constructions.
