# Common fixed-level coefficient support on the rational norm kernel: proof

`Langlands.CuspidalSupport.rationalNormKernelUniformSupport` proves exactly
`Langlands.CuspidalSupport.RationalNormKernelUniformSupportStatement.{uF, uV}`
(module `Langlands.Representation.CuspidalSupport.RationalNormKernelUniformSupportStatement`),
with the field universe `uF` and the representation-carrier universe `uV`
independent. [Statement](RationalNormKernelUniformSupportStatement.md)

The theorem has no hypotheses. Its scope is the whole statement: every
nonarchimedean local field of any characteristic, every connected reductive
group scheme `G`, every maximal split torus `i` and generic cocharacter `ν`,
with the statement's canonical rational-point topology, local compactness,
`NonarchimedeanGroup` and Hausdorff premises, standard-cocharacter statement,
relative-root-system realization and closed unipotent point subgroups. Rank
zero and an empty simple-root type are included. For every compact open
subgroup `K` of the actual `Plancherel.rationalCommonNormKernel G`, with its
inherited topology, the conclusion is
`CompactCoefficientClass.HasUniformFixedLevelCoefficientSupport K.toSubgroup`:
one compact subset of the kernel, chosen first, contains the support of
`g ↦ ℓ (π(g⁻¹) v)` for every `IrreducibleCompactCoefficientRep` `π` of the
kernel, every `K`-fixed vector `v` and every `K`-invariant algebraic-dual
functional `ℓ`. The axioms of the theorem are `propext`, `Classical.choice` and
`Quot.sound`.

## The Lean term

```
rationalNormKernelUniformSupport_of_joint.{uF, uV}
  BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence.{uF}
```

- `Langlands.BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence`
  (module `Langlands.BruhatTits.SpecialCompact.JointBasisProof`) proves
  `JointSpecialCompactBasisExistenceStatement.{u}` for every universe `u`,
  without hypotheses: Renard V.5.1–V.5.2 at one geometric special vertex.
  [Joint witness](../../BruhatTits/SpecialCompact/JointBasisProof.md)
- `Langlands.CuspidalSupport.rationalNormKernelUniformSupport_of_joint`
  (module `Langlands.Representation.CuspidalSupport.RationalNormKernelSupportGeometry`)
  proves `JointSpecialCompactBasisExistenceStatement.{uF} →
  RationalNormKernelUniformSupportStatement.{uF, uV}`.
  [Reduction](RationalNormKernelSupportGeometry.md)

The reduction is instantiated at `.{uF, uV}` and the joint basis theorem at
`.{uF}`.

## The implemented argument

The argument applied works with representations of the norm kernel itself. It
uses no ambient irreducible representation, no extension of a kernel
representation, no restriction decomposition and no ambient compact-mod-centre
coefficient bound. All comparisons between the ambient group and the kernel are
geometric: subgroups, levels and Cartan charts are carried through the actual
inclusion `Plancherel.rationalCommonNormKernel G → G(F)`. Write `H` for this
kernel.

**1. One geometric package.** After `IsAffineHom` is taken from connected
reductivity, `finite_simpleRoot` gives finiteness of the simple roots of
`(i, ν)`, and a `Fintype` instance is chosen. Then
`NormKernelUniformSupportGeometry.nonempty_of_joint` applies the joint witness
at the given `G`, `T`, `i`, `ν`. It obtains an apartment datum `D`, a special
vertex `x`, the represented centralizer `j`, the torus factorization `s` with
`s ≫ j = i`, the bijective restriction evaluation, the special compact
properties of `K0 := D.specialCompactSubgroup x` (from which compactness of `K0`
in the canonical point topology is taken), the same-compact standard-Levi
compatibility and `SimultaneousStandardBasisAt i ν K0`. Corrected fundamental
cocharacters `d` come from `nonempty_normKernelFundamentalCocharacters`. From the
compatibility, `exists_isFiniteLatticeTransversal` gives a finite lattice
transversal, and `exists_finite_centralCartanFactorization` gives one finite
residual set `R ⊆ G(F)` and, for every ambient point `g`, an expression
`g = k₁ * (d.orthantHom(n) * f) * k₂ * z` with `k₁, k₂ ∈ K0`, `f ∈ R` and `z` in
the centre of `G(F)`. The same `K0` carries the basis and the chart. Other
clauses of the joint witness are not used.

**2. A common level below `K`.** `NormKernelUniformSupportGeometry.hasUniformSupport`
is applied to the prescribed `K` (only its openness is used).
`nonempty_normKernelCompressionLevel` maps `K` into the ambient group, using
openness of `H` in the canonical topology (`isOpen_rationalCommonNormKernelConditional`,
from the statement's nonarchimedean and local-compactness premises), and
chooses a member `K₁` of the simultaneous basis inside that ambient open
subgroup. The level is `L = K₁ ∩ H`, the preimage of `K₁` under the inclusion.
It is open in `H`, contained in `K`, and compact because its image under the
inclusion is exactly the compact `K₁`. Normality of `K₁` in `K0` makes
`K0 ∩ H` normalize `L`. The record `NormKernelCompressionLevel` also keeps,
for the minimal standard face, the ordered factorization of `L` into opposite
radical, Levi and radical parts, membership of the whole orthant
`d.orthantHom` in `Hecke.iwahoriPositiveMonoid`, and forward conjugation
preservation of `L ∩ Levi`. Radicals, Levis and opposite radicals of `H` are
the preimages of the actual standard unipotent and Levi point subgroups.

**3. Measure.** `H` receives its Borel σ-algebra and the Haar measure
`Measure.haar`. `H` is locally compact because it is open in the locally
compact ambient group (`isOpen_rationalCommonNormKernel`). The measure is
internal to the proof; the conclusion mentions none.

**4. Hecke sandwich on the kernel.** `hasUniformSupport_of_centralCartanCover`
(module `RationalNormKernelSupportSandwich`) first proves `ambient_normalized`:
compact subgroups lie in `H` (`compactSubgroup_le_rationalCommonNormKernel`), so
`K0` normalizes the image of `L`. `Plancherel.exists_rationalNormKernel_residual_cover`
uses closedness of `H` and compactness of `H ∩ Z(G(F))` to restrict the ambient
central chart to `H`: it gives a compact subgroup `Γ ≤ H` normalizing `L` and a
finite `R' ⊆ H` such that every element of `H` is `γ * (d.orthantHom(n) * r) * γ'`
with `γ, γ' ∈ Γ`, `r ∈ R'`. Injectivity of the inclusion identifies the
preimage of the image of `L` with `L`.
`Hecke.nonempty_fixedLevelSandwich_of_residual_iwahoriCartan` then constructs
`Hecke.FixedLevelSandwich` data in the corner algebra
`HeckeAlgebra.Corner μ L` of the compact open level `L` of `H`: finitely many
edge elements and finitely many commuting middle elements whose sandwich
products span the corner. These data are chosen before any representation.

**5. Common support at `L`.**
`CompactCoefficientClass.hasUniformFixedLevelCoefficientSupport_of_sandwich`
(module `CompactCoefficient.FiniteStratumUniformSupport`) turns the sandwich
into `HasUniformFixedLevelCoefficientSupport L.toSubgroup`. By
`fixedStratum_finite_of_sandwich` and `sandwichSimpleModuleDimensionBound`, the
classes of compact irreducible smooth representations of `H` with a nonzero
`L`-fixed vector form a finite set; this uses the simplicity of the fixed space
as a corner module and separating corner elements, not common support. For one
representative of each class, `finiteDimensional_fixedVectors` gives a finite
basis of its `L`-fixed space. The coordinate functionals, extended by averaging
over `L`, are `L`-invariant and therefore smooth dual vectors; the compactness
predicate of `IrreducibleCompactCoefficientRep`, which concerns every smooth
dual vector, makes their inverse coefficients against the basis compactly
supported. The union of these supports is one compact set for the
representative. Every `L`-invariant algebraic-dual functional is unchanged by
the normalized projection onto `L`-fixed vectors, so all its inverse
coefficients against `L`-fixed vectors vanish outside that union. The bound of
the chosen representative moves to every representation of the same class
along the representation equivalence given by `ofRep_eq_iff`
(`fixedLevel_support_of_equiv`). The finite union over the classes is the
common compact set; a representation whose `L`-fixed space is zero has zero
coefficients.

**6. From `L` back to `K`.** Since `L ≤ K`, every `K`-fixed vector is
`L`-fixed (`fixedVectors_antitone`) and every `K`-invariant functional is
`L`-invariant. The same compact set therefore bounds the coefficients at `K`.
This is the conclusion for the prescribed `K`.

The closed-unipotent premise of the statement and the compactness of `K` are
not used.

## Comparison with the source

The statement is the class-uniform coefficient-support step of David Renard,
*Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, VI.3.4, printed pp.145–146 / PDF pp.151–152 (source ID
`renard-2026-representations-groupes-reductifs-padiques`). Renard places an
irreducible kernel representation inside the restriction of an ambient
irreducible (remark after VI.2.3), bounds ambient coefficients modulo the centre
uniformly at a fixed level (VI.2.4) and deduces compact support on the kernel
(VI.2.1(b)⇒(c)). The Lean proof takes a different route that stays on the
kernel: finite Hecke sandwich generation at a small level (the mechanism of
Renard V.5.3 and the dimension argument of VI.2.3–VI.2.4), finiteness of the
fixed-level classes in the manner of Bernstein–Zelevinsky (1976) 4.16, and a
finite union of individual compact supports.
