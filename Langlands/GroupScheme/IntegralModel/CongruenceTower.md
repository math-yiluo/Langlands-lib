# Actual positive-level congruence towers of integral group models

This is an internal canonical extension of the published
`Langlands.GroupScheme.IntegralModel`, `IntegralModelReduction` and
`IntegralModel.LocalField` interfaces. It uses their existing actual schemes,
section groups, base-change point equivalences and integral-point map, together
with Mathlib's ideal powers and quotient homomorphisms. No additional
literature theorem is asserted or required for these construction laws.

The universe `u` is arbitrary. The construction works for a supplied
`M : IntegralModel R K G` over a local integral domain `R` with specified
fraction field `K`. In particular it applies directly to
`M : LocalFieldIntegralModel F G`, for
`F : Type u` with `Field F`, `ValuativeRel F`, `TopologicalSpace F` and
`IsNonarchimedeanLocalField F`. In this specialization `R` is literally
`↥𝒪[F]`, the actual valuation integer subring, and `K` is `F`, with its
existing subtype inclusion. No alternative integral ring, section group,
generic-point carrier or rational-point topology is introduced. There is no
characteristic restriction.

All levels are indexed by **positive naturals `ℕ+`**. Level zero is outside
this API. Put `m = IsLocalRing.maximalIdeal R`. The coefficient definitions are

- `congruenceRing R n = R ⧸ m ^ (n : ℕ)`;
- `congruenceQuotient R n`, the actual `Ideal.Quotient.mk (m ^ n)`;
- `congruenceBaseMap R n`, the contravariant `Spec.map` of this quotient;
- `M.congruenceFibre n`, the actual group-scheme pullback of `M.group` along
  `congruenceBaseMap R n`.

Thus the level group is the sections of the actual base-changed group over
`Spec (R / m^n)`, with the group law inherited from that group scheme.
`M.reductionAt n` is exactly the published `baseChangeSectionHom` along the
quotient spectrum map. `reductionAt_left` gives its literal scheme-map formula:
the pullback lift of the restricted integral section and the identity on the
quotient spectrum. This retains both projections and the original section.

The three subgroup constructions use the original maps:

- `M.congruenceKernelAt n = (M.reductionAt n).ker` inside `M.integralSections`;
- `M.congruenceSubgroupAt n = (M.congruenceKernelAt n).map M.integralPointMap`
  inside the original `rationalPoints G`;
- `M.congruenceInIntegralPointsAt n` is the same kernel's image under the
  surjective range restriction of `M.integralPointMap`, inside `M.integralPoints`.

The two literal membership laws state

```text
x ∈ M.congruenceKernelAt n ↔ M.reductionAt n x = 1

g ∈ M.congruenceSubgroupAt n ↔
  ∃ x : M.integralSections,
    M.reductionAt n x = 1 ∧ M.integralPointMap x = g.
```

The generic congruence subgroup lies in `M.integralPoints`. Kernel normality
and normality of its image under the surjective range restriction are proved.
`congruenceInIntegralPointsAt_eq_subgroupOf` identifies this latter subgroup
with `(M.congruenceSubgroupAt n).subgroupOf M.integralPoints`, giving the stated
normality with its ambient group explicit. No injectivity theorem for the
integral-point map is needed for this argument.

For `h : n ≤ k`, `congruenceRingTransition R h` is the actual quotient factor
`R / m^k → R / m^n`, induced by `m^k ≤ m^n`. Its composite with the level-`k`
quotient is the level-`n` quotient; the coefficient transitions are identities
at equal levels and compose in a tower. Their contravariant spectrum maps
satisfy the corresponding commutative triangle, identity and composition laws.

The auxiliary `GroupScheme.baseChangePointRestriction` constructs section
restriction between two actual pullbacks along any map of tests over their
common original base. It first uses `baseChangeBasePointsEquiv` to read an
actual pullback section as a point of the original group scheme, precomposes
with the map of tests, and uses the target inverse equivalence. It is a group
homomorphism because all three operations are group homomorphisms. The
projection formula describes precisely this precomposition. The section,
identity, composition and naturality laws are proved by the original
projection formulas and equality of the underlying over-morphisms.

`M.congruenceTransition h` specializes this construction to the actual
quotient factor map. `congruenceTransition_fst` gives its original-group
projection. The proved formula

```text
M.congruenceTransition h (M.reductionAt k x) = M.reductionAt n x
```

is the factorization of the actual reductions. Equal-level transitions are
identities and successive transitions compose. Applying this formula at the
identity proves `congruenceKernelAt_antitone`. Taking the same original
integral-point images proves `congruenceSubgroupAt_antitone`.

For a compatible model homomorphism `φ : M.Hom N f`,
`φ.congruenceFibreMap n` is its actual group-scheme base change to `R / m^n`.
`Hom.reductionAt_naturality` is the existing general base-change-section
naturality law. `Hom.congruenceTransition_naturality` says quotient restriction
commutes with these fibre maps. Reduction naturality preserves the integral
congruence kernels, and the original generic compatibility square
`Hom.integralPointMap_naturality` then proves preservation of their generic
congruence images under `rationalPoints.map f`.

At level one, `congruenceResidueRingEquiv R` is the canonical
`Ideal.quotEquivOfEq (pow_one m)` from `R / m^1` to
`IsLocalRing.ResidueField R = R / m`. Its composite with the level-one
quotient is literally the existing `IsLocalRing.residue R`.
`congruenceResidueBaseIso` is its spectrum isomorphism, and
`congruenceResidueTestIso` records its compatibility with the original base.
`M.congruenceResiduePointsEquiv` transports the actual level-one points to
the existing full special-fibre points by these canonical test and pullback
point equivalences. `congruenceResiduePointsEquiv_apply` identifies this
transport with restriction along that spectrum isomorphism. The proved
comparison formula is

```text
M.congruenceResiduePointsEquiv (M.reductionAt 1 x) = M.reduction x.
```

It identifies `congruenceKernelAt 1`, `congruenceSubgroupAt 1` and
`congruenceInIntegralPointsAt 1` with their published residue-level
counterparts. The entire special fibre is retained, including arbitrary
nonreductive or disconnected fibres.

These are intrinsic algebraic construction laws. The file proves no
compactness, openness, cofinality, quotient-reduction surjectivity, pro-p
property, model existence or identification with a building subgroup.
Smoothness, reductivity and connectedness are unnecessary for these laws.
The local-field neighborhood-basis target is a separate Prop-valued statement
on these same generic subgroups and the named `rationalPointTopology`.
