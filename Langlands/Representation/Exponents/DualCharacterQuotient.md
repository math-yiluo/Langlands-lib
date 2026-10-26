# Dual-detected character quotients and central defect images

Author: Worker 531.

This is a derived algebraic construction over the published objects in
`Exponents.DualJacquet`. It constructs the actual annihilator quotient and
central-defect images with their full ambient group actions. Every assertion
below is an intrinsic construction law proved in the paired Lean file.

## Generic central action

The namespace `Langlands.DualCharacterQuotient` uses a commutative ring `R`,
an arbitrary group `G`, a commutative group `H`, an `R`-module `V`, and
`ρ : Representation R G V`. The ring, both groups and the carrier have
independent universes. The supplied homomorphism `ι : H →* G` has central
image, witnessed by `hι : ∀ a, ι a ∈ Subgroup.center G`, and
`χ : H →* Rˣ` is arbitrary.

`dualSpace ρ ι χ` is exactly the published
`generalizedCommutativeCharacterSpace (commutativeTranspose (ρ.comp ι)) χ`.
Writing this space as `E`, its members are algebraic dual functionals with a
finite uniform character-defect order for each functional. No uniform bound
on the whole space is required. The transpose action satisfies
`(a · φ)(v) = φ(ρ(ι a)v)`, with no character inversion or conjugation.

`dualTranslate` is precomposition by `ρ(g)`, bundled as an intertwiner of the
transpose `H`-action. Centrality proves its intertwining equation;
`dualTranslate_mem` then applies the published functoriality of generalized
central character spaces. Thus `E` is stable under this precomposition for
every `g : G`.

`annihilator ρ ι hι χ` is a `Subrepresentation ρ` whose underlying submodule
is `E.toSubmodule.dualCoannihilator`. `mem_annihilator` states exactly

```
v ∈ K ↔ ∀ φ : Module.Dual R V, φ ∈ E → φ(v) = 0.
```

The invariance proof applies this equation to `φ ∘ ρ(g)` using
`dualTranslate_mem`. It retains the entire `G`-action.
`quotient ρ ι hι χ : Rep.{uV} R G` is the actual module quotient `V / K`
with the induced action. `quotientMap` is its actual `G`-intertwining quotient
map `q`, and `quotientMap_surjective` proves surjectivity.
`quotientMap_eq_zero_iff` identifies `q(v) = 0` with the same annihilation
condition.

`evaluation` descends each `φ ∈ E` to a linear functional on this quotient.
`evaluation_quotientMap` proves `evaluation φ (q(v)) = φ(v)`.
`eq_zero_iff` proves separation on every quotient element:

```
c = 0 ↔ ∀ φ : E.toSubmodule, evaluation φ c = 0.
```

The proof chooses a preimage under `q` and uses the quotient's defining
annihilator. It does not identify the entire dual of the quotient with `E`.

## Defects and their actual images

For `a : H`, `defect ρ ι hι χ a` is the full `G`-intertwining endomorphism
`D_a` of the quotient `C`, with underlying linear map

```
D_a = C.ρ(ι a) - (χ(a) : R) • identity.
```

Its intertwining proof again uses centrality. The lemmas `defect_toLinearMap`
and `defect_apply` give this formula; `defect_pow_toLinearMap` identifies
intertwiner powers with linear-endomorphism powers. For every natural `k`,
`defect_pow_quotientMap` and `evaluation_defect_pow_quotientMap` prove

```
D_a^k(q(v)) = q((ρ(ι a) - χ(a) I)^k(v)),
evaluation φ (D_a^k(q(v)))
  = ((commutativeTranspose (ρ.comp ι)(a) - χ(a) I)^k φ)(v).
```

The first proof is induction on `k` using equivariance and linearity.
The second combines it with the published transpose-defect identity.
`defect_pow_quotientMap_eq_zero_iff` combines this identity with separation:
the left side vanishes exactly when the displayed dual-defect evaluation is
zero for every `φ ∈ E`.

`defectRange ρ ι hι χ a k` is the actual subrepresentation
`range(D_a^k)` of `C`; `mem_defectRange` gives its existential image membership.
`defectRangeRepresentation` equips this subtype with its induced `G`-action.
`defectRangeProjection` is the actual power `D_a^k` corestricted to its image
and is surjective by `defectRangeProjection_surjective`.
`defectRangeInclusion` is the subtype inclusion into `C`.
`defectRangeMap` is the composite of the corestriction with `q`, and
`defectRangeMap_surjective` proves it is surjective from the original `V`.
All three maps are bundled intertwiners for `G`.

`defectRangeInclusion_projection` and `defectRangeInclusion_map` give their
pointwise formulas. `defectRangeInclusion_comp_map` gives the exact equality
of intertwiners

```
inclusion ∘ defectRangeMap = D_a^k ∘ q.
```

These definitions reuse Mathlib's quotient representation, `Rep.mkQ`,
intertwiner powers and range, and linear-map range corestriction.
`defectRange_zero` proves that the image for `k = 0` is the entire quotient.

## Opposite Jacquet specialization

The namespace `Langlands.PadicField.TopologicalData` specializes the construction
to every prime `p`, field `F : PadicField.{uF} p`, supplied `T`,
rank `n`, block shape `B`, representation
`A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)` and character
`χ : (Fin B.length → F.Carrierˣ) →* ℂˣ`.
The field universe `uF` and carrier universe `uV` remain independent.
Here the ambient representation is exactly
`J = CuspidalJacquetMultiplicity.oppositeJacquet T B A`, its acting group is
the full product Levi `B.Levi F.Carrier`, and `ι` is
`B.blockScalarLevi F.Carrier`. The centrality witness is the published
`B.blockScalarLevi_mem_center F.Carrier`.

The detecting space is definitionally the actual
`generalizedCommutativeCharacterSpace (T.splitCentreDualJacquet B A).ρ χ`.
The opposite Jacquet normalization and its transpose convention are inherited
unchanged from `DualJacquet`. In particular, restriction to block scalars is
used to select functionals, while the quotient and image representations
and every bundled map use the full Levi.

Every specialized declaration has prefix `dualJacquetCharacter`, except for
the two membership lemmas beginning `mem_dualJacquetCharacter`.
The object and map suffixes are `Annihilator`, `Quotient`, `QuotientMap`,
`Evaluation`, `Defect`, `DefectRange`, `DefectRangeRepresentation`,
`DefectRangeProjection`, `DefectRangeInclusion` and `DefectRangeMap`.
The corresponding surjectivity, annihilator/zero, evaluation and defect-power
lemmas specialize the generic formulas above.
`dualJacquetCharacterDefectRangeProjection_apply`,
`dualJacquetCharacterDefectRangeMap_apply` and
`dualJacquetCharacterDefectRangeInclusion_apply` give their underlying subtype
formulas. `dualJacquetCharacterDefectRangeInclusion_comp_projection` and
`dualJacquetCharacterDefectRangeInclusion_comp_map` state the two composite
equalities as full-Levi intertwiners.
`dualJacquetCharacterDefectRange_zero` specializes the zeroth-image identity.

## Provenance and scope

The motivating original is A. J. Silberger, *Introduction to harmonic analysis
on reductive p-adic groups* (1979), printed pp.91–92, especially the character
quotient and central-operator image argument in Corollary 2.4.2. Registered source:
`silberger-1979-harmonic-analysis`, SHA256
`b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc`.
The original page images PDF97–98 were read. The full-Levi invariant quotient,
its evaluation API, and all natural-power images are derived here by elementary
module and representation operations. This is an algebraic extension to arbitrary
representations and characters, rather than a claim of Silberger's theorem in
that generality.

No irreducibility, admissibility, smoothness, finite spectrum, finite
nilpotence bound, nonvanishing, criticality or analytic hypothesis is used.
Zero modules, an empty block shape, a vanishing detecting space and `k = 0`
are allowed by the same definitions. If `E` vanishes, the defining annihilator
is all of `J`, so the actual quotient vanishes; no separate field imposing
nonzeroness is supplied. Finite decomposition, a maximal nonzero image layer,
an irreducible quotient, scalar action on such a layer, support conclusions,
and analytic consequences remain separate obligations. The paired Lean file
introduces no axiom or proof hole.
