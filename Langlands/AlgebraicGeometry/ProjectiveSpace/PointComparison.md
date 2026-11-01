# Comparing projective-space points on two affine charts

The theorem
`AlgebraicGeometry.ProjSpace.specMap_comp_awayInclusion_eq_of_forall_apply_ratio_mul_eq`
proves equality of two morphisms from an affine scheme into the same
polynomial projective space. The morphisms may use different standard
affine charts. Their coordinate ratios must arise from the same family
of homogeneous coordinates.

## Objects and exact hypotheses

Let `R` and `B` be commutative rings in the same arbitrary universe,
with an `R`-algebra structure on `B`, and let `n : ℕ`. Write
`𝒜 = MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R`.
The projective space is `Proj 𝒜`, using the published `ProjSpace`
definitions. Its chart at `i : Fin (n + 1)` is
`Spec (Away 𝒜 (MvPolynomial.X i))`, with the actual open immersion
`Proj.awayι`.

The input supplies a family `a : Fin (n + 1) → B`, indices `i` and
`j`, proofs that `a i` and `a j` are units, and algebra homomorphisms
`ψi` and `ψj` from these two chart rings to `B`. For every index `l`,
the required identities are

\[
 \psi_i(X_l/X_i)\,a_i=a_l,\qquad
 \psi_j(X_l/X_j)\,a_j=a_l.
\]

Here the fractions are precisely `ProjSpace.ratio R n i l` and
`ProjSpace.ratio R n j l`. The conclusion is equality of scheme
morphisms

\[
 \operatorname{Spec}(\psi_i)\mathbin{\gg}\operatorname{awayι}_i
 =
 \operatorname{Spec}(\psi_j)\mathbin{\gg}\operatorname{awayι}_j.
\]

Neither ring must be nontrivial. The dimension may be zero, and the
indices may coincide. The exported theorem retains the hypothesis on
`a i` from the source, although the implemented proof needs only the
unit hypothesis on `a j` and the two displayed coordinate identities.
It imposes no separate unit-ideal condition on the whole family `a`.

## Construction and proof

The helper namespace is `AlgebraicGeometry.ProjSpace.PointComparison`.
The maps `mapI` and `mapJ` take the two chart rings to the homogeneous
localization away from `X i * X j`. Their values on ratios satisfy

\[
 \operatorname{mapJ}(X_l/X_j)\,
 \operatorname{mapI}(X_j/X_i)=\operatorname{mapI}(X_l/X_i).
\]

The proof checks this equality after applying the injective map to the
ordinary localization. The maps also agree on scalars from `R`.

The coordinate relation at `j` gives
`ψi (X j / X i) * a i = a j`. Since `a j` is a unit, so is
`ψi (X j / X i)`. The primary definition `liftij` is the resulting
ring homomorphism from the overlap ring to `B`, obtained by
`IsLocalization.Away.lift` and the actual localization instance
`Away.isLocalization_mul`. It is conditional on exactly this supplied
data and the proved unit property.

The localization universal property proves that `liftij` restricts to
`ψi` along `mapI`. To prove its restriction along `mapJ` equals `ψj`,
the proof uses `ProjSpace.adjoin_range_ratio`: chart ratios generate
the chart ring as an `R`-algebra. On a ratio, the overlap identity and
the two coordinate formulas give equality after multiplying by the
unit `a j`, which can be cancelled. On scalars the result follows
from equality of the two scalar maps. Addition and multiplication
preserve the equality, completing algebra-adjoin induction.

Thus both chart ring maps factor through the same `liftij`. Applying
`Spec.map` reverses the factorizations.
`Proj.SpecMap_awayMap_awayι` identifies their composites with the two
chart inclusions, proving equality in `Scheme`, including their
structure sheaf maps.

## Source and adaptations

The source is registered as
`anthropic-flt-complete-lean-source-6e837e75`, commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`, distribution SHA-256
`a2baece9c13f309f914ac09f2d8342a17d363c8ad27e587b84337ff943ed2e1a`.
Both original files were read completely:

- `P2M/Sol/S_AlgebraicGeometry_ProjSpace_specMap_comp_awayInclusion_eq_of_forall_apply_ratio_mul_eq.lean`,
  lines 1–156, SHA-256
  `0ebe4e6207beb9f3d78ce8ccc1d14e5e3ceee6e29fa0c4ec12b09fe6fa12fd01`.
- `Theorems/Thm_AlgebraicGeometry_ProjSpace_specMap_comp_awayInclusion_eq_of_forall_apply_ratio_mul_eq.lean`,
  lines 1–28, SHA-256
  `4b46f6a075cc0c705e85880c91b6526741a0aa8154c867fef755a5f201ef1fb0`.

The generated solution namespace becomes
`AlgebraicGeometry.ProjSpace.PointComparison`, and the theorem is
exported directly under the original wrapper's name. The published
`Langlands.AlgebraicGeometry.ProjectiveSpace.Charts` import replaces the aggregate `Mathlib`,
original definition and `P2M.Util` imports. Two proof-local `letI` declarations become `let` declarations to follow
the current linter. The construction and proof are retained without
mathematical changes. The exported signature
matches the complete original wrapper.

Apache 2.0 attribution is retained in
[LICENSE](../../../licenses/Anthropic-FLT/LICENSE),
[NOTICE](../../../licenses/Anthropic-FLT/NOTICE), and
[ATTRIBUTION.md](../../../licenses/Anthropic-FLT/ATTRIBUTION.md).
There is no separate attribution-table entry for these source files.

## Scope

This is a conditional equality of two supplied projective-space
morphisms. It will support compatibility of Grassmannian chart maps.
It does not construct a Grassmannian representing scheme or its
projective embedding. It proves no CM moduli representability,
admissibility, smoothness, projectivity or normalized presheaf
comparison; those remain obligations of the host task.
