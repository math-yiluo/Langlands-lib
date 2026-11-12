# Density of actual geometric two-power torsion

Author: Worker 3376.

The theorem `Langlands.AbelianScheme.Tate.fieldTwoPowerTorsionDensity` proves
the exact Library proposition
`Langlands.AbelianScheme.Tate.FieldTwoPowerTorsionDensityStatement.{u}`. For
every field `Ω : Type u` with `IsAlgClosed Ω` and `CharZero Ω`, and every actual
bundled abelian scheme `A : AbelianScheme (Spec (CommRingCat.of Ω))`, the set
`twoPowerTorsionLocus A` is dense in the underlying space of `A`. That set
consists of the images of the unique point of `Spec Ω` under the actual sections
`s : Over.mk (𝟙 _) ⟶ A.X` with `s ^ (2 ^ n) = 1` for some `n`, the power being
taken in the existing section group. The universe `u` is arbitrary.

## Implemented proof

The proof is one application. The published reduction
`fieldTwoPowerTorsionDensity_reduction`, from module
`Langlands.AbelianScheme.Tate.TwoPowerTorsionDensityReduction`, proves

```text
GroupScheme.FieldCubePullbackStatement.{u} →
GroupScheme.AlgebraicallyClosedFieldAmpleExistenceStatement.{u} →
FieldTwoPowerTorsionDensityStatement.{u}
```

Both antecedents are now unconditional published theorems:

- `Langlands.GroupScheme.fieldCubePullback.{u}`, from
  `Langlands.AbelianScheme.FieldCubePullbackProof`, proves the balanced cube
  pullback identity for actual line bundles over an arbitrary field.
- `Langlands.GroupScheme.algebraicallyClosedFieldAmpleExistence.{u}`, from
  `Langlands.AbelianScheme.AlgebraicallyClosedFieldAmpleExistenceProof`, gives
  an actual ample line bundle on every commutative smooth proper geometrically
  connected group scheme over an algebraically closed field.

Applying the reduction to these two theorems gives the target.

The imported reduction argues as follows. Fix `Ω` and `A`. The published
`twoPowerTorsionClosureAbelianScheme_exists` realizes the Zariski closure of
`twoPowerTorsionLocus A` as an actual abelian scheme `B` with a homomorphism
`f : B ⟶ A` whose underlying morphism is a closed immersion with that closure as
range. Let `gA` and `gB` be the relative dimensions of `A` and `B`. Since `2 ≠ 0`
in `Ω`, the ample bundles on `A` and `B` and the cube identity feed the published
rank formula `finrank_multiplication_eq_of_ne_zero`. Combined with
`natCard_level_eq_multiplicationFinrank`, it gives `2 ^ (2 * gA)` actual
`2`-torsion sections of `A` and `2 ^ (2 * gB)` of `B`. The published
`twoPowerTorsionLevelComparison` makes the `2`-torsion level map of `f`
bijective, so `gB = gA`. Then `fieldEqualDimensionClosedImmersion` makes the
underlying morphism of `f` an isomorphism. Its range, the closure of the
torsion locus, is therefore the whole space.

The theorem's type is the Library proposition itself. It has no hypotheses
and assumes no density, torsion cardinality, Tate faithfulness or replacement
torsion model. It uses the actual `twoPowerTorsionLocus` and section group
operations of the statement. The target statement pair and its imports are
unchanged. The theorem depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Provenance

This is the final internal composition of three published theorems. The
reduction's companion records the source correspondence and the differences
from it. The source is Edixhoven, van der Geer and Moonen, *Abelian Varieties*,
preliminary version, Chapter V, §3, Theorem (5.30) and its proof in the case
`p ≠ char(k)`, printed page 84 (PDF page 88). It is registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`. The
companions of the two antecedent proofs record their authors and sources.
