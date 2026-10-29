# Reduction of the closed agreement locus to an affine base

`Langlands.AbelianScheme.RigidifiedClassesEqualizerClosedReductionStatement.{u}` is the
proposition

```lean
RigidifiedClassesEqualizerClosedAffineStatement.{u} →
  RigidifiedClassesZariskiSeparatedStatement.{u} →
    RigidifiedClassesEqualizerClosedStatement.{u}
```

This unit only defines the proposition. It proves nothing. In particular it does not
prove `RigidifiedClassesEqualizerClosedStatement`. It only says that this statement follows
from the two named hypotheses.

## The three propositions

All three are published Prop-valued definitions in `namespace Langlands.AbelianScheme`. They
are used here unchanged, at the same universe `u`.

- `RigidifiedClassesEqualizerClosedStatement.{u}` (module
  `Langlands.AlgebraicGeometry.Picard.RigidifiedClassesEqualizerClosedStatement`), the
  conclusion. For every scheme `S`, abelian scheme `A` over `S`, object `T : Over S` and two
  classes `q r : RigidifiedClasses A T`, there are a scheme `Z` and a closed immersion
  `ι : Z ⟶ T.left` such that a morphism `h : T' ⟶ T` in `Over S` factors through `ι`
  (`∃ g, g ≫ ι = h.left`) exactly when the actual rigidified pullbacks
  `classesPullback … h q` and `classesPullback … h r` are equal.
- `RigidifiedClassesEqualizerClosedAffineStatement.{u}` (module
  `Langlands.AlgebraicGeometry.Picard.RigidifiedClassesEqualizerClosedAffineStatement`), the
  first hypothesis. It is the conclusion specialised to `S = Spec R` for a commutative ring
  `R` and to `T = Over.mk (𝟙 (Spec R))`.
- `RigidifiedClassesZariskiSeparatedStatement.{u}` (module
  `Langlands.AlgebraicGeometry.Picard.RigidifiedClassesZariskiSeparatedStatement`), the second
  hypothesis. For every `S`, `A`, `T`, open cover `𝒰` of `T.left` and classes `q`, `r`: if the
  pullbacks of `q` and `r` along every cover member `Over.homMk (𝒰.f i)` agree, then `q = r`.

So the proposition says: the affine-base case and Zariski separatedness of rigidified classes
together imply the general closed agreement locus, for an arbitrary base `S` and arbitrary
parameter object `T`.

## Provenance

Internal. The implication is a decomposition step of this project, made in proof task
`e3d4a3ab-f378-42af-87c5-0cd4caec7b2e` for the published conclusion. That conclusion is
derived from the Stacks Project, *More on Morphisms*, Lemmas 37.33.1 (tag 0BDP) and 37.33.4
(tag 0BF0); see its paired Markdown. The present statement adds no mathematics of its own. It
records the standard reduction of a representability statement for a Zariski-local subfunctor
to an affine base. The hypotheses are exactly the two other published propositions. A Lean
proof of the implication is a separate unit. The remaining inputs, proofs of the affine-base
statement and of Zariski separatedness, are separate proof tasks.
