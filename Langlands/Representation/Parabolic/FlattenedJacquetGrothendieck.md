# Actual flattened Jacquet restriction on exact finite-length K0

Author: Worker 320.

This is a derived internal adapter for the existing actual parabolic functors.
It introduces no new assertion from the literature. All parameters are arbitrary
`{p : ℕ} [Fact p.Prime]`, `F : PadicField.{uF} p`, supplied
`T : F.TopologicalData`, a natural rank `n`, an ordered positive block shape `B`
and a refinement `S : BlockRefinement B`. The field and representation-carrier
universes remain independent; actual smooth complex carriers have universe
`max uF uV`.

`Langlands.Parabolic.normalizedFlattenedJacquetK0` first applies the existing
`normalizedComposedJacquetK0` and then the actual coordinate equivalence
`flattenedLeviK0`. Its domain is the exact finite-length smooth Grothendieck
group of `GL_n(F)` and its codomain is that of the actual product Levi of
`B.flatten S`. It is an integer-linear map on every virtual class. The exact
quotients retain all short exact relations, including nonsplit sequences.

`normalizedFlattenedJacquetK0_eq` proves that this composite equals
`normalizedJacquetK0 F T (B.flatten S)`. Generator extensionality reduces the
equality to actual finite-length smooth objects. The existing composed Jacquet
preservation theorem gives finite length of the direct full-radical quotient;
actual continuous coordinate pullback preserves its finite length. The ordinary
flattened Jacquet object has finite length by the published Jacquet theorem.
The three generator formulas reduce the desired equality of classes to an
intertwining equivalence between those actual objects. That equivalence is the
second clause of published `flattenedJacquetComparison`, which identifies the
actual upper radicals and the inverse half-modulus normalized actions and sends
each class of an original vector to its class. Thus equality of the canonical
Grothendieck classes completes the proof. No abstract replacement functor or
assumed transitivity certificate is used.

`normalizedComposedInductionK0_comp_composedJacquetK0` then proves

```text
normalizedComposedInductionK0 F T B S ∘ normalizedComposedJacquetK0 F T B S
  = normalizedInductionK0 F T (B.flatten S) ∘
      normalizedJacquetK0 F T (B.flatten S).
```

By the existing definitions the left side is induction from the coarse Levi
to `GL_n(F)`, refined induction from the refined Levi to the coarse Levi,
refined Jacquet restriction from the coarse Levi to the refined Levi, and
coarse Jacquet restriction from `GL_n(F)` to the coarse Levi, in that order
from output to input. The proof substitutes the published
`normalizedComposedInductionK0_eq_flattened`, reassociates linear-map
composition, and applies `normalizedFlattenedJacquetK0_eq`. It uses the actual
normalized upper-block induction with positive half-modulus covariance and
right translation, and the actual inverse half-modulus upper Jacquet action.

Both equalities include rank zero, the empty shape and empty refinement family.
They concern all virtual classes and have no positivity, admissibility,
irreducibility, cuspidality, finite vector-space dimension, tensor decomposition
or extra theorem-valued hypothesis. The unit supplies a transitivity adapter;
it does not prove Aubert involutivity, irreducibility of an Aubert image or the
analytic segment classification. Its only direct inputs are the published
flattened induction and normalized quotient comparison modules.
