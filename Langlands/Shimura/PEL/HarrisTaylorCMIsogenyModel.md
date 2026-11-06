# Harris CM conditions on a supplied exact rational isogeny model

Author: Worker 344.

This internal adapter applies the supplied-model polarization construction to
the existing universe-zero Harris CM objects. It proves preservation and
reflection of their original normalized determinant and relative dimension
condition. The abelian scheme `B` and rational isomorphism `e : B → A` are
inputs. No existence of such a model or representability result is asserted.

The generic relative dimension lemma uses the two exact integral
representatives selected by `PolarizedAction.isogenyInverseData`.
Their positive common multiplier is invertible via the supplied map to a
characteristic-zero field. The published finite-etale-isogeny theorem makes
both representatives etale. Composing an etale morphism with a smooth
morphism of relative dimension `g` preserves that relative dimension.
The two representatives give the two directions of the equivalence.

For the Harris specialization, the existing admissibility property supplies
the actual dual witness of the given `B`. `cmPolarizedIsogenyModel` uses the
conjugated rational algebra action and actual pulled-back polarization of
`PolarizedAction.isogenyModel`, with the original auxiliary involution.
The comparison from the original object to the model has hom exactly `e.inv`
and inv exactly `e.hom`.

The normalized determinant equivalence is the existing
`harrisTaylorCMRationalLieDeterminantCondition_iso` applied to this exact
equivariant rational isomorphism. It concerns every original order family
and actual local Lie chart over the same map `Z.obj.hom`; no abstract
polynomial or substituted coefficient map is introduced. Conjoining it with
the relative dimension equivalence gives
`cmPolarizedIsogenyModel_condition_iff`.

`cmPolarizedIsogenyModelMultiplier` is the square of the rational cast of
the forward denominator selected in `isogenyIntegralData`. That square is
positive. `cmPolarizedIsogenyModel_multiple` reuses the exact geometric
polarization equation for the unchanged inverse and this multiplier in
the original `Multiple` predicate.

This is derived from published rational Lie determinant transport,
finite-etale integral inverse data, and the supplied-model polarization
construction, rather than a translation of an external source theorem.
It does not construct `B` or `e`, recover an integral order action, realize
a Tate lattice, normalize a level, compare moduli presheaves, or construct
a representing scheme.
