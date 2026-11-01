# Actual quotient retractions on a selected central block

Author: Worker 526. The namespace is
`Langlands.QuotientRealBlockRetraction`. This internal algebraic assembly
uses the grouped lifting corollary, the published grouped-central
retraction and Mathlib's simple-source intertwiner lemma. The group and
all three carrier universes remain independent.

`projectorFixedOnGrouped` extends a projector identity on each selected
generalized central-character space to their actual grouped sum, by
supremum induction and linearity.

`quotientInjection` considers actual maps `i : A → E`, `r : E → A` and a
surjection `f : E → N`. It assumes finite full-central operator span on
`E`, irreducibility of `A`, that `i ∘ r` fixes the selected block, and a
nonzero map `g : A → N` whose image is selected. If `f ∘ i` were zero,
selected lifting would lift each `g(v)` to a selected `w`. The identity
`w = i(r(w))` would make `g(v)` zero. Thus `f ∘ i` is nonzero, and
irreducibility makes it injective. No identity between `i` and an
adjunction unit is needed.

`quotientProjector` also assumes finite full-central operator span on `N`
and injectivity of `f ∘ i`. Selected lifting and the projector identity
show that every selected target vector equals `f(i(a))`. Choose a
preimage `a`; injectivity makes this choice linear and equivariant.
Composing that inverse with the published central retraction of `N`
extends it to an actual map `rQ : N → A`. The composite `f ∘ i ∘ rQ`
fixes the entire selected target block.

`quotientRetraction` assumes the whole source `A` lies in its selected
block and `g` is nonzero. Intertwiners preserve grouped blocks, so the
preceding results apply. The constructed `rQ` is also a left inverse to
`f ∘ i` on all of `A`.

These statements retain all generalized central directions and allow
other target blocks. The finite central actions, nonzero map and source
block property are explicit hypotheses, supplied by the actual
representation-theoretic specialization in `ActualQuotientRealBlock`.
