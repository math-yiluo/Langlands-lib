# Twisted conjugation on semilinear stabilizers

This internal group-action construction extends
`SemilinearCocycleAction`. Let groups `Γ` and `H` act through
`ρ : Γ →* MulAut H` and `A : Γ →* Equiv.Perm X`, with
`A σ (g • x) = ρ σ g • A σ x`. Let `c : Γ → H` satisfy
`c (σ * τ) = c σ * ρ σ (c τ)`.

`conjugationAction` is the group homomorphism whose value at `σ` sends
`g` to `c σ * ρ σ g * (c σ)⁻¹`. The cocycle identity proves its
multiplication law. The identity case uses the published `cocycle_one`.
`action_smul` proves compatibility of this group action with the already
constructed twisted permutation action on `X`.

`conjugationAction_mem_stabilizer_iff` transports point stabilizers,
without requiring the point to be fixed. Its proof rewrites the
stabilizer equation using `action_smul` and uses injectivity of the
twisted permutation.

`restrictGroupAction` restricts any automorphism action to a subgroup
preserved by every element of `Γ`. The inverse on that subgroup is the
restriction of the action of `σ⁻¹`. The group action laws and
multiplicativity follow by equality of the underlying group elements.
`stabilizerAction` applies this construction at a point fixed by every
twisted permutation. Its evaluation lemma retains the actual
inner-twisted coefficient formula.

`conjugationAction_mem_normal_iff` shows that any normal subgroup stable
under `ρ` is also stable under twisted conjugation. The forward
implication conjugates back by `(c σ)⁻¹`; the reverse implication uses
normality directly. `normalStabilizerAction` restricts to the
intersection of such a normal subgroup with the stabilizer of a
twisted-fixed point. Its evaluation lemma again gives the same formula.

All three carrier universes are independent. The construction assumes
neither a topology nor finite-level behavior of the cocycle. This is
derived internal content from the imported group-action constructions
and group identities; it introduces no claim about original literature.
It does not construct an integral model, identify a neutral parahoric,
or produce a reductive quotient.
