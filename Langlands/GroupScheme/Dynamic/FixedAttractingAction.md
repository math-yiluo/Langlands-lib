# Actions on cocharacter fixed and attracting schemes

Let `H` be an affine group scheme over the spectrum of an arbitrary commutative
ring `R`, let `X` be an affine relative scheme, let `a` be a supplied actual
action of `H` on `X`, and let `χ : Gm → H` be an actual cocharacter. In every
universe, this module constructs an action of the existing dynamic centralizer
of `χ` on the actual fixed scheme of the restricted action on `X`, and an action
of the existing dynamic parabolic on its actual attracting scheme. These are
the previously constructed all-relative-test representing schemes. The acting
groups are `Dynamic.Affine.centralizerScheme χ` and
`Dynamic.Affine.parabolicScheme χ`.

The action morphisms retain the supplied original action after the actual
inclusions into `H` and `X`. The lemmas `cocharacterFixedAction_act_comp` and
`cocharacterAttractingAction_act_comp` assert this equality on every relative
scheme test, with no restriction to affine, reduced or field-valued tests.

For either new action, its actual relation is `(h,x) ↦ (h • x,x)`. The lemmas
`cocharacterFixedAction_relation` and `cocharacterAttractingAction_relation`
identify these relations with the maps induced on the fixed and attracting
schemes of the original relation. The source comparison uses the conjugation
fixed/centralizer or attracting/parabolic isomorphism and the product comparison;
the target comparison is the product comparison for `X × X`.

If `H` and `X` are smooth over `R` and the original action relation is smooth,
then both new action relations are smooth. These are the conclusions of
`smooth_cocharacterFixedAction_relation` and
`smooth_cocharacterAttractingAction_relation`. All three smoothness assumptions
are retained. The construction imposes no characteristic, nontriviality or
regularity condition on the cocharacter.

The module also provides the generic `actionOnFactor` construction: when a
supplied action morphism restricts along a group homomorphism and factors
through a monomorphism of relative schemes, the factor is an actual action.
Its point laws follow by cancellation of that monomorphism.

This is an internal construction. First, restricting `a` along `χ` gives its
actual multiplicative-group action. The original action morphism is equivariant
for conjugation on `H` and this restricted action on `X`, by the action laws and
the group identity `(t h t⁻¹)t = t h`. The relation is equivariant for the same
source and diagonal target actions. The actual centralizer and parabolic
inclusions give respectively fixed and attracted points. Product criteria and
equivariant functoriality therefore factor the action morphisms through the
actual fixed and attracting schemes. Monomorphism cancellation supplies the
action laws. For each relation comparison, composition with the two actual
inclusions and product projections gives equality with the original relation;
monomorphism cancellation proves the required equality. Finally, smoothness of
the structure maps of `H × X` and `X × X` follows by base change and composition.
The earlier smooth equivariant fixed/attracting map theorems apply to the
original relation, and the comparison isomorphisms transfer that smoothness to
the two actual action relations.

The provenance is entirely internal to the existing action laws, all-test
representability, product comparisons, conjugation comparisons and relative
smoothness theorems. This unit does not assert orbit closedness, reductive
quotient affineness or `DynamicQuotientProperStatement`.
