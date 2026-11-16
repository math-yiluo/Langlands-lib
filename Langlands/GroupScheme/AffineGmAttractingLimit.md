# The limit map from an attracting scheme to its fixed scheme

For an actual action of the chosen multiplicative group on a separated
relative scheme X over any scheme S, an affine-line extension of an orbit
is unique. Restricting two extensions to the multiplicative group and using
the published extension-uniqueness lemma proves this assertion. Every point
fixed after all scheme refinements has a constant orbit extension.

Scaling the affine-line parameter by a universal unit agrees with acting on
the extension. Both sides agree on the multiplicative-group parameter by the
action multiplication law, so uniqueness makes them equal everywhere.
Evaluation at zero and the fact that scaling fixes zero imply that this
value is fixed after every relative scheme refinement. If the original
point is fixed, uniqueness identifies any orbit extension with the constant
one, and its zero value is the original point. These results require only
separatedness of X over S, with no affineness or smoothness assumption.

Now let R be any commutative ring and X any affine scheme over Spec R with
a supplied actual multiplicative-group action s. The constructed attracting
scheme has a universal affine-line orbit extension. Its zero evaluation
`schemeActionAttractingZero` is fixed, so all-test fixed-scheme representation
factors it through the actual morphism `schemeActionAttractingLimit` from the
attracting scheme to the fixed scheme. Composition with the fixed inclusion
is precisely zero evaluation. Affineness supplies the separatedness used
in the preceding argument.

The universal extension is natural on every relative test: pulling it back
along a factor of x agrees with any affine-line orbit extension of x, by
uniqueness. Consequently, pulling back its zero evaluation gives the zero
value of that extension. No affine restriction is imposed on this test.

The fixed-scheme inclusion has a constant orbit extension, hence factors
through the attracting scheme as `schemeActionFixedToAttracting`. Its
composite into X is the original fixed inclusion. Evaluating its extension
at zero recovers that same inclusion, and cancellation through the fixed
closed monomorphism proves that this morphism is a section of the limit map.

This is an internal deduction from actual scheme action laws, the published
separated extension-uniqueness and affine-line scaling lemmas, and the actual
fixed and attracting representation theorems. It constructs no new source
theorem. It does not prove relative smoothness of induced maps, orbit
closedness, reductive quotient affineness or `DynamicQuotientProperStatement`.
