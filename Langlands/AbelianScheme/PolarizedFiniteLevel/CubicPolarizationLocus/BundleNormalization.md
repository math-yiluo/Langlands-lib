# Normalization at the identity section

`normalizedBundle` uses the tensor inverse of the restriction to the identity to give an actual rigidified line bundle. `normalizedBundleClass` divides the ordinary class by the pullback of its restriction. The class of the carrier computed from any normalization evaluation agrees with this formula. The formula commutes with tensor powers and with arbitrary change of base. Two normalized classes agree exactly when the original bundles differ by an actual bundle pulled back from the base. The class formula proves the converse with the quotient of the two restrictions as the base bundle.

These identities follow from the section equation, compatibility of pullback with tensor products, and the inverse evaluation in `LineBundle.normalize`.
