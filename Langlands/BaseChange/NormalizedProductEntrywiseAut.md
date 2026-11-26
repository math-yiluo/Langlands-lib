# Entrywise pullback of normalized parabolic induction

`normalizedParabolicInducedEntrywiseAutEquiv` identifies the pullback of normalized induction along an entrywise field automorphism with normalized induction of the pulled-back Levi action. Both are actual smooth induced representations. Precomposition on sections gives the map. Its covariance uses `leviProjection_parabolicAut` and `parabolicHalfModulus_parabolicAut`, which express commutation with the Levi projection and preservation of the half modulus.

For an external tensor of block actions, evaluation on pure tensors identifies the pulled-back Levi tensor with the tensor of the pulled-back factors. This gives `normalizedProductInducedEntrywiseAutEquiv`. These are internal consequences of the published smooth-induction pullback and block tensor constructions.
