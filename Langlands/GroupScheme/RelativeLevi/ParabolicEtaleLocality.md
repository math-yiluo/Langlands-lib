# Étale detection of relative parabolicity

This derived module proves that a homomorphism of group schemes in a reductive
ambient group is relatively parabolic if its pullback by a surjective étale
base morphism is relatively parabolic.

`IsRelativeParabolicSubgroup.of_etale_surjective` first descends smoothness and
affineness of the source structure morphism. Faithfulness of the pullback
functor on slice schemes detects monicity of the inclusion. For each point of
the base, surjectivity supplies a point above it. The map of residue fields is
separable and hence algebraic because the base morphism is étale. The actual
pullback comparisons identify the upper residue inclusion with extension of
the lower residue inclusion.

Both lower residue group schemes are affine. Closedness of the residue
inclusion therefore descends from the upper parabolic inclusion by the imported
affine faithfully flat reflection theorem. The imported algebraic-extension
reflection of field parabolicity now proves that the lower residue inclusion is
parabolic. Closedness of the original inclusion over the full base is not an
input or a conclusion of this argument.

`isRelativeParabolicSubgroup_iff_etale_surjective` combines this detection
theorem with arbitrary base-change preservation. There is no affineness,
quasi-compactness or noetherian hypothesis on the base schemes or cover.

`ParabolicSubgroupModuli.ofEtaleSurjective` constructs the actual
`ParabolicSubgroup G` from a supplied inclusion whose étale pullback is
relatively parabolic. Its underlying subgroup functor is the range of the
original inclusion. The value and base-change laws identify this range and
recover the prescribed pulled-back inclusion's range on every test scheme.

The proof is an internal consequence of the imported scheme property descent,
residue field and actual group-scheme comparison theorems. Its parabolic
predicate is unchanged, and it constructs no parameter scheme or effective
subgroup descent. No additional external mathematical assertion is used.
