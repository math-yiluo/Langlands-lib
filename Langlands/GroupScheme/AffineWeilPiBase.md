# Weil restriction from a finite product of copies of the base ring

For an arbitrary commutative ring `A`, a finite type `I`, and an affine group
scheme `H` locally of finite type over `Spec(A^I)`, this internal construction
identifies the actual affine Weil restriction of `H` with the categorical
product of its pullbacks along the evaluation maps `A^I → A`.

The implemented proof uses the published tensor decomposition
`WeilGm.piTensorEquiv`. For every actual `A`-algebra `R`, it identifies
`A^I ⊗_A R` with `R^I`, with coordinate `b ⊗ r ↦ b(i) r`. The original
`A^I`-action on coordinate `i` is retained through that evaluation.
The published multiplicative comparison for affine group points over a
product of coefficient rings gives the corresponding product of original
point groups. Each is the actual point group of the pullback of `H` along
evaluation. Composition with the multiplicative point equivalence of
the original affine Weil restriction yields the displayed point splitting.

The tensor coordinates commute with every coefficient-algebra
homomorphism. The implemented proof combines this naturality with the
published factor-point comparison and finite-product point comparison.
The resulting natural isomorphism of actual affine group-valued point
functors gives `AffineWeil.PiBase.iso` by affine full faithfulness.

This is an internal composition of Library constructions, motivated by the
finite disjoint-union identity used in Brian Conrad, *Reductive group
schemes* (2014), Proposition 6.4.4 and Remark 6.4.5, pp.232–233, registered
as `conrad-2014-reductive-group-schemes`. There are no field, reducedness,
characteristic, reductivity or nonempty-index hypotheses. All rings,
schemes and test algebras lie in the arbitrary universe `u`. Construction
of `H` from separately supplied component groups is a separate step.
