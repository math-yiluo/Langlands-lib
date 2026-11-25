# Adjoint Weil presentations from supplied finite products

This internal construction converts a supplied actual finite product
decomposition into the existence witness required by the affine adjoint
Weil-restriction target. The motivating source is Brian Conrad,
*Reductive group schemes* (2014), the proof of Proposition 6.4.4 and
Remark 6.4.5, pp.232–233, registered as
`conrad-2014-reductive-group-schemes`.

`AffineAdjointWeilPresentation G` contains a finite, projective, étale
algebra over the original affine base, a reductive group on that algebra
with adjoint almost-simple geometric fibres, surjectivity of its spectrum
map, and an isomorphism of `G` with its actual affine Weil restriction.
The affine and local finite type hypotheses needed to form that
restriction are retained as part of the data. `exists_pair` forgets this
data to the existential format of the original target.

`ofProduct` assumes a supplied isomorphism from `G` to a finite product
of reductive groups with almost-simple geometric fibres. It assumes
triviality of the full relative centre of `G` and nontriviality of every
geometric fibre. The finite-product centre comparison proves that all
factor groups have trivial full centre. Their almost-simple geometric
fibres are therefore adjoint.

The actual `AffineWeil.FiniteFamily` construction supplies the finite
product algebra, assembled group, component recovery, fibre properties
and Weil isomorphism. Surjectivity is proved pointwise: above a given
point of the original base, a nontrivial geometric fibre gives a
nontrivial original group functor; a nontrivial product has a nonempty
factor index. An evaluation section of the finite product algebra then
gives a point above it. This also handles the empty base, where the
surjectivity condition is vacuous; no global nonempty-base or
nonempty-index assumption is added.

This is an internal assembly of the supplied product and proved
finite-family constructions. It does not construct the simple factors
or prove étale pair descent or uniqueness. All rings, schemes and
factor indices lie in the arbitrary universe `u`.
