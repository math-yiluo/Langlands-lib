# Finite coefficient models of affine smooth group schemes

This internal construction combines the published affine scheme approximation
theorem, `Langlands.GroupScheme.subalgebraDescent`, and descent of smoothness
to finitely generated subalgebras. It is a prerequisite for reducing integral
models over the maximal unramified integers to finite coefficient stages.

`GroupModel R A G` contains a finitely generated `R`-subalgebra of `A`, an affine
smooth group scheme over it, and an actual group scheme isomorphism from `G`
to its base change. `exists_groupModel` also preserves a prescribed finite set
of coefficients. `groupModel` chooses a model with no prescribed coefficients.

The proof first approximates the underlying affine scheme, then descends its
group law by the published group scheme subalgebra theorem. A further finite
coefficient extension makes the structure morphism smooth. Affineness survives
the two base changes. Finite type is transitive in the coefficient tower, and
the pullback tower comparison gives the resulting group isomorphism.

This result does not assert that the coefficient algebra is finite or
unramified, and it does not construct a Galois action or a descent datum.
