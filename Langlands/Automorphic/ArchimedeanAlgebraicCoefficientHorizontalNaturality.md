# Naturality of the actual analytic and algebraic coefficient comparison

Fix a number field `F`, a natural rank `n`, finite index types `I` and `m`, an unrestricted embedding-index family `e`, and the original matrix representation `ρ`. For any full automorphic operator intertwiner `L : S.Intertwiner T`, this internal construction makes the original analytic-to-algebraic coefficient comparison natural in the automorphic realization.

`tensorAnalyticAlgebraicReducedLieEquiv_natural` states that applying `L` to the automorphic tensor factor and then applying the original analytic coordinate comparison gives the same vector as first applying that comparison and then applying `L`. Both maps fix the coefficient factor except for the comparison itself. After unfolding the underlying tensor maps, Mathlib's two one-sided tensor composition identities prove this equality.

`tensorAnalyticAlgebraicHorizontalEquiv_natural` gives the corresponding equality of bundled finite adelic intertwiners on the original compact horizontal cochains. Extensionality reduces it to the tensor equality evaluated at each alternating-map input. The compact horizontal submodules, full coefficient carriers and original reduced Lie actions are retained.

With `NeZero n`, `tensorAnalyticAlgebraicHorizontalCyclesSquare` and `tensorAnalyticAlgebraicHorizontalCohomologySquare` construct bundled commuting squares on the existing differential kernels and cycle quotients. The four edges in degree `q` are:

- Top: full automorphic transport from the original analytic cochains, cycles or cohomology of `S` to those of `T`.
- Right: the original analytic-to-algebraic comparison at `T`, as its underlying intertwiner.
- Left: the same original comparison at `S`.
- Bottom: full automorphic transport from the original algebraic objects of `S` to those of `T`.

Each square includes the equality `right.comp top = bottom.comp left`. The cohomological corners are the existing quotients of differential kernels by preceding differential-image boundaries, including the original degree-zero convention. All finite adelic representations are those already defined on these objects.

`tensorAnalyticAlgebraicHorizontalCyclesEquiv_natural` and `tensorAnalyticAlgebraicHorizontalCohomologyEquiv_natural` expose these bundled equalities as inferred-type proof abbreviations. They specialize the generic square-preservation laws directly. The generic cycle and quotient maps on the comparison edges are definitionally the underlying intertwiners of the original `tensorAnalyticAlgebraicHorizontalCyclesEquiv` and `tensorAnalyticAlgebraicHorizontalCohomologyEquiv`; the other two edges are definitionally the full analytic and algebraic transport maps. No cochain commutation or chain-compatibility assumption is added: the cochain square is proved here, and all four chain equations are already proved for the actual maps.

The number field has its independent universe `uF`. The embedding and coefficient index types are arbitrary finite small types with no nonemptiness assumption; the two orientations available at complex places remain unrestricted. Tensor and cochain naturality have no rank-nonzero premise. The cycle and quotient constructions explicitly require `NeZero n`, and every construction allows all natural cohomological degrees. This module adds no topology, analytic regularity, coefficient-occurrence or nonvanishing assertion.

This is an internal composition of the existing actual coefficient comparison, full automorphic tensor transports, and generic horizontal square constructors. Its proof route is tensor-map commutation, horizontal restriction, then existing kernel and quotient descent; it asserts no new original-source identification.
