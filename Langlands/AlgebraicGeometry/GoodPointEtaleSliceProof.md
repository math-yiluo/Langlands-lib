# Etale slices through good points

This internal proof combines the local differential slice construction by
Worker 101, the good-point cotangent bridge by Worker 303, and the propagation
and open shrinking construction by Worker 424. These three workers are
coauthors of this combined result.

For an equivalence relation `t,s : R → U` with `s` smooth and a common
identity section `e`, suppose `x` satisfies the maximal ideal equality
`IsGoodPoint t s e x`. Choose common affine neighborhoods `V` of `x` and
`W` of `e(x)`. Write `A=Γ(U,V)` and `B=Γ(R,W)`, with the `A`-algebra
structure on `B` induced by `s`. The prime `q` of `e(x)` contracts to the
same ideal `p` of `A` under both `s` and `t`. The good-point chart theorem
says that the differentials of the images of `p` under `t` span the
residue cotangent space of `B_q` over `A`.

The differential slice construction selects finitely many equations in
`p`. Their quotient spectrum gives a preimmersion `g : Z → U`, locally
of finite presentation, and a point `a` over `x` where the stalk of
`Z ×_U R → R → U` is formally etale at the canonical identity lift of
`a`. The quotient preimmersion makes the second pullback projection
injective on points, which identifies the point selected by the
algebraic construction with that canonical lift.

The identity lift is a section of the first pullback projection. Since
`s` is smooth, it is flat and locally of finite presentation. The
propagation theorem therefore supplies an open neighborhood `O` of `a`
such that the entire map `O ×_U R → R → U` is etale. Composing `O → Z`
with `g` preserves the preimmersion and local finite presentation, and
the point over `x` remains in `O`.

The result is a slice through a supplied good point. It does not assert
that every orbit contains a good point or construct a globally
surjective family of slices. Those remain separate inputs to the final
smooth equivalence relation slicing theorem. No unproved statement is
used as a hypothesis of this result.
