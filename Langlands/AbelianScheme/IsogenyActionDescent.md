# Descent of integral actions through actual isogenies

This is an internal derived construction from
`Langlands.AbelianScheme.IsogenyFactorization`, the actual abelian-scheme
category, and the exact kernel comparison in `FiniteEtaleQuotient`. It adds no
geometric existence assumption. The base is an arbitrary scheme in an arbitrary
universe; the acting ring may be noncommutative and has an independent universe.

`KillsKernel q g` means that the composite of the actual group-scheme kernel
inclusion of `q` with `g` is the trivial homomorphism. For a supplied finite,
flat, surjective isogeny `q : A ⟶ B`, `IsogenyActionDescent.lift` specializes
actual group-scheme factorization to abelian-scheme homomorphisms. The lemmas
`fac`, `hom_ext` and `lift_unique` establish its factorization and uniqueness.
The kernel pullback square proves `killsKernel_self`; composing a factorization
proves `killsKernel_of_factor`.

For a unital ring action `α : R →+* End A`, suppose every composite `α r ≫ q`
kills the scheme kernel of `q`. `IsogenyActionDescent.action` is an actual
unital ring homomorphism `R →+* End B`. Its equivariance equation is
`q ≫ action hq α hα r = α r ≫ q`, and this equation characterizes the action
uniquely. Each endomorphism is constructed by factorization; cancellation along
the isogeny proves preservation of zero, one, addition and multiplication. The
multiplication check uses the existing endomorphism ring convention
`e * f = f ≫ e`, including for noncommutative `R`.

The descent commutes with arbitrary actual scheme base change. To prove kernel
vanishing after base change, pull back the already constructed factorization
and apply `killsKernel_of_factor` to the kernel of the pulled-back map. This
uses the actual new scheme kernel, without choosing an identification of it
with a pullback of the old kernel. Uniqueness then proves `lift_baseChange` and
`action_baseChange`. The action comparison is equality of the existing
`baseChangeOrderAction` with descent on the same pulled-back abelian schemes.
No flatness condition on the base-change map is imposed.

For a supplied finite étale closed subgroup `K`, `K.PreservedBy e` means there
is an actual endomorphism `k` of the commutative group scheme `K.G` satisfying
`K.inclusion ≫ e = k ≫ K.inclusion`. For supplied quotient data `D`,
`D.killsKernel_iff` uses the exact group-scheme isomorphism `D.kernelIso` to
identify kernel vanishing with `K.inclusion ≫ g = 0`. In particular the quotient
map vanishes on `K`. Thus each subgroup-preserving endomorphism satisfies the
required kernel condition. `D.lift` supplies factorization for any map killing
`K`, and `D.action` descends an action whose endomorphisms all preserve `K`.
The quotient action has the same uniqueness and arbitrary-base-change laws.

All subgroups, kernels, quotient schemes and morphisms retain their complete
scheme structure. The results need a supplied isogeny or quotient; they do not
construct a stable finite subgroup, an integral model of a rational action, or
a representing scheme for the normalized Harris CM moduli problem. These are
separate obligations. No external literature is newly asserted here.
