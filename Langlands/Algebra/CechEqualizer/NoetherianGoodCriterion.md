# The noetherian core of the smooth equalizer fibre criterion

`Langlands.Algebra.CechEqualizer.NoetherianGoodCriterion.{u,v,w,z}` is a
`Prop`-valued definition. It quantifies over a commutative noetherian ring
`A₀ : Type u`, commutative `A₀`-algebras `C₀ : Type v` and `C₁ : Type w`,
an arbitrary `A₀`-module `N : Type z`, and an `A₀`-linear map
`d : C₀ →ₗ[A₀] C₁` with `d 1 = 0`. It assumes that `C₀` is faithfully flat
and `C₁` is flat over `A₀`. If `q.ResidueField` is `Good d` for every
associated prime `q` of `N`, the conclusion is `Good d N`.

The definition `Good` is imported from
`Langlands.Algebra.CechEqualizer.Definitions`: every element of `N ⊗[A₀] C₀`
killed by `N ⊗ d` must be `n ⊗ 1` for some `n : N`. The hypothesis concerns
all associated primes of `N`, including nonmaximal primes. The module `N`
is not assumed finitely generated. There is no field, domain, or reducedness
condition on the base or the two algebras. No assertion is made over an
arbitrary nonnoetherian base by this proposition alone.

This is an internal lemma derived for the proof of
`Langlands.Algebra.SmoothEqualizerFibreCriterion`; it is not a literal
statement from the Stacks Project. Its proof, `noetherianGoodCriterion` in
`Langlands.Algebra.CechEqualizer.Good`, is the noetherian argument by primary
decomposition and coprimary induction. This statement module assumes none of
that proof.
The later smooth-algebra argument descends to a noetherian model before
using this criterion, so the original fibre criterion retains its full
arbitrary-base scope.
