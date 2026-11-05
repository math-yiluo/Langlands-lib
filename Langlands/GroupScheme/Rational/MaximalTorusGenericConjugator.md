# Generic conjugators of a maximal torus over rational function fields

Author: Worker 1420.

This internal, derived module states a form of the maximal-torus
unirationality problem that does not mention the parameter scheme. It proves
that this form implies the published target, and it proves the case where
the torus is normalized by the whole group. The field `k : Type u` is
arbitrary; there is no infinitude, perfection or characteristic assumption.

`HasGenericTorusConjugator j₀` is the proposition that, for some finite
coordinate type `n : Type u`, there are a scheme `X` over `Spec k`, a
morphism `π : X → rationalFunctionFieldOver k n` over `k` and a morphism
`g : X → G.X` over `k`. Here `π` is flat, surjective and quasi-compact on
underlying schemes, and `g` has dense underlying range in `G`. In addition,
`TorusConjugateDescends j₀ π g` holds: test points of `X` with equal images
under `π` give points of `G` that differ by a point of the all-test torus
normalizer. Informally, `g` is a generic point of `G`, defined over a
faithfully flat cover of the spectrum of a purely transcendental field
`k(x_i : i ∈ n)`. The conjugates of the torus by the two pullbacks of `g` to the
kernel pair of that cover agree. This module neither constructs nor uses a
torus over `k(x_i : i ∈ n)`. What is descended, in `MaximalTorusParameterDescent`,
is the parameter point `g ≫ q` of a supplied parameter map `q`. The predicates
`TorusConjugateDescends` and `rationalFunctionFieldOver` are those of
`MaximalTorusParameterDescent`.

`HasGenericTorusConjugator.isUnirational` proves `IsUnirational k Q` for every
actual parameter map `q : G.X → Q` of `j₀`. It applies
`IsMaximalTorusParameter.isUnirational_of_torusConjugateDescends`
to the supplied data.

`hasGenericTorusConjugator_of_normalizer_eq_top` assumes that every point of
`G`, over every test scheme, lies in `torusNormalizer j₀`. It also assumes that
`G.X.hom` is flat and quasi-compact, which holds for the smooth affine groups of the
target. Its witness takes `n` empty, `X` the fiber product of `G.X` with
`rationalFunctionFieldOver k n` over `Spec k`, `π` the second projection and `g`
the first projection. Flatness and quasi-compactness of `π` are base changes
of those of `G.X.hom`. `G.X.hom` is surjective because the identity section
is a section of it, so `π` is surjective by Mathlib's `Scheme.Pullback.range_snd`. The structure map
of `rationalFunctionFieldOver k n` is surjective, because its source is the
nonempty spectrum of a field and its target is a single point. Hence `g` is
surjective by `Scheme.Pullback.range_fst`, so it has dense range. The descent condition holds
because every point is in the normalizer.

`MaximalTorusGenericConjugatorStatement` quantifies `HasGenericTorusConjugator j₀`
over every field `k : Type u`, every group scheme `G` over `Spec k` that is
smooth, affine and connected, and every maximal torus `j₀`. These are exactly
the group hypotheses of `MaximalTorusParameterUnirationalStatement`.
`maximalTorusParameterUnirational_of_genericConjugator` proves that this
statement implies `MaximalTorusParameterUnirationalStatement.{u}`, using
`HasGenericTorusConjugator.isUnirational` for each supplied `Q` and `q`.

Provenance: derived from the helper modules `MaximalTorusParameterDescent` and
`UnirationalSpreading`, the published `torusNormalizer` and
`IsMaximalTorusParameter`, and pinned Mathlib fiber products of schemes. The
generic conjugator statement is modeled on the role of the generic Cartan
subgroup over a purely transcendental function field in the proof of SGA 3,
Exposé XIV, Théorème 6.1. It is not claimed to be equivalent to that theorem,
and no literature statement is formalized. This module does not prove
`MaximalTorusGenericConjugatorStatement` beyond the normalizer case. That
construction is the remaining substance of the unirationality target.
