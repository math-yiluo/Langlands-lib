# Conditional native degree of the sixfold polarization

`Langlands.AbelianScheme.PolarizedFiniteLevel.SixfoldPolarizationDegreeReductionStatement`
is an internal intermediate proposition for the cubic-fibre cohomology argument.
It quantifies every published `Prerequisites P`, every field `K`, all natural
indices `g`, `d`, `n`, and every actual
`a : Datum P (Spec K) g d n`. Algebraic closure and positivity of `d` are
unnecessary for this conditional step.

Let `A = a.abelian` and `λ = a.polarization`. Multiplication by six is the actual
abelian-scheme endomorphism `(6 : ℕ) • 𝟙 A`. The proposition assumes that its
underlying scheme morphism is finite and flat and has constant native rank
`6^(2*g)`. It concludes that the actual underlying scheme morphism of `6 • λ`
is finite and flat, with constant native rank `6^(2*g) * d^2`.
`HasConstantDegree f r` is the existing predicate `∀ y, f.finrank y = r`,
using Mathlib's `Scheme.Hom.finrank` at every point of the actual target.

The polarization, its per-datum dual witness, dimension and level are those
already in `Datum`. In particular, `a.polarized` supplies that `λ` is an
isogeny and therefore finite and flat, and `a.degree` supplies its constant
native rank `d^2`. No replacement map, auxiliary degree invariant or chosen
coordinate presentation occurs in the proposition.

## Internal provenance

This is a specialization of the published
`Langlands.AlgebraicGeometry.finiteFlatConstantRankComposition` to the actual
multiplication-by-six map followed by `λ`, together with the existing datum
fields. The preadditive identity `(6 • 𝟙 A) ≫ λ = 6 • λ` identifies that
composite with the desired morphism. The dual abelian scheme is locally of
finite type over the noetherian field spectrum, so its underlying scheme
satisfies the composition theorem's locally noetherian target premise.
Finite and flat morphisms compose.

This derived packaging translates no additional external source assertion.
It is a statement only. It leaves finite flatness and the rank of
multiplication by six as explicit hypotheses; it proves no unconditional
multiplication theorem, ampleness, cohomological vanishing or Euler identity.
The unconditional `CubicFibreCohomologyStatement` remains unchanged.
