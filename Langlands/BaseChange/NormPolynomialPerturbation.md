# Cyclic norms of polynomial perturbations

This module gives the algebraic steps for parts (a) and (c) of
`NormNeighbourhoodStatement`. The perturbation calculation specializes the norm
argument on a maximal torus in Henniart–Lemaire, *Changement de base et
induction automorphe pour GL_n en caractéristique non nulle*, Mém. SMF 124
(2011), II.2.10, printed p. 71. It uses the cyclic norm and association of
`Langlands.BaseChange.Norm`, following I.1.2 and I.2.1–2 of the same source.

The base change of an invertible matrix `s` is fixed by every power of `σ`. When
it commutes with `δ`, it also commutes with every image of `δ` under those
powers. Induction on the length of the ordered norm product then gives
`N(δ s_E) = N(δ) s_E^l`. With `δ = 1`, this shows that `s^l` is a norm with
witness `s_E`.

For a norm `γ`, association gives `x` with `x⁻¹ N(δ₀) x = γ_E`. The
twisted conjugate `δ = x⁻¹ δ₀ σ(x)` has norm `γ_E` because `σ^l = 1`. The
identity `σ(N(δ)) = δ⁻¹ N(δ) δ`, together with fixedness of `γ_E`, implies
that `δ` commutes with `γ_E`. The matrix of `s_E` is a polynomial in the
matrix of `γ_E`, since base change respects addition, scalar multiplication,
and products. Thus `δ` commutes with `s_E`, and the product calculation supplies
the norm witness `δ s_E` for `γ s^l`. Conjugacy invariance of association
then yields `g γ s^l g⁻¹` as a norm.

The proof uses commutative coefficient rings and the relation `σ^l = 1` in
the perturbation theorem. It therefore applies to all cyclic algebras in the
neighbourhood statement, including products of fields.
