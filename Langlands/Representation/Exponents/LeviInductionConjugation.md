# Conjugation of normalized induction for rational parabolics

The conventions are those of David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, VI.1.2 (normalized parabolic induction), VI.5.4 and VI.10.1
(conjugation of inducing data). Renard uses this transport when comparing the inductions
of conjugate cuspidal data.

`leviInductionIsoOfConj` takes two actual rational parabolic data `(p, l, r)` and `(p', l', r')`
of `G`, including their Levi factors, unipotent radicals and multiplication isomorphisms.
Let `g ∈ G(k)` and `φ : M' ≅ M` identify the Levi embeddings by
`l' ≫ p' = φ.hom ≫ l ≫ p ≫ Int(g)`. If the range of `p'` is the conjugate of the range of `p`
by `g`, then `i_{p,l,r} σ ≅ i_{p',l',r'} (σ ∘ φ)` for every smooth representation `σ` of
`M(k)`. Here `σ ∘ φ` is pullback along `ambientIsoPointsEquiv φ`.

The two equations imply the corresponding point-image equations for the parabolics and
Levis. The radical equation follows from `parabolicRadical_range_eq`, which identifies
the images of geometric unipotent radicals of two presentations of the same parabolic.
The proof applies `inductionConjugationIsoApp`, whose map on induced functions is
`f ↦ f(g⁻¹ ·)`. It then identifies the transported inducing representation with
`σ ∘ φ` by the identity linear map. The Levi embedding equation ensures that the two
Levi actions agree after conjugation by `g⁻¹`.

`leviInductionConjugateIso` uses the conjugate datum `(p ≫ Int(g), e.hom ≫ l, r)`
for `e : M' ≅ M`. `leviInductionIsoOfRangeEq` takes `g = 1` and `φ = 𝟙` to compare
two presentations with the same parabolic range and the same Levi embedding. The
identity linear map identifies the resulting pullback along `𝟙` with `σ`.
