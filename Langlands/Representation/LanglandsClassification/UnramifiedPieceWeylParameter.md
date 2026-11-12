# The actual Weyl parameter of an unramified geometric-lemma piece

This internal construction compares the original character maps of an arbitrary
represented geometric-lemma intersection datum for two parabolics with a common
Levi. It is a derived bridge between the existing common-torus, rational
conjugacy, full-parameter and normalized-real-part interfaces. It transcribes no
additional assertion from the literature.

Let `p : P → G` and `q : Q → G` be the supplied parabolics, with Levi maps
`l : M → P` and `lQ : M → Q`, and assume `lQ ≫ q = l ≫ p`. Let `D` be any
`GeometricLemmaIntersectionDatum` for a rational point `z` and these supplied
maps. Let `pres : ParabolicRootPresentation p l a` be the supplied actual root
presentation for the split component `a : A → M`. No hypothesis chooses a Weyl
representative for `z`, and `Q` need not be opposite to `P`.

The definition `ParabolicRootPresentation.normalizerComponentPullback pres n`
is the group-scheme map

```
A --pres.data.f--> T --normalizingAut(i,n).hom--> T --pres.leviTorusHom--> M.
```

Here `i = pres.data.i`, and `n` is an actual point of `normalizerPoints i`.
The direction of the torus automorphism is its forward direction.

The generic theorem `exists_normalizerPoint_of_commonSplitTorus` applies to a
connected reductive closed subgroup `j : M → G`. Two maps of a common torus into
`M`, maximal split after composition with `j` and related by conjugation by
`z`, give rational points `mS,mT` of `M` and `n : normalizerPoints i` such that

```
n.val = j(mS) * z * j(mT)^(-1).
```

Its proof uses rational maximal-split-torus conjugacy inside `M` on each of the
two maps. The resulting torus isomorphisms show that this corrected point
normalizes the fixed `i`. The proof retains both corrections and the original
point `z`.

`D.exists_normalizerPoint_sameLevi pres hLevi` specializes this construction
to the source common torus `D.t` and the transported original target common
torus `D.targetCommonTorusHom`. Their ambient maximality and the original
conjugation identity supply the generic hypotheses. It returns the displayed
factorization with `j = l ≫ p`.

For any actual component factor `b : A → D.L'` with
`b ≫ D.lQ' ≫ D.q' = a`, the original source-side map is
`b ≫ D.φ.hom ≫ D.l' ≫ D.p'`. For any correction points and normalizer point
satisfying the displayed factorization, the theorem
`D.character_comp_piece_eq_normalizerPullback` identifies the pullback of
every group character `χ : M(k) → ℂˣ` through this original map with its
pullback through `pres.normalizerComponentPullback n`.

The generic map theorem `comp_innerIso_eq_normalizer_pullback` explains this
equality. Centrality of `a` removes conjugation by the target correction
`mT`. Naturality of inner automorphisms and normalization of `i` identify the
normalizer pullback with the original map followed by conjugation by `mS`
inside `M`. Cancellation uses the closed subgroup `j`. The generic character
theorem `character_comp_eq_of_normalizerCorrection` then removes this last
conjugation because the character takes values in the commutative group `ℂˣ`.
These generic results do not require smoothness of the character.

Over a nonarchimedean local field, for an original unramified Levi character
`ψ`, the theorem
`D.normalizedRealPart_piece_eq_of_normalizerCorrection` gives

```
normalizedRealPart (ψ ∘ (b ≫ D.φ.hom ≫ D.l' ≫ D.p'))
  = rationalCharacterRestrictReal (groupHom pres.data.f)
      (relativeWeylFullRealAction i ((QuotientGroup.mk n)^(-1))
        (leviUnramifiedFullRealPart pres ψ)).
```

All rational-point topologies are the existing canonical ones. The theorem
uses the proved open kernel of the original torus restriction of `ψ`.
Normalized real-part functoriality first applies to the normalizing torus
automorphism and then to `pres.data.f`. Uniqueness of the normalizing
automorphism identifies the automorphism for `n⁻¹` with the inverse of the
one for `n`. The inverse Weyl class in the formula is required because the
existing character action is defined by inverse precomposition.

This unit proves the character comparison for arbitrary supplied same-Levi
intersection data. It does not prove nonidentity double-coset exclusion from
the Levi Weyl subgroup, a nonzero piece displacement, an opposite-cone
comparison, spectral separation, or the host regularity proposition. Those
remain subsequent steps.
