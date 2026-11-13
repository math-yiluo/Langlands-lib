# Natural maps from the non-identity self-intersection pieces vanish

This module is an internal helper. It is not stated as such in the literature. It was written
for the Lean proof `inducedProgeneratorCenterInclusion` of the centre inclusion `ℨ_Ω ⊂ ℨ_D`
(Renard 2026, VI.10.4, second Lemma, printed p. 211, PDF p. 217). Renard proves that Lemma
with the free `ℨ_D`-module structure of `R_Ω` (the first Lemma of VI.10.4) and the generic
irreducibility VI.8.5, and his proof contains no argument of this kind. In the Lean proof the
module is the local step of the kernel vanishing (`CuspidalSupport/InducedKernelVanishing`).
Consider a piece of the geometric lemma for `r_P^G ∘ i_P^G` at a double coset `P w P` with
`w ∉ M`. The module shows that every map from that piece to `σ` that commutes with the
endomorphisms of `σ` is zero. There are two cases. If the intersection parabolic subgroup of
`M` is proper, the piece itself is zero by supercuspidality. Otherwise `w` normalizes `M`, and
the vanishing needs more: the twisted equivariance of the map, the naturality of
`fullPieceEquiv`, a central element `c` of `M(F)` and a rational character `χ` with
`|χ|(w c w⁻¹) ≠ |χ|(c)` (Renard V.3.5), and the
hypothesis that no element of `M(F)` whose positive powers avoid `⁰M(F)` fixes a nonzero vector
of `σ`.

## Setting

`G` is a connected reductive group over a non-archimedean local field `F`, with the point
topology on `G(F)`. `P = M N` is a rational parabolic subgroup with rational Levi subgroup `M`
and geometric unipotent radical `N`. `z ∈ G(F)`, and `D` is an intersection datum
(`GeometricLemmaIntersectionDatum`) of the geometric lemma for the pair `(P, P)` at the double
coset of `z`. `D.pieceFunctor` is the corresponding piece functor: it sends a smooth
representation `σ` of `M(F)` to the piece of `r_P^G(i_P^G σ)` attached to that double coset.
`⁰M(F)` is `Plancherel.rationalCommonNormKernel M`, the common kernel of the norms `|χ|` of the
rational characters `χ` of `M`.

## Statement

`pieceFunctor_hom_eq_zero_of_not_mem` assumes the following.

- `z⁻¹ ∉ M(F)` (as a subset of `G(F)` through `l ≫ p`).
- `σ` is supercuspidal.
- (No fixed vectors.) If `t ∈ M(F)` and `tⁿ ∉ ⁰M(F)` for every `n > 0`, then `σ(t)` fixes
  no nonzero vector.
- `g : D.pieceFunctor σ → σ` is an `M(F)`-intertwiner with
  `g ∘ D.pieceFunctor(a) = a ∘ g` for every endomorphism `a` of `σ`.

The conclusion is `g = 0`.

## Proof

1. If `D.p'` is not an isomorphism, the intersection parabolic `P' = D.p'` of `M` is proper.
   Supercuspidality of `σ` makes the Jacquet module `r_{P'}^M σ` zero. The piece consists of
   functions with values in that Jacquet module, so it is zero too
   (`subsingleton_pieceFunctor_obj`). Then `g = 0`.
2. Otherwise `D.q'` is an isomorphism as well (`isIso_q'_of_isIso_p'_of_iso`). The datum gives an
   isomorphism `φ : M ≅ M` with `φ ∘ (l ≫ p) = (l ≫ p) ∘ Int(z⁻¹)` (`fullLeviConjugacy`), so
   `z⁻¹` normalizes `M`. Let `ψ : M(F) ≃ M(F)` be the induced map on points
   (`fullLeviPointsEquiv`, with `ψ c = φ(c)`).
3. Since `z⁻¹ ∉ M(F)`, the contrapositive of Renard V.3.5 (`leviNormalizerNormFixing`) gives a
   central `c ∈ M(F)` and a rational character `χ` with `|χ|(φ c) ≠ |χ|(c)`.
4. Let `E = fullPieceEquiv σ`. It identifies the piece with `σ ∘ ψ⁻¹`, and it is natural in `σ`
   (`fullPieceEquiv_naturality`). Put `T = g ∘ E⁻¹ : σ → σ`. Then:
   - `T(σ(ψ⁻¹ x) v) = σ(x) T(v)` for `x ∈ M(F)`, because `E⁻¹` and `g` are intertwiners;
   - `T(a v) = a(T v)` for every endomorphism `a` of `σ`, by naturality of `E` and the
     hypothesis on `g`.
5. Since `c` is central in `M(F)`, `σ(c)` is an endomorphism of `σ`. For any `v`, put
   `t = c⁻¹ ψ(c)`. Then
   `σ(t) T(v) = σ(c⁻¹) σ(ψ c) T(v) = σ(c⁻¹) T(σ(c) v) = σ(c⁻¹) σ(c) T(v) = T(v)`.
   The second equality is the twisted equivariance at `x = ψ c`, the third is step 4 with
   `a = σ(c)`.
6. No power `tⁿ` with `n > 0` lies in `⁰M(F)`. Otherwise `|χ|(t)ⁿ = 1`. Since `|χ|(t)` is a
   nonnegative real number, this gives `|χ|(t) = 1` (`pow_eq_one_iff_of_nonneg`), that is
   `|χ|(ψ c) = |χ|(c)`. This contradicts step 3.
7. By the no-fixed-vector hypothesis, `T(v) = 0` for every `v`. Hence `g(y) = T(E y) = 0` for
   every `y` in the piece.
