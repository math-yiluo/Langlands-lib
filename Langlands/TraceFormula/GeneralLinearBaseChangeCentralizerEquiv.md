# Twisted centralizers of related rational points of `Res_{L/K} GL_n` and `GL_n`

Module `Langlands.TraceFormula.GeneralLinearBaseChangeCentralizerEquiv`, namespace
`Langlands.TraceFormula`. It uses the notation of
`Langlands.TraceFormula.GeneralLinearBaseChangeNormPairing` (`GLₙ`, `Wₙ`, `Θₙ`, the matrix
coordinates `Φ = cyclicWeilAdelicMap K L n` and `GeneralLinearGroupPoints.adelicHomeomorph`,
the ordered norm `N`).

The module identifies the `θ`-centralizer of a rational point `r` of `Wₙ(𝔸_K)¹` with the
centralizer of a related rational point `q` of `GLₙ(𝔸_K)¹` whose coordinate is regular
semisimple. This is the isomorphism of centralizers `G_{δσ} ≅ G_γ` of Henniart–Lemaire
(*Changement de base et induction automorphe pour GL_n en caractéristique non nulle*, I.2.3,
printed pp. 13–14): the `σ`-centralizer of `δ` is an inner form of the centralizer of an
associated `γ` (p. 13), hence isomorphic to it when `γ` is regular (p. 14). Arthur–Clozel
(*Simple algebras, base change, and the advanced theory of the trace formula*, Chapter 1)
prove the inner-form statement in §1 (printed p. 3) and use the isomorphism in §4 in the
comparison leading to (4.6) (printed p. 44). The module proves it for the adelic points of
norm one and a regular semisimple rational `q`. The related points are those of the relation
"`N(δ)` is conjugate to `γ`" of Henniart–Lemaire I.2.2; see
`Langlands.TraceFormula.GeneralLinearBaseChangeNormPairing`.

## Regularity

`IsRegularSemisimple` (module `Langlands.JacquetLanglands.RegularElliptic`) means that the
characteristic polynomial is separable.

- `isRegularSemisimple_of_localProjection_rational`: a rational matrix whose component at a
  finite place is regular elliptic (`IsRegularElliptic`) is regular semisimple. The
  characteristic polynomial of the component is the image of that of the matrix
  (`Matrix.charpoly_map`), and separability descends (`Polynomial.separable_map`).
- `isRegularSemisimple_of_baseChange`: if the scalar extension of `b ∈ GL_n(K)` to `L` is
  regular semisimple, so is `b`, by the same argument.
- `isRegularSemisimple_of_baseChangeNormRelated`: let `r` and `q` have rational coordinates
  `a` and `b`, with `Φ(N(r)) y = y ι(b)` for a rational `y`. If `Φ(N(r))` is regular elliptic at
  a finite place `w` of `L`, or the coordinate of `q` is regular elliptic at a finite place `v`
  of `K`, then `b` is regular semisimple. In the first case `N(a)` is regular semisimple and
  conjugate to the base change of `b` (`isRegularSemisimple_conj_iff`), and
  `isRegularSemisimple_of_baseChange` applies. In the second case
  `isRegularSemisimple_of_localProjection_rational` applies to `b`.

## Coefficient extension

`adelicCoefficientExtension : AdelicGL K n →ₜ* AdelicGL L n` is entrywise application of the
adele inclusion `𝔸_K → 𝔸_L` (`adeleInclusion`), as a continuous homomorphism. Results:
`adelicCoefficientExtension_apply` (its definition), `adelicCoefficientExtension_rational`
(on rational matrices it is `baseChange K L n`), `adelicCoefficientExtension_injective`,
`determinantNorm_adelicCoefficientExtension` (the absolute value of the determinant is raised
to the power `[L : K]`), `adelicCoefficientExtension_mem_determinantNormOne_iff` (norm one is
preserved and reflected), `adelicEquiv_adelicCoefficientExtension` (the entrywise Galois
action fixes its image, for `IsCyclicAlgebra σ l`) and
`adelicCoefficientExtension_mem_range_rational_iff` (rational exactly when the extension is
rational, for `IsCyclicAlgebra σ l`).

## Centralizers in `GL_n`

- `mem_centralizer_iff_commute_adelicHomeomorph`: `z` is in the centralizer of `q` in
  `GLₙ(𝔸_K)¹` exactly when the adelic matrices of `z` and `q` commute.
- `centralizer_commutative_of_isRegularSemisimple`: if the coordinate of `q` is a regular
  semisimple rational matrix, the centralizer of `q` is commutative. Two adelic matrices
  commuting with a regular semisimple rational matrix commute with each other
  (`adelicGL_commute_of_regular_rational_centralizer`, module
  `Langlands.TraceFormula.AdelicRegularCentralizer`).
- `exists_continuousMulEquiv_of_bijective` (open mapping theorem): a continuous bijective
  homomorphism from a σ-compact topological group onto a Hausdorff Baire topological group is
  an isomorphism of topological groups. It is Mathlib's `MonoidHom.isOpenMap_of_sigmaCompact`
  turned into a `ContinuousMulEquiv`.

## The centralizer isomorphism

`exists_baseChangeCentralizerEquiv`: assume `IsCyclicAlgebra σ l`, let `r` and `q` have
rational coordinates `a ∈ GL_n(L)` and `b ∈ GL_n(K)`, with `b` regular semisimple, and let
`y ∈ GL_n(L)` satisfy `Φ(N(r)) y = y ι(q)`. Then there is
`e : twistedCentralizer Θₙ.toMonoidHom r ≃ₜ* twistedCentralizer (MonoidHom.id _) q` with

- `ι(e(x)) = y⁻¹ Φ(x) y` in `GL_n(𝔸_L)` for every `x`, where `ι` is
  `adelicCoefficientExtension` applied to the coordinate; and
- `e(x)` is rational exactly when `x` is rational.

Proof. Put `A = rational(a)`, `B = rational(y)` and `a' = B⁻¹ A σ(B)`, where `σ` acts by
`AdelicGLTransport.adelicEquiv`. From the relation and `cyclicWeilAdelicMap_norm`,
`y⁻¹ N(a) y = baseChange b`, so `N(a') = baseChange b` over `𝔸_L`. The descent of exact
regular norm centralizers (`exactRegularNormCentralizerEquiv`, module
`Langlands.BaseChange.ExactRegularNormCentralizer`) has two consequences:

- for every `x ∈ GL_n(𝔸_K)` commuting with `b`, the extension `ι(x)` fixes `a'` under
  twisted conjugation;
- every adelic `z` fixing `a'` is `ι(x)` for such an `x`.

Through the homeomorphism `en` of `Wₙ(𝔸_K)¹` with the norm-one adelic matrices
(`generalLinearWeilNormOneHomeomorph`) and `conj_mem_twistedCentralizer_iff`, the map
`F(x) = en⁻¹(B ι(x) B⁻¹)` is a continuous homomorphism from the centralizer of `q` to the
`θ`-centralizer of `r`. The determinant identity above shows that it lands in the norm-one
group. `F` is injective because `ι` and the coordinate maps are. It is surjective by the
second consequence. Both centralizers are closed (`isClosed_twistedCentralizer`), hence
locally compact and second countable, and the open mapping theorem makes `F` a topological
isomorphism. Take `e = F⁻¹`. Rationality is matched because `B` is rational and
`adelicCoefficientExtension_mem_range_rational_iff`.
