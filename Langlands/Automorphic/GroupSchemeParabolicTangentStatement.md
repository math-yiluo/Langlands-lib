# The complexified archimedean tangent of a rational parabolic

Module `Langlands.Automorphic.GroupSchemeParabolicTangentStatement`, namespace
`Langlands.Automorphic.GroupSchemeFunctions`. The module makes two definitions and
states one proposition. It proves nothing about them.

## Definitions

Let `F` be a number field in an arbitrary universe and `G` an affine group scheme over
`Spec F` with `hsmooth : SmoothOfRelativeDimension d G.X.hom`. The infinite adelic points
`G(F_∞) = InfiniteAdelicGroupPoints F G` carry the Library's atlas
`smoothChartedSpace F G hsmooth` with model `smoothModel F d` and the smooth Lie group
structure `smoothLieGroup F G hsmooth`, the same structures that define
`AdelicEnvelopingAlgebra F G hsmooth` and the actual differential operators
`plotSmoothDifferential`.

- `AdelicComplexLieAlgebra F G hsmooth` is `ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ, smoothModel F d)
  (InfiniteAdelicGroupPoints F G)`: the complexification of Mathlib's Lie algebra of the
  Lie group `G(F_∞)` (the tangent space at the identity with the bracket of left-invariant
  vector fields). Its complex Lie algebra structure is Mathlib's extension of scalars
  (`LieAlgebra.ExtendScalars`). The universal enveloping algebra of this Lie algebra is
  `AdelicEnvelopingAlgebra F G hsmooth`.
- For a homomorphism `f : H ⟶ G` of affine group schemes over `F` with atlases
  `hH`, `hG`, `complexPointDifferential F hH hG f` is the complex-linear extension of the
  manifold derivative at the identity (`mfderiv`) of the map of infinite adelic points
  `H.affinePointsTarget f`, that is `x ↦ x ≫ f.hom.hom`. Both tangent spaces at the
  identity are the model spaces `smoothModel F e` and `smoothModel F d`, so this is a
  complex-linear map `AdelicComplexLieAlgebra F H hH →ₗ[ℂ] AdelicComplexLieAlgebra F G hG`.

## The proposition

`ParabolicLeviTangentGradingStatement.{u}` takes a connected reductive `G` over a number
field `F`, a parabolic subgroup `q : Q ⟶ G`, a geometric unipotent radical `iV : V ⟶ Q`, a
rational Levi subgroup `l : M ⟶ Q` with `IsIso (subgroupMultiplication l iV)`, affineness
of the underlying schemes of `G`, `M` and `V`, and atlases `hG`, `hM`, `hV` of relative
dimensions `d`, `e`, `c`. Write `g = AdelicComplexLieAlgebra F G hG`,
`dφ = complexPointDifferential F hM hG (l ≫ q)` and
`dψ = complexPointDifferential F hV hG (iV ≫ q)`. The conclusion is:

1. `g` is reductive: `LieAlgebra.radical ℂ g = LieAlgebra.center ℂ g`, in the sense of
   Humphreys, *Introduction to Lie Algebras and Representation Theory* (GTM 9), §19.1,
   printed p. 102 (PDF p. 115).
2. There is `H ∈ g` such that
   - the eigenvectors of `ad H` with integer eigenvalues span `g`;
   - `dφ` is injective, and its range is the centralizer `{Y | ⁅H, Y⁆ = 0}` of `H`;
   - the range of `dψ` is the span of the eigenvectors of `ad H` with positive integer
     eigenvalues.

So the complexified tangent of the Levi points is the zero eigenspace and that of the
radical points is the positive part of one integral grading of the reductive Lie algebra
`g`.

## Provenance

The proposition is derived; it collects, for the actual archimedean Lie groups of the
Library, standard facts on algebraic groups over fields of characteristic zero.

- J. S. Milne, *Algebraic Groups* (2022 corrected reprint), registered as
  `milne-2022-algebraic-groups`, Theorem 25.1, printed p. 547 (PDF p. 558): every
  parabolic subgroup of a reductive group is `P(λ)` for a cocharacter `λ` defined over the
  ground field. The Library proves this as `Langlands.GroupScheme.parabolicDynamic`, and
  the module `Langlands.GroupScheme.Rational.OriginalLeviCocharacter` moves `λ` into the
  given rational Levi, with centralizer the Levi image.
- Milne, Theorem 13.33(c), printed p. 266 (PDF p. 277): `Lie(Z(λ)) = g_0(λ)` and
  `Lie(U(λ)) = g_+(λ) = ⨁_{n>0} g_n(λ)`, where `g_n(λ)` is the weight space of `G_m`
  acting through `Ad ∘ λ` for the character `t ↦ t^n`. Over the actual dual-number Lie
  algebras the Library proves this as `Langlands.GroupScheme.dynamicRingLie`.
- Milne, Lemma 23.68, printed p. 507 (PDF p. 518): in characteristic zero a connected
  algebraic group is reductive exactly when its Lie algebra is reductive and its centre
  is of multiplicative type.

The element `H` corresponds to the derivative at `1` of `λ` at every archimedean place,
for which `ad H` acts on the weight space `g_n(λ)` by `n`. The proposition states its
conclusions on the Mathlib Lie algebra of the manifold `G(F_∞)` itself; it contains no
comparison map with the algebraic Lie algebra. To derive the archimedean assertions from
the algebraic ones, one identifies the Mathlib tangent Lie algebra of each `G(F_v)`, for
the Library's atlas and Mathlib's bracket, with the Lie algebra of the base change of
`G` to the completion `F_v`, compatibly with the derivatives of homomorphisms of group
schemes. At a complex place `v`, the real Lie algebra of `G(F_v)` complexifies to the
sum of the local complex Lie algebra and its complex conjugate. The two summands carry
the same integral weights, so the range descriptions apply to each summand. This module
proves neither that identification nor any of the conclusions.

## Use

The proposition supplies the tangent data for the Harish-Chandra projection of
enveloping centres onto the Levi in Mœglin–Waldspurger, *Spectral Decomposition and
Eisenstein Series* (1995), I.2.17, printed pp. 37–38 (PDF pp. 20–21), registered as
`moeglin-waldspurger-1995-growth-and-constant-terms`, for the actual infinite adelic
points and their differential operators: the zero eigenspace is the image of the Levi,
and the positive eigenvectors, being tangent to the radical, differentiate functions
that are left invariant under the radical to zero along the Levi.
