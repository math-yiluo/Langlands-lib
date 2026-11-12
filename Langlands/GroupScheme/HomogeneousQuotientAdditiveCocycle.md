# Functions on a group with prescribed additive left translation by a subgroup

Authors: Worker 1497.

Let `Q : HomogeneousQuotient j` be a homogeneous quotient `G/N` of a group scheme `G`
over `S` by a subgroup `j : N ⟶ G` (the structure
`HomogeneousQuotientFromEmbedding.HomogeneousQuotient`). Let `χ` be a natural additive
function on the points of `N`, valued in global functions of the test scheme. This
module shows that, when `G` and `G/N` are affine and `j` is a monomorphism, some global
function `f` on `G` satisfies `f(n · x) = f(x) + χ(n)` for all points `n` of `N` and `x`
of `G`.

## Provenance

This is an internal helper result for the proof of
`Langlands.GroupScheme.AffineHomogeneousQuotientReductiveStatement`. It is not a
transcription of a cited theorem. It is the step of that proof where an additive
character `χ` of a subgroup `N` is extended to a function `f` on `G` that is
translated by `χ` under left translation by `N`. This uses only that `G` and `G/N`
are affine. The descent
input is the published
`Langlands.AlgebraicGeometry.AffineAdditiveCocycle.AddCocycle.exists_coboundary`. It
says that a natural additive cocycle on an affine, flat and surjective scheme over an
affine base is the coboundary of one global function (faithfully flat descent through
the Amitsur complex).

## Declarations

All of these are in the namespace
`Langlands.GroupScheme.HomogeneousQuotientAdditiveCocycle`, with
`{S : Scheme} {G N : GroupScheme S} {j : N ⟶ G} (Q : HomogeneousQuotient j)`.

- `leftProjection Q : G.X ⟶ Q.scheme`, defined as `(𝟙 G.X)⁻¹ ≫ Q.projection`, the
  map `g ↦ π(g⁻¹)`. `comp_leftProjection` says `x ≫ leftProjection Q = x⁻¹ ≫
  Q.projection`.
- `leftProjection_eq_iff Q a b`: for points `a b : T ⟶ G.X`, the images under
  `leftProjection Q` agree if and only if `a * b⁻¹` lies in the range of `j`. This is
  the field `Q.fibers` applied to `a⁻¹` and `b⁻¹`.
- `witness Q a b h : T ⟶ N.X`, with `witness_spec : witness Q a b h ≫ j.hom.hom =
  a * b⁻¹`. It is chosen from the range membership above. `eq_witness [Mono j.hom.hom]`
  says that any point `n` with `n ≫ j.hom.hom = a * b⁻¹` equals the witness.
- `cover Q : Over Q.scheme.left`: the scheme of `G` over `G/N` through
  `leftProjection`. `baseObj Q Z` views a test scheme `Z` over `G/N` as a scheme over
  `S`. `basePoint Q a : baseObj Q Z ⟶ G.X` views a point of `cover Q` as a point of
  `G`. `basePoint_leftProjection` says that two such points have the same image under
  `leftProjection Q`.
- `cocycle Q χ hχ hadd [Mono j.hom.hom] : AddCocycle (cover Q)`: the cocycle
  `(a, b) ↦ χ(n)`, where `n` is the witness with `n ≫ j = a * b⁻¹`. Here
  `χ : ∀ {T : Over S}, (T ⟶ N.X) → Γ(T.left, ⊤)` and the hypotheses are
  - `hχ : χ (t ≫ n) = t.left.appTop (χ n)` (naturality in the test scheme), and
  - `hadd : χ (n * m) = χ n + χ m` (additivity).

  Naturality of the cocycle follows from `hχ` and uniqueness of witnesses. The
  cocycle identity follows from `hadd`, since `(a * b⁻¹) * (b * c⁻¹) = a * c⁻¹`.
- `exists_leftTranslate [Mono j.hom.hom] [IsAffine G.X.left]
  (hQ : IsAffine Q.scheme.left) χ hχ hadd`:

  `∃ f : Γ(G.X.left, ⊤), ∀ {T : Over S} (n : T ⟶ N.X) (x : T ⟶ G.X),
  ((n ≫ j.hom.hom) * x).left.appTop f = x.left.appTop f + χ n`.
- `exists_leftTranslate_of_isAffineHom [IsAffine S] [Mono j.hom.hom]
  [IsAffine G.X.left] (hQ : IsAffineHom Q.scheme.hom) χ hχ hadd`: the same
  conclusion, where `G/N` is affine because it is affine over the affine base `S`.

## Proof of `exists_leftTranslate`

The map `cover Q` is the inverse map of `G` (an isomorphism) followed by
`Q.projection`, which is smooth and surjective by the fields of `Q`. So `cover Q` is
flat and surjective, and its source `G` is affine. With `G/N` affine,
`AddCocycle.exists_coboundary` gives `β : Γ(G.X.left, ⊤)` with
`cocycle(a, b) = a*β - b*β` for all pairs of points of `cover Q`. Take `f := β`.

Given `n : T ⟶ N.X` and `x : T ⟶ G.X`, put `y := (n ≫ j) * x`. Then `y * x⁻¹ = n ≫ j`,
so `y` and `x` have the same image under `leftProjection Q`. View `T` as the scheme
`Z` over `G/N` through `x ≫ leftProjection Q`, and view `y` and `x` as points of
`cover Q` over `Z`. The witness for this pair is `n` (by `eq_witness`). So the
coboundary identity reads `χ n = y*β - x*β`, which is the claim.
