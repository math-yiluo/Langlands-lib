# Geometric inputs for points of the analytic quasi-étale site

This module states the geometric prerequisites of the published target
`QuasiEtaleSite.GeometricPointStatement` (module
`Langlands.Geometry.Analytic.QuasiEtaleGeometricPointStatement`). It then proves
that they imply the target. The prerequisites are unproved proposition
definitions, so the module does not prove `GeometricPointStatement`
unconditionally. It mirrors the published étale reduction in
`EtaleGeometricPointGeometry` and `EtaleGeometricPointPullbacks`.

All statements keep the independent universes `u`, `v` and `uL` of the target:
the ground field is `K : Type u` (complete, ultrametric), the spaces are objects
of `LocalizedCategory.{u, v, v} (K := K)`, and `L : Type uL` is a complete,
ultrametric, algebraically closed normed field with `NormedAlgebra K L`. There
is no Hausdorff, separatedness, compactness or nontrivial-valuation hypothesis.
`quasiEtale` is the Library's quasi-étale morphism property (module
`QuasiEtaleSite`).

## Localized statements (namespace `Langlands.Analytic.SaturatedAtlasPresentation`)

1. `LocalizedQuasiEtaleCompositionStatement K`: quasi-étale morphisms of the
   localized category are stable under composition
   (`MorphismProperty.IsStableUnderComposition`).
2. `LocalizedQuasiEtaleBaseChangeStatement K`: quasi-étale morphisms are stable
   under base change (`MorphismProperty.IsStableUnderBaseChange`). In every
   pullback square of the localized category whose right leg is quasi-étale,
   the parallel left leg is quasi-étale. Pullbacks along quasi-étale morphisms
   exist by the published `exists_localizedPullback_of_quasiEtale`. This is the
   quasi-étale analogue of the published `LocalizedEtaleBaseChangeStatement`.
3. `LocalizedQuasiEtaleCancellationStatement K`: if `g : Y ⟶ X` and `f ≫ g` are
   quasi-étale, then `f` is quasi-étale
   (`MorphismProperty.HasOfPostcompProperty quasiEtale quasiEtale`). Equivalently,
   an `X`-morphism between spaces quasi-étale over `X` is quasi-étale.
4. `LocalizedQuasiEtaleFieldPointPullbackStatement K L`: the functor
   `localizedFieldPointFunctor L` of `L`-valued points takes every pullback
   square having a quasi-étale leg `f` to a pullback square of types. This is
   the published `LocalizedEtaleFieldPointPullbackStatement` with the étale leg
   replaced by a quasi-étale leg.
5. `LocalizedQuasiEtaleFieldPointImageLiftStatement K L`: let `f : A ⟶ B` be
   quasi-étale and `p` an `L`-valued point of `B`. If the underlying ordinary
   point of `p`, given by `localizedFieldPointProjection`, lies in the image of
   `localizedSpaceFunctor.map f`, then some `L`-valued point `q` of `A` satisfies
   `(localizedFieldPointFunctor L).map f q = p`. The image of `q` must be the
   prescribed `p`, including its field evaluations; an ordinary point above the
   same point is not enough.

`QuasiEtaleSite.GeometricPointLocalizedInputsStatement` is the conjunction of
statements 1–3 for every `K` and statements 4–5 for every `K` and every `L` as
above. It is the declaration recorded for this candidate.

## Site-level statements (namespace `...QuasiEtaleSite`)

These are the quasi-étale versions of the three published étale site-level
statements, stated for objects and arrows of `QuasiEtaleSite X`.

- `GeometricPointRefinementStatement`: let `p` and `q` be `L`-valued points of
  objects `U` and `V` with the same image in `X`. Then some object `W` has
  arrows `f : W ⟶ U` and `g : W ⟶ V` and an `L`-valued point `r` with
  `f r = p` and `g r = q`.
- `GeometricPointEqualizationStatement`: let parallel arrows `f, g : U ⟶ V`
  agree on an `L`-valued point `p` of `U`. Then some arrow `h : W ⟶ U` satisfies
  `h ≫ f = h ≫ g`, and some `L`-valued point of `W` maps to `p`.
- `GeometricPointImageLiftStatement`: let `p` be an `L`-valued point of `U`
  whose underlying point lies in the image of an arrow `f : V ⟶ U`. Then some
  `L`-valued point `q` of `V` satisfies `f q = p`.

`GeometricPointGeometryStatement` is their conjunction.

## Implemented conditional proofs

From the site-level statements (`geometricPointStatement_of_geometry`):

- `pointFibre_elements_nonempty`: the identity `X ⟶ X` together with `x` is an
  element of `pointFibre L x`.
- `pointFibre_isCofiltered_of_geometry`: the refinement and equalization
  statements apply directly to objects and arrows of the category of elements.
  The commuting triangle of a site arrow (`MorphismProperty.Over.w`) shows that
  the lifted points still lie over `x`.
- `exists_mem_range_of_mem_quasiEtalePrecoverage`: by
  `mem_quasiEtalePrecoverage_iff`, every point of `U` has a neighbourhood that
  is a finite union of images of affinoid domains of members of a covering
  presieve. So the point lies in the image of one member of the presieve.
- `pointFibre_cover_lifting_of_imageLift`: this member and the image-lift
  statement give a fibre element over a member of the presieve.
- `pointFibre_jointlySurjective_of_geometry`: the previous step shows
  `quasiEtalePrecoverage X ≤ Types.jointlySurjectivePrecoverage.comap
  (pointFibre L x)`. `hasPointwiseLiftingSquares_of_cofiltered` obtains pointwise
  lifting squares from cospans in the cofiltered category of elements. The
  published `PointwiseCovering.isJointlySurjective_of_mem_toGrothendieck` and
  monotonicity of `Precoverage.toGrothendieck` then give joint surjectivity for
  every covering sieve of `quasiEtaleTopology X`, including pullback and
  transitivity saturation.

From the localized statements (`geometricPointGeometry_of_localized`):

- `exists_refinement_of_pullbacks` (uses composition and base change as
  instances, and statement 4): take a pullback `P` of `U.hom` and `V.hom` from
  `exists_localizedPullback_of_quasiEtale`. Base change makes `P ⟶ V`
  quasi-étale and composition makes `P ⟶ X` quasi-étale. Statement 4 makes the
  square of `L`-valued points a pullback of types, so the compatible pair
  `(p, q)` comes from a point of `P`.
- `exists_equalization_of_pullbacks` (uses composition, base change,
  cancellation and statement 4): let `P = V ×_X V` with second projection `b`
  and diagonal `d`. `b` is quasi-étale by base change, and `d` by cancellation
  because `d ≫ b = 𝟙`. Let `c : U ⟶ P` be the map `(f, g)`. Statement 4 for the
  square of `P` shows `d (f p) = c p`. The pullback `E` of `d` along `c` exists,
  and its leg `t : E ⟶ U` is quasi-étale, so `t ≫ U.hom` is an object of
  `Qét(X)`. Statement 4 for the square of `E` lifts `p` to `E`. Composing the
  square of `E` with the two projections of `P` gives `t ≫ f = t ≫ g`.
- `exists_imageLift_of_localized` (uses cancellation and statement 5): an arrow
  `f : V ⟶ U` of `Qét(X)` satisfies `f.left ≫ U.hom = V.hom`, so cancellation
  makes `f.left` quasi-étale, and statement 5 applies. Cancellation cannot be
  dropped here. Two `L`-valued points with the same underlying point and the same
  image in `X` need not coincide (their field embeddings can differ by a Galois
  conjugation), so the lift must be taken along `f.left` itself.

`geometricPointStatement_of_localized` composes the two reductions. Its type is
`GeometricPointLocalizedInputsStatement.{u, v, uL} →
GeometricPointStatement.{u, v, uL}`.

## Original sources and provenance

PDF indices below are 0-based page indices of the registered files.

Berkovich, *Vanishing cycles for formal schemes*, Invent. Math. 115 (1994),
registered as `berkovich-1994-vanishing-cycles-formal-schemes`, SHA256
`f4f7bc00cc46a0a5f72a69d7bbb220bce1d3ed9fd465aeda629f37dfc054bed1`:

- §3, printed pp.543–544 (PDF indices 4–5): the definition of quasi-étale
  morphisms and of the quasi-étale site `Qét(X)` and its coverings.
- Lemma 3.1, printed p.544 (PDF index 5): "(i) Quasi-étale morphisms are
  preserved under compositions, under any base change functor and under any
  ground field extension functor. (ii) If Y and Z are quasi-étale over X, then
  any X-morphism Z → Y is quasi-étale." Statement 1 is the composition part of
  (i), statement 2 the base-change part of (i), and statement 3 is (ii)
  rephrased as right cancellation. Ground field extension is not stated here.
  Berkovich's proof reduces to étale morphisms and Theorem 3.4.1 of the 1993
  paper.

Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
registered as `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`:

- §3.4, Theorem 3.4.1 and its proof, printed pp.65–67 (PDF indices 61–63). The
  theorem gives an equivalence between finite étale germs at a point `x` and
  finite étale algebras over its completed residue field `ℋ(x)`. For an étale
  morphism, the completed residue field of a point above `x` is therefore a
  finite separable extension of `ℋ(x)`. Affinoid domains do not change completed
  residue fields. So an embedding of `ℋ(x)` into the algebraically closed `L`
  extends to the source point; this is the source idea behind statement 5.
- §4.2, Propositions 4.2.1–4.2.2, printed p.87 (PDF index 83): the stalk
  interpretation of geometric points that motivates the target.

Statements 1–3 are formalizations of Lemma 3.1 for the Library's localized
category. Statements 4–5 and the three site-level statements are internal
(derived) formulations of the fibre-product, diagonal and residue-field route of
the target's suggested proof. They are not literal transcriptions of numbered
assertions in Berkovich. Statement 4 holds for any pullback square in the
source category, because `L`-valued points are compatible with fibre products.
The hypothesis of a quasi-étale leg only restricts it to the squares the
reduction needs, and it is the leg along which the Library constructs pullbacks.
The conditional proofs use only Mathlib, the published Library and the
hypotheses stated in this module.
