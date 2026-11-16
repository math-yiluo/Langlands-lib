# Geometric inputs for points of the analytic étale site

Author: Worker 620.

This module states three geometric prerequisites and proves that their conjunction
implies the published `GeometricPointStatement`. The prerequisites themselves are
unproved proposition definitions. The module does not prove
`GeometricPointStatement` unconditionally.

All declarations below are in
`Langlands.Analytic.SaturatedAtlasPresentation.EtaleSite`. The statements retain
the independent universes `u`, `v`, and `uL` of the target: the ground field is
`K : Type u`, the space is `X : LocalizedCategory.{u, v, v} (K := K)`, and the
complete algebraically closed ultrametric extension is `L : Type uL` with
`NormedAlgebra K L`. There is no Hausdorff hypothesis or nontrivial valuation
hypothesis.

## Geometric statements

1. `GeometricPointRefinementStatement`: if `U` and `V` are objects of the actual
   étale site of `X`, and their `L`-valued points `p` and `q` have the same image
   in `X`, there is an object `W` of that site with arrows to `U` and `V` and
   an `L`-valued point `r` mapping to the prescribed `p` and `q`.
2. `GeometricPointEqualizationStatement`: if parallel site arrows `f, g : U ⟶ V`
   agree on an `L`-valued point `p` of `U`, there is a site arrow `h : W ⟶ U`
   with `h ≫ f = h ≫ g` and an `L`-valued point of `W` mapping to `p`.
3. `GeometricPointImageLiftStatement`: if the underlying ordinary point of an
   `L`-valued point `p` of `U` belongs to the image of a site arrow `f : V ⟶ U`,
   there is an `L`-valued point `q` of `V` whose image is exactly `p`.

The third statement uses `localizedFieldPointProjection` to obtain the ordinary
point and the published `points X` functor to express image membership. Thus it
requires preservation of the prescribed chart-compatible field evaluations, not
merely an ordinary point above the same point. The aggregate
`GeometricPointGeometryStatement` is the conjunction of these three statements.

These are internal geometric formulations derived from the usual fibre-product,
diagonal, and completed-residue-field route to geometric points. They are not
literal transcriptions of numbered assertions in Berkovich.

## Implemented conditional reduction

`pointFibre_elements_nonempty` uses the identity object `X ⟶ X` and the given
point. It does not require algebraic closedness or completeness of `L`.

`pointFibre_isCofiltered_of_geometry` applies the first two statements directly
to objects and arrows of the category of elements of `pointFibre L x`. The
structure equation of a site arrow shows that every lifted point still lies
over `x`. Equality of fibre elements follows from equality of their underlying
field-valued points. The equalizing equation in the category of elements follows
from the equation between site arrows.

`pointFibre_cover_lifting_of_imageLift` first chooses an arrow in an ordinary
jointly surjective presieve whose image contains the underlying point of a
given fibre element. The third geometric statement then lifts the prescribed
field-valued point through that arrow. Its image in `X` is again `x`.

For `pointFibre_jointlySurjective_of_geometry`, this yields an inclusion from
`etalePrecoverage X` to the jointly surjective precoverage induced by
`pointFibre L x`. A private categorical helper obtains pointwise lifting squares
from cospans in the cofiltered category of elements. The published
`PointwiseCovering.isJointlySurjective_of_mem_toGrothendieck`, together with
monotonicity of `Precoverage.toGrothendieck`, then gives joint surjectivity for
every sieve of the generated topology. This step includes its pullback and
transitivity saturation; it does not identify covering sieves with raw covering
presieves.

Finally, `geometricPointStatement_of_geometry` supplies the cofilteredness
instance and the covering-sieve lifting property. Its conclusion is exactly
the published `GeometricPointStatement.{u, v, uL}`, under the explicit hypothesis
`GeometricPointGeometryStatement.{u, v, uL}`.

## Original sources and remaining obligations

Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
registered as `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`:

- §3.3, Proposition 3.3.7 and Corollaries 3.3.8–3.3.9, printed pp.63–64
  (PDF indices 60–61), supply the source geometry of the diagonal, étale base
  change and composition, and étaleness of arrows in `Ét(X)`.
- §3.4, Theorem 3.4.1 and its proof, printed pp.65–67 (PDF indices 62–64),
  compare finite étale germs at a point with finite étale extensions of its
  completed residue field.
- §4.2, Propositions 4.2.1–4.2.2 and Corollary 4.2.3, printed p.87
  (PDF index 84), give the stalk interpretation motivating the target.

To prove the three stated inputs for the Library's atlas model still requires
the analytic constructions and their compatibility with `localizedFieldPointFunctor`.
In particular, ordinary-point lifting alone does not prove the image-lifting
statement, and a categorical pullback alone does not supply the prescribed pair
of field-valued points. The conditional proofs use only the existing Library
and Mathlib APIs and the hypotheses stated in this module.
