# Smooth open neighbourhoods of versal points, from openness of versality

This module proves that openness of versality for actual Picard families
implies the published `VersalSmoothNeighbourhoodStatement`. The result is
conditional: `PicardOpennessOfVersalityStatement` is a hypothesis and is not
proved here.

Namespace: `Langlands.AlgebraicGeometry.Picard.PicardGroupoid`.

## Main result

`versalSmoothNeighbourhood_of_openness (hO : PicardOpennessOfVersalityStatement.{u}) :
VersalSmoothNeighbourhoodStatement.{u}`.

Spelled out, assume `hO`. Let:

- `R` be a commutative ring of finite type over `ℤ`;
- `X : Over (Spec R)` be proper and flat;
- `U : Over (Spec R)` be locally of finite type, with an actual line bundle `L`
  on `(relativeSpace X.hom).obj U`;
- `u₀ : U.left`, `K` a field with an `R`-algebra structure, and
  `e : U.left.residueField u₀ ≅ CommRingCat.of K`;
- `p : ArtinianTest.residueBase R K ⟶ U` satisfy
  `p.left = Spec.map e.hom ≫ U.left.fromSpecResidueField u₀`, with `p.left`
  locally of finite type;
- `IsFormallyVersalAt X.hom L p` hold.

Then there are `V : Over (Spec R)` and `j : V ⟶ U` such that `j.left` is an
open immersion, `u₀` lies in the image of `j.left`, and
`HasSmoothPointFibers X.hom ((LineBundle.pullback ((relativeSpace X.hom).map j)).obj L)`
holds.

## Proof

1. `R` is noetherian, being of finite type over `ℤ`
   (`Algebra.FiniteType.isNoetherianRing`). So `X.hom` is locally of finite
   presentation, since it is proper over a noetherian base.
2. `hO` gives an open `W` of `U.left` with `u₀ ∈ W`. Moreover `L` is formally
   versal at every locally finite-type field point of `U` with image in `W`.
3. Take `V = Over.mk (W.ι ≫ U.hom)` and `j = Over.homMk W.ι`. Then `j.left = W.ι`
   is an open immersion, and its image is `W` (`Scheme.Opens.range_ι`), which
   contains `u₀`. Also `V.hom` is locally of finite type.
4. The pulled-back bundle is the published `restrictBundle X.hom L j`.
   `PointFiberArtinianLifting.exists_smooth_pointFiberScheme_of_versal` gives
   `HasSmoothPointFibers` for it. Its hypothesis is versality at every locally
   finite-type field point `p'` of `V`. Such a `p'` gives `p' ≫ j`, which is
   locally of finite type with image in `W`. By step 2, `L` is versal at
   `p' ≫ j`. By `PointFiberArtinianLifting.isFormallyVersalAt_restrictBundle`,
   the restricted bundle is then versal at `p'`.

## Provenance

Internal infrastructure for the finite-type Picard stack atlas task. It follows
the step in the proof of The Stacks Project, Artin's Axioms, Lemma 98.13.8
(Tag 07XY, artin.pdf pp. 23–24, snapshot
`stacks-artin-axioms-approximation-2026-11-06`) where openness of versality
shrinks the chart to an open on which it is versal at every finite type point,
and that chart is then smooth (Lemmas 98.13.3 and 98.13.7). The smoothness
step uses the module `PointFiberArtinianLifting` and does not formalize those
lemmas. No cited source theorem is formalized here. Openness of versality
enters only as the hypothesis `hO`.
