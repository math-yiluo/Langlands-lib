# Actual adjunction and quotient extraction

Author: Worker 526. The namespace is
`Langlands.ActualQuotientRealBlock`. This internally specializes the
quotient-block algebra to actual upper normalized induction and its
normalized opposite Jacquet module. Field, coarse-carrier and
outer-carrier universes remain independent.

`oppositeMap` restricts the normalized Jacquet map along the existing
product-Levi equivalence. Its endpoints are exactly the bundled
`CuspidalJacquetMultiplicity.oppositeJacquet` representations.
`oppositeMap_surjective` lifts an actual coinvariant representative
through the supplied ambient surjection.

`nonzeroAdjunctionMap` applies public standard second adjointness to
admissible inputs. A surjection onto a nontrivial outer carrier is nonzero;
the linear adjunction equivalence gives a nonzero map from its inducing
representation into the opposite Jacquet module of that outer target.
This map need not be identified with the whole-induction embedding.

`quotientRetraction` takes an arbitrary irreducible analytically tempered
coarse representation, its real twist, and an arbitrary irreducible
actual outer quotient. Public relative admissibility proves every
adjunction admissibility condition, character twisting proves
irreducibility of the coarse twist, and `TemperedCoarseRealBlock` puts
the entire coarse twist in its real block at `size k * t k`.

Its remaining hypotheses are finite full-central operator spans on the
whole induced opposite Jacquet module and the quotient opposite Jacquet
module, together with actual maps `i,r` whose composite fixes each
open-kernel generalized full-central space with that real part. The
same maps are used for all those characters. Supremum induction extends
this identity to the grouped block. The quotient algebra, using the
nonzero adjunction map, proves that the opposite quotient map composed
with `i` is injective and constructs an actual global `rQ` back to the
coarse twist. It is a left inverse on that twist, and the reverse
composite fixes the quotient's entire selected real block.

`quotientRetractionOfFiniteGeneration` derives both central-action
hypotheses from `oppositeJacquetCentralAction`. Relative admissibility
applies to the whole induction and its actual quotient. Irreducibility
makes the quotient finitely generated over its group algebra; finite
generation of the whole induction remains an explicit input here.

The implemented proof uses the published adjunction, admissibility and
twisting results and the displayed generalized-block algebra. It retains
the opposite Jacquet module of the specified quotient itself and all
central nilpotents. It requires no fine-support map or quotient of a
fine ambient induction.
