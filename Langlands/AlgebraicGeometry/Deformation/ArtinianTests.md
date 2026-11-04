# Augmented local Artinian algebra tests

This internal construction assembles Mathlib's actual commutative algebras,
over-categories, local Artinian ring facts and spectrum functor. Its ring
and scheme assertions are proved from those APIs. It introduces no
external deformation theorem or existence assumption.

Fix a commutative ring \(k\), a field \(K\), and an algebra structure
\(k\to K\), all in arbitrary universe \(u\).
`ArtinianTest k K` is the full subcategory of augmented \(k\)-algebras
whose objects are local Artinian \(k\)-algebras \(A\) with a specified
surjective \(k\)-algebra map \(\epsilon_A:A\to K\). More precisely,
the ambient category is `Over (CommAlgCat.of k K)`, so \(A\) is an
object of the \(k\)-algebra category equipped with a map *to* \(K\).
No map \(K\to A\), section of the augmentation, or coefficient field
inside \(A\) is selected or required.

`algebra` and `augmentation` expose the actual algebra and map, and
`mk` bundles any such test. `toAlgHom` exposes a morphism as the actual
\(k\)-algebra homomorphism \(q:A\to B\).
`augmentation_comp` states precisely
\(\epsilon_B\circ q=\epsilon_A\); `homMk` constructs a morphism from
that same condition. The identity and composition formulas are the
ordinary algebra-homomorphism formulas.

`ker_augmentation` proves that \(\ker\epsilon_A\) is the maximal ideal
of \(A\), using surjectivity onto the field. `isLocalHom` proves that
every compatible arrow is local: the composite with the target
augmentation is the local source augmentation, so locality follows
from Mathlib's localness-of-a-composite criterion. The arrow itself
need not be surjective.
`ker_le_maximalIdeal` follows by applying the augmentation to an
element killed by the arrow.

`maximalIdeal_isNilpotent` identifies the maximal ideal with the
Jacobson radical of zero and uses nilpotence of that radical in an
Artinian ring. `augmentation_ker_isNilpotent` then applies the kernel
identification. These facts concern the actual ideals, not a chosen
presentation or a split extension.

`residueBase k K` is \(\operatorname{Spec} K\) over
\(\operatorname{Spec} k\), and `base A` is the corresponding
\(\operatorname{Spec} A\). `reduction A` is the actual spectrum map
induced by \(\epsilon_A\), with its triangle over \(k\).
`baseMap q` is the actual spectrum map
\(\operatorname{Spec} B\to\operatorname{Spec} A\).
The identity, composition, and residue-triangle equations follow
from spectrum functoriality and augmentation compatibility.

`pointedTest A` retains that specified residue map as an object of
the under-category of `residueBase k K` inside the scheme slice
over \(\operatorname{Spec} k\). `pointedMap q` retains the same
triangle for an arrow. `pointedSpec` packages these into a
contravariant functor on all augmented Artinian tests.
`baseMap_isClosedImmersion` proves that a surjective algebra arrow
induces a closed immersion, and `reduction_isClosedImmersion`
applies this fact to every augmentation.

Finally, `IsElementarySurjection q` is the explicit internal
convention that \(q\) is surjective and the maximal ideal of its
source annihilates its kernel:
\(\mathfrak m_A\ker q=0\). No one-dimensional-kernel requirement is
included. `IsElementarySurjection.ker_sq` proves
\((\ker q)^2=0\) from \(\ker q\subseteq\mathfrak m_A\) and ideal
multiplication monotonicity. This module does not claim a
factorization into elementary surjections, a lifting property,
formal versality, or algebraization.
