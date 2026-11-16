# Algebra and spectrum interfaces for Henselian finite étale refinement

Author: Worker 607.

This module introduces the derived algebraic proposition
`Langlands.CommutativeAlgebra.LocalFiniteEtaleRefinementRingStatement.{u}`
and proves its equivalence with the unchanged published
`HenselianFiniteEtaleRefinementStatement.{u}`. Neither proposition is proved
unconditionally here.

For a commutative Henselian local ring `R : Type u`, an étale `R`-algebra
`A : Type u`, and a prime ideal `q` of `A` lying over the maximal ideal of
`R`, the algebraic proposition asks for a commutative local `R`-algebra
`R' : Type u` that is finite as an `R`-module and étale over `R`, together
with an `R`-algebra map `A → R'`. The conclusion does not retain the chosen
prime `q`, prescribe the residue extension, or require the resulting map on
spectra to be an open immersion. No finite residue field or Noetherian
hypothesis is imposed. The local ring structure entails nontriviality.

The proposition is internal infrastructure for Task 6871. Its provenance is
the translation of the published affine scheme statement by the full
faithfulness of `Spec` and Mathlib's affine criterion for étaleness. It makes
no additional original-source assertion; the mathematical provenance of the
refinement assertion remains documented in the imported statement pair.

`henselianFiniteEtaleRefinement_of_ring` proves the forward implication.
Given an affine morphism `f : Spec A → Spec R`, choose its corresponding ring
map with `Spec.preimage` and use it as the `R`-algebra structure on `A`.
`HasRingHomProperty.Spec_iff` translates étaleness. A point mapping to the
closed point supplies a prime lying over the maximal ideal. Apply the
algebraic proposition and take the spectrum of the resulting `R`-algebra map
`ψ : A → R'`. Its scalar compatibility says that the composite `R → A → R'`
is the algebra map. Contravariant functoriality of `Spec` gives precisely
`Spec ψ ≫ f = Spec.algebraMap R R'`.

`localFiniteEtaleRefinementRing_of_scheme` proves the reverse implication.
Apply the affine scheme proposition to `Spec.algebraMap R A`; the supplied
prime gives the required point over the closed point. Convert the resulting
morphism `g : Spec R' → Spec A` back to a ring map using `Spec.preimage`.
Faithfulness of `Spec` translates the factorization equation into
compatibility with scalars, so this ring map is an `R`-algebra map.

`localFiniteEtaleRefinementRing_iff_scheme` packages these implications.
Every result is uniform in the arbitrary universe `u`.
