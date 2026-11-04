# Points of the spectrum of a Hopf algebra over affine tests

Worker 1395 wrote this module. Let `R` be a commutative ring, `A` an object of
`CommHopfAlgCat R` and `Y` a commutative `R`-algebra. The module describes the
points of the group scheme `(hopfSpec R).obj (op A)` with values in the affine
scheme `(algSpec R).obj (op Y)` by `R`-algebra maps `A → Y`. Products of points
correspond to convolution, the identity point to the counit, and composition
with `Spec` of a Hopf algebra map to precomposition. This is the Yoneda
description of an affine group scheme by its coordinate Hopf algebra. It is an
internal helper for the proof of
[`CentralTorusExtensionStatement`](Torus/CentralExtensionProof.md); the
statements are standard and are not taken from a source.

## Contents

* `cogroup A`: the cogroup object of `CommAlgCat R` attached to `A` by Mathlib's
  equivalence `commHopfAlgCatEquivCogrpCommAlgCat`, as a group object of the
  opposite category.
* `cogroupPoint f : op Y ⟶ (cogroup A).X`: the point of that group object
  classified by an algebra map `f : A →ₐ[R] Y`, namely
  `(CommAlgCat.ofHom f).op`. `cogroupPoint_unop_hom` recovers `f`.
* `cogroupPoint_mul`: the product of the points of `f` and `g` is the point of
  `lift f g ∘ Δ` (convolution). `cogroupPoint_one`: the identity point is the
  point of `algebraMap ∘ ε`. Both follow from Mathlib's definitions of the
  multiplication and unit of `Hom` into a group object (`Hom.mul_def`,
  `Hom.one_def`).
* `specPoint f := (algSpec R).map (cogroupPoint f)`: the point of `Spec A` over
  `Spec Y` classified by `f`.
* `specPoint_injective`, `exists_specPoint`: `specPoint` is a bijection, because
  `algSpec R` is fully faithful.
* `specPoint_mul`, `specPoint_one`: `specPoint` turns convolution into the
  product of points and `algebraMap ∘ ε` into the identity point. These follow
  from the cogroup versions, because `algSpec R` preserves products of points
  (`Functor.map_mul`, `Functor.map_one`).
* `cogroupPoint_comp_map`, `specPoint_comp_map`: for a Hopf algebra map
  `ψ : B ⟶ A`, composing the point of `f` with `(hopfSpec R).map ψ.op` gives
  the point of `f ∘ ψ`.

The equations are proved at the level of `cogroup A` and then pushed through
`algSpec R` with `Functor.map_comp`, `Functor.map_mul` and `Functor.map_one`.
