# Rational function fields as algebras over the base field

Author: Worker 1420.

This internal, derived module fixes one `k`-algebra structure on the function field
`K = (𝔸(m; Spec k)).functionField` of affine space over a field `k : Type u`, for any
`m : Type u`. It also names the coordinate functions in `K`. There is no finiteness,
infinitude or characteristic assumption.

- `rationalFunctionFieldAlgebra k m : Algebra k K` is the ring homomorphism `k → K`
  corresponding, under the full faithfulness of `Spec` (`Spec.preimage`), to the
  structure morphism `Spec K → Spec k` of the published `rationalFunctionFieldOver k m`.
  That structure morphism is the generic-point morphism `Spec K → 𝔸(m; Spec k)` followed
  by the projection to `Spec k`. The definition is reducible and is declared an instance.
- `algebraBaseMap_rationalFunctionField`: with this structure, the published
  `algebraBaseMap k K = Spec.map (algebraMap k K)` is equal to
  `(rationalFunctionFieldOver k m).hom`. The proof is Mathlib's `Spec.map_preimage`.
  Results stated for base change along `algebraBaseMap k K`, such as the Lie kernel
  comparison `Lie.kernelBaseChangeLinearEquiv`, therefore apply to base change along the
  structure morphism used by `ReducesRationalFunctionFields` and
  `HasSmallerTorusConjugatorReduction`.
- `rationalFunctionFieldCoordinate k m i : K` is the germ at the generic point of the
  global coordinate function `AffineSpace.coord (Spec k) i` of `𝔸(m; Spec k)`
  (Mathlib's `Scheme.germToFunctionField` on the whole space), that is, the image of the
  `i`-th coordinate function in `K`. No property of these elements is proved here.

Provenance: derived from the published `rationalFunctionFieldOver` and `algebraBaseMap`
and pinned Mathlib (`Spec.preimage`, `Spec.map_preimage`, `Scheme.germToFunctionField`,
`AffineSpace.coord`). It is glue for the generic semisimple-centralizer case of the
dimension induction for `MaximalTorusParameterUnirationalStatement`. No literature
statement is formalized.
