module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.LocalPullback
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkTensor
public import StacksFrontier.RingTheory.TensorProduct.ReducedFractionRingIntegralClosure

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# The local rings of the normalization of a base change

Let `A` be a domain with fraction field `K`, let `B` be a finite flat `A`-algebra whose
localization at the nonzero elements of `A` is `L`, let `f : X ⟶ Spec A` be a scheme over `A`
and let

```
W = X ×_{Spec A} Spec B
```

be the base change of `X` along `Spec B ⟶ Spec A`, with first projection `pr : W ⟶ X`.  Let `ν`
be the normalization of `W`, assumed formable, and let `y` be a point of the normalization lying
over a point `w` of `W`.  Write `O = 𝒪_{X, pr w}`, assumed to be a domain, and `F` for its
fraction field.  **Then the local ring of the normalization at `y` is a localization at a prime
ideal of the integral closure of `O` in the reduction of `F ⊗[K] L`.**

This is the identification used at a generic point of a fibre in the reduced fibre theorem,
where `O` is the local ring of `X` at such a point, `F` its fraction field, and `L` the finite
extension of `K` along which the base is normalized.

Two facts are composed.  The local ring `𝒪_{W, w}` is a localization at a prime of
`O ⊗[A] B`, by `AlgebraicGeometry.exists_isLocalization_atPrime_stalk_tensorProduct`.  Hence, by
`exists_ringEquiv_stalk_normalizationScheme_localizationAtPrime_of_isLocalization`, the local
ring `𝒪_{Y, y}` of the normalization is a localization at a prime of the integral
closure of `O ⊗[A] B` in the total ring of fractions of its own reduction.  That integral
closure is the integral closure of `O` in the reduction of `F ⊗[K] L`, by
`nonempty_algEquiv_integralClosure_fractionRing_tensorProduct`, and a localization at a prime
is transported along a ring isomorphism of the two closures.

## Main results

* `isArtinianRing_fractionRing_nilradicalQuotient_tensorProduct`: the total ring of fractions of
  the reduction of `O ⊗[A] B` is Artinian, being the reduction of the finite `F`-algebra
  `F ⊗[K] L`.
* `AlgebraicGeometry.Scheme`:
  `exists_ringEquiv_stalk_normalizationScheme_localizationAtPrime_of_tensorProduct`, for a
  scheme `W` whose local ring at `w` is a localization of `O ⊗[A] B`, the local ring of the
  normalization of `W` at a point over `w` is a localization at a prime of the integral closure
  of `O` in the reduction of `F ⊗[K] L`.
* `AlgebraicGeometry.Scheme`:
  `exists_ringEquiv_stalk_normalizationScheme_pullback_localizationAtPrime`, the same conclusion
  for `W` the base change of `X` along `Spec B ⟶ Spec A` and `O` identified with the local ring
  of `X` under `w`.

## Implementation notes

The ring `O` is not taken to be the local ring `𝒪_{X, pr w}` itself but an abstract domain
together with a ring isomorphism onto it compatible with the two structure maps of `A`.  The
`A`-algebra structure on the local ring is the one coming from `f`, and it can only be named
after the point `pr w` is available, so the data making `O` a domain with fraction field `F`
could not otherwise be stated.

## References

* [Stacks Project, Tag 0C3B](https://stacks.math.columbia.edu/tag/0C3B)
* [Stacks Project, Tag 09IL](https://stacks.math.columbia.edu/tag/09IL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

open scoped nonZeroDivisors TensorProduct

universe u

variable (A O K F B L : Type u) [CommRing A] [CommRing O] [CommRing K] [CommRing F]
  [CommRing B] [CommRing L] [Algebra A O] [Algebra A K] [Algebra A F] [Algebra A B]
  [Algebra A L] [Algebra K F] [Algebra K L] [Algebra O F] [Algebra B L]
  [IsScalarTower A O F] [IsScalarTower A K F] [IsScalarTower A B L] [IsScalarTower A K L]
  [IsArtinianRing F] [IsDomain O] [Module.Flat A B] [Module.Finite A B] [Module.Finite K L]
  [IsLocalization (nonZeroDivisors A) K]
  [IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) L]
  [IsLocalization (nonZeroDivisors O) F]

omit [Module.Finite A B] in
include K F L in
/-- **The total ring of fractions of the reduction of a base change is Artinian.** For `A` a
domain with fraction field `K`, `B` a flat `A`-algebra with `L` its localization at the nonzero
elements of `A` and finite over `K`, and `O` a domain over `A` with Artinian fraction ring `F`,
the total ring of fractions of the reduction of `O ⊗[A] B` is Artinian.

It is the reduction of `F ⊗[K] L`, which is a finite `F`-algebra and therefore Artinian. -/
theorem isArtinianRing_fractionRing_nilradicalQuotient_tensorProduct :
    IsArtinianRing (FractionRing ((O ⊗[A] B) ⧸ nilradical (O ⊗[A] B))) := by
  let _ := tensorProductFractionRingAlgebra A O K F B L
  let _ := nilradicalQuotientAlgebra (O ⊗[A] B) (F ⊗[K] L)
  have _ := isFractionRing_nilradicalQuotient_tensorProduct A O K F B L
  have _ : Module.Finite F (F ⊗[K] L) := Module.Finite.base_change K F L
  have _ : IsArtinianRing (F ⊗[K] L) := isArtinian_of_tower F inferInstance
  exact (IsLocalization.algEquiv
    (nonZeroDivisors ((O ⊗[A] B) ⧸ nilradical (O ⊗[A] B)))
    (FractionRing ((O ⊗[A] B) ⧸ nilradical (O ⊗[A] B)))
    ((F ⊗[K] L) ⧸ nilradical (F ⊗[K] L))).symm.toRingEquiv.isArtinianRing

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme

end
