module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties
public import StacksFrontier.RingTheory.Support.Basic
public import StacksFrontier.Topology.Dimension.Krull
import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# The support of a module on a fibre

Let `R → S` be a ring map, let `M` be a finite `S`-module and let `r` be a prime of `R`. The
support of the fibre module `M ⊗_R κ(r)` over the fibre ring `κ(r) ⊗_R S` is the subject of
this file. Two descriptions of it are proved.

The first is a *dictionary*: `Spec(κ(r) ⊗_R S)` is the fibre of `Spec(S) → Spec(R)` over `r`,
by `PrimeSpectrum.preimageHomeomorphFiber`, and under that identification the support of the
fibre module is the part of `Supp_S(M)` lying over `r`. That part is `Module.fiberSupport`, and
the identification is `Module.fiberSupportHomeomorph`. The point of the dictionary is that the
fibre support is a subspace of `Spec(S)` and so can be compared along a map of `R`-algebras
without base changing the map; the price is that it is not closed, being an intersection of a
closed set with a fibre.

The second is the behaviour of the fibre support along an *integral* extension `B → A` of
`R`-algebras: at a prime of `B` over which there is exactly one prime of `A`, the fibre support
upstairs and the fibre support downstairs have the same local dimension. This is
`Module.topologicalKrullDimAt_fiberSupport_eq_of_isIntegral`, the fibre-by-fibre form of
`Module.topologicalKrullDimAt_support_eq_of_isIntegral`.

## Main definitions

* `Module.fiberSupport R S M r` is the part of `Supp_S(M)` lying over the prime `r` of `R`.
* `Module.fiberSupportHomeomorph` identifies the support of the fibre module over the fibre
  ring with `Module.fiberSupport`.

## Main results

* `Module.support_tensorProduct_eq_preimage_comap`: the support of `S ⊗_R M` for a finite
  `R`-module `M` is the inverse image of `Supp_R(M)`.
* `Module.image_comap_support_fiber`: **the support of the fibre module, pushed into `Spec(S)`,
  is the part of the support of `M` lying over `r`.**
* `Module.topologicalKrullDimAt_support_fiber`: the local dimension of the support of the fibre
  module at a prime of the fibre ring is the local dimension of `Module.fiberSupport` at the
  corresponding prime of `S`.
* `Module.topologicalKrullDimAt_fiberSupport_eq_of_isIntegral`: **the local dimension of the
  fibre support is unchanged by an integral extension at a prime with a unique prime above
  it.**

## Implementation notes

The `S`-algebra structure on the fibre ring `κ(r) ⊗_R S` is `Algebra.TensorProduct.rightAlgebra`,
made a local instance here. It is not a global instance — the action of `S` on `S ⊗_R S` would
be ambiguous — and it is the structure in which `Module.DevissageStageData.Pointed` records the
conditions of Stacks 05HZ that mention the fibre module, so the statements below are directly
applicable there.

The map `Spec(κ(r) ⊗_R S) → Spec(S)` used throughout is contraction along
`algebraMap S (κ(r) ⊗_R S)`, which is `Algebra.TensorProduct.includeRight`. That it is a
topological embedding with image the fibre is read off `PrimeSpectrum.preimageHomeomorphFiber`,
whose inverse is that contraction by `rfl`.

`IsClosedMap.restrictOfIsClosedOfPreimage` takes the subset of the source as a set `U'`
together with an equation `U' = f ⁻¹' U` rather than as the inverse image itself: the set a
consumer has in hand is the fibre of a *composite* map, equal to but not syntactically the
inverse image of the fibre downstairs.

## References

* [Stacks Project, Tag 00L1](https://stacks.math.columbia.edu/tag/00L1)
* [Stacks Project, Tag 0BUR](https://stacks.math.columbia.edu/tag/0BUR)
-/

@[expose] public section

open TensorProduct TopologicalSpace

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- **Stacks 0BUR for the tensor model of a base change.** The support of `S ⊗_R M` for a
finite `R`-module `M` is the inverse image of `Supp_R(M)` under `Spec(S) → Spec(R)`. -/
public theorem Module.support_tensorProduct_eq_preimage_comap {R S M : Type*} [CommRing R]
    [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Module.support S (TensorProduct R S M) =
      PrimeSpectrum.comap (algebraMap R S) ⁻¹' Module.support R M :=
  (IsBaseChange.of_equiv (LinearEquiv.refl S (TensorProduct R S M))
    (f := TensorProduct.mk R S M 1) (fun _ => rfl)).support_eq_preimage_comap

namespace PrimeSpectrum

section Fiber

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

end Fiber

section Tower

variable {R B A : Type*} [CommRing R] [CommRing B] [CommRing A] [Algebra R B] [Algebra R A]
  [Algebra B A] [IsScalarTower R B A]

end Tower

end PrimeSpectrum

namespace Module

section Fiber

variable (R : Type*) [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
  (M : Type*) [AddCommGroup M] [Module S M] (r : Ideal R) [r.IsPrime]

end Fiber

section Tower

variable {R B A M : Type*} [CommRing R] [CommRing B] [CommRing A]
  [Algebra R B] [Algebra R A] [Algebra B A] [IsScalarTower R B A]
  [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower B A M]

end Tower

end Module

end
