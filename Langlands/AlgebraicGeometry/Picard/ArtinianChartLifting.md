# Elementary lifting of actual Picard chart points

This is an internal construction from the actual point-fibre presheaf of
`PicardGroupoid.relative` and the elementary quotient induction in
`Deformation.ArtinianQuotients`. It introduces a lifting condition on a fixed
actual family and proves an elementary-surjection criterion for that condition.
No external deformation or algebraicity theorem is invoked.

## Data and actual points

Fix an arbitrary universe `u`, a commutative ring `k : Type u`, a field
`K : Type u` with its specified `k`-algebra structure, a scheme morphism
`f : X ⟶ Spec k`, a scheme `U` over `Spec k`, and an actual line bundle `L`
on `U ×_k X`. No geometric hypothesis on `f` or `U` is imposed.

An `ArtinianTest k K` is an actual local Artinian commutative `k`-algebra
with a specified surjective augmentation to `K`. Its arrows are all actual
augmentation-preserving `k`-algebra homomorphisms. In particular, the source
algebra is not required to have a `K`-algebra structure or an augmentation
section.

For an arbitrary scheme `T` over `Spec k`, an actual line bundle `M` on
`T ×_k X`, and a map `a : Spec A ⟶ T` over `Spec k`, the private abbreviation
`FiberPoints f L M (Over.mk a)` is the actual point type
`PseudofunctorPointFiber.Points (relative f) (Core.mk L) (Core.mk M)`.
Its elements consist of a map `x : Spec A ⟶ U` over `Spec k` and a specified
isomorphism between the ordinary pullbacks of `L` and `M` to the relative
space over `Spec A`. Neither datum is discarded or quotiented. These are the
raw point fibres on the iterated slice used in `StackAtlas`, before its
iterated-slice equivalence and universe lift.

## Restriction and lifting

For an actual algebra arrow `q : A ⟶ B` and compatible maps
`a : Spec A ⟶ T`, `b : Spec B ⟶ T`, write `w` for the equality
`baseMap q ≫ a = b`. Here `baseMap q` is the actual map `Spec B ⟶ Spec A`.
`testArrow q w` is the corresponding arrow `Over.mk b ⟶ Over.mk a`
in the slice over `T`.

`restrict f L q M w` applies the existing actual point-fibre restriction.
It pulls back the specified bundle isomorphism using the original
pseudofunctor composition comparisons. The lemma `restrict_baseMap`
identifies its base map with `baseMap q ≫ x`.

`HasLiftingFor f L q` requires this restriction to be surjective for every
actual `T`, `M`, `a`, `b`, and compatibility equality `w` as above. Thus a
prescribed point over `Spec B`, including its chosen bundle isomorphism,
must be the restriction of a point over `Spec A`. This definition applies
to every test arrow; it does not assume that `q` is surjective.

`hasLiftingFor_comp` proves closure under composition. For
`q : A ⟶ B` and `r : B ⟶ C`, the proof uses the intermediate map
`b = baseMap q ≫ a`. It lifts the prescribed point first along `r` and
then along `q`. The equality `baseMap_comp` identifies the actual slice
arrow of the composite with the composite slice arrows, and
`PseudofunctorPointFiber.restrict_comp` proves that the resulting lift
has exactly the prescribed restriction. This equality concerns the entire
point, including its specified isomorphism.

## Elementary criterion and scope

`IsFormallySmoothOnTests f L K` means `HasLiftingFor f L q` for every
surjective arrow of `ArtinianTest k K`. Surjectivity here is that of the
underlying actual algebra homomorphism.

`isFormallySmoothOnTests_iff_elementary` proves that it is equivalent to
lifting for every elementary surjection. The explicit convention from
`ArtinianTests` is surjectivity together with
`maximalIdeal A * ker(q) = 0`; it includes zero kernels and imposes no
one-dimensional-kernel condition. The forward implication takes the
surjectivity component. The reverse implication applies
`ArtinianTest.surjective_induction` to the predicate `HasLiftingFor`, using
the elementary lifting premise and `hasLiftingFor_comp`. That induction
uses the actual terminating filtration `maximalIdeal A ^ n * ker(q)` and
retains the original endpoint arrows.

This result supplies a criterion for the stated lifting condition at the
fixed residue field `K`. It does not construct a family satisfying the
condition, identify it with smoothness of representing schemes, or prove
formal versality, effectivity, algebraization, or a smooth Picard atlas.
Those remain further obligations of the field-atlas task.
