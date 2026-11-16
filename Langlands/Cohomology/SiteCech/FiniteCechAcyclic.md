# Higher-derived vanishing from a finite augmented test system

This is an internal categorical consequence of `FiniteCechSystem` and its
coefficient-lifting lemmas. The ambient category is an `R`-linear abelian
category with enough injectives, where `R` is any commutative ring.

`DerivedHomAcyclic B R F` says that, for every test object `B i` and positive
degree `n + 1`, the actual classical right-derived functor of
`Hom_R(B i, -)` evaluated at `F` is a zero `R`-module.
The main theorem proves this predicate from `K.HomAcyclic R F`, which is
positive exactness of all the supplied Hom cochain complexes.
The entry construction `K.derivedHomZeroIso R F hF i n` is the resulting
isomorphism of that actual higher-derived module with the zero module.

The proof uses coefficient dimension shifting. Embed `F` into a chosen
injective object and take its cokernel `Q`. The finite test-system result
gives surjectivity of `Hom_R(B i, I) → Hom_R(B i, Q)` and preserves the Hom
exactness predicate for `Q`. The linear Hom functor preserves limits:
its composite with the forgetful functor is representable, and that
forgetful functor reflects limits. Thus its zeroth right-derived functor
is naturally isomorphic to itself.

In degree one, the degree-zero connecting morphism is zero by the
surjectivity just proved. It is also epic because the next derived
module of the injective middle object is zero. Its target is therefore
zero. In subsequent degrees, the connecting morphism remains epic; its
source is zero by induction applied to `Q`, so its target is zero.
The proof uses the published `DerivedPlus` long exact sequence and
Mathlib's vanishing of higher right-derived functors on injectives.
Standard models of the derived categories are chosen locally in the
proof and are not additional hypotheses of the result.

No analytic geometry is constructed here. Applying this criterion to
sheaf sections still requires the finite test-system data, coefficient
Hom exactness and the natural comparison with the relevant sections
functor. The theorem does not itself prove the analytic comparison.
