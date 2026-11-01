# The actual derived unit on complexes of acyclic terms

Authors: Worker 595 (proof construction and initial documentation), Worker 310
(interface verification and final documentation).

This module implements the internal comparison specified by
`Langlands.Cohomology.AcyclicTermsDerivedUnitStatement`. Its final theorem
`Langlands.Cohomology.acyclicTermsDerivedUnitStatement` has exactly that
proposition as its type, with six independent universe parameters.

For an additive left exact functor `F : C ⥤ D` between the stated abelian
categories, with enough injectives in `C`, the hypothesis says that every term
of a bounded-below integer-indexed complex `K` is acyclic for each positive
classical right derived functor of `F`. The conclusion concerns Mathlib's actual
unit `F.rightDerivedFunctorPlusUnit.app K`: the map from the derived-category
image of the termwise image of `K` to the bounded-below right derived functor
applied to the derived-category image of `K`. No hypothesis is imposed on the
homology of `K`.

The implemented proof has two steps. First,
`AcyclicComparison.quasiIso_map_of_acyclic_terms` shows that applying `F`
termwise preserves a quasi-isomorphism `f : K ⟶ L` when both bounded-below
complexes have acyclic terms. Its mapping cone is acyclic because `f` is a
quasi-isomorphism. If `K` and `L` vanish below `m` and `n`, respectively, the
cone vanishes below `min m n - 1`. Each cone term is isomorphic to the binary
biproduct of the appropriate terms of `K` and `L`, so its positive derived
functors vanish by the published biproduct and isomorphism lemmas. The Library's
`AcyclicComparison.acyclic_map` therefore makes the termwise image of the cone
acyclic. The canonical comparison of the image of a cone with the cone of the
image map then proves that `F f` is a quasi-isomorphism.

Second, `AcyclicComparison.isIso_derivedUnit_of_acyclic_terms` chooses a
bounded-below injective replacement `i : K ⟶ L` using Mathlib's
`CochainComplex.Plus.exists_quasiIso_injective`. Every term of `L` is injective
and hence acyclic for the positive right derived functors of `F`. The first
step makes `F i` a quasi-isomorphism. Localization thus sends both `i` and
`F i` to isomorphisms. In the naturality square of the actual derived unit,
the unit at the injective complex is an isomorphism by Mathlib's instance,
and the two morphisms induced by `i` are isomorphisms. The naturality equality
and cancellation of the right isomorphism imply invertibility of the unit at
`K`. The final theorem applies this construction to all the parameters of the
published proposition.

The provenance is internal. This proof extends the published bounded-below
acyclic-complex argument in
`Langlands.Cohomology.AcyclicResolution.ComparisonProof` using Mathlib's mapping
cones, injective replacements, localization, and actual derived-functor unit.
It does not invoke acyclicity of the homology of `K`, geometric vanishing, or
any caller-supplied derived comparison. It supplies the generic comparison;
its specialization to scheme-module cohomology is a separate construction.
