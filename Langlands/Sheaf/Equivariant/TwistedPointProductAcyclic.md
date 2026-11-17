# Compact acyclicity reduced to injective coefficient diagrams

This internal categorical reduction concerns the existing actual restricted smooth
point-product functor `T = coefficientRestrictedSmoothPointProductFunctor`. It uses
the independent category-morphism, category-object, group and coefficient universes
`v`, `u`, `uG` and `w`. The coefficient index and site fibers use `w`. The ordinary
support-point family may have a separate index and any topology. The hypotheses
include translation invariance, admissible refinements, the pointwise right Kan
extensions used by induction, sheafification on both sites, local smallness of the
ordinary site, and enough injectives in its module-sheaf category.

Fix an ordinary object `U` and let `Γ` be the existing
`PointSupport.sheafCompactSections J supportPoints R U`.
`compactDerivedCoefficientRestrictedSmoothPointProductIso` defines the existing
derived-composite comparison as an isomorphism, in every degree, under the
injective-coefficient vanishing hypothesis below. Its source is the right-derived
`T ⋙ Γ` evaluated on the coefficient diagram; its target is the right-derived `Γ`
evaluated on its image under `T`.

`isZero_compactDerived_coefficientRestrictedSmoothPointProduct_of_injective`
assumes positive-degree right-derived `Γ` vanishes on `T(N)` for every injective
coefficient diagram `N`. It proves the same vanishing for `T(M)` for every
coefficient diagram `M`.

The discrete coefficient category has enough injectives by the objectwise
construction in `PointProductAcyclic`. The previously established exactness of
`T` makes its positive right-derived functors zero. The existing
`isIso_compComparison` therefore compares the right-derived functors of `T ⋙ Γ`
with those of `Γ` on `T(M)`; the assumed vanishing on injective coefficient
diagrams makes this comparison an isomorphism. The functor `T ⋙ Γ` is exact by
`TwistedPointProductExact`, so its positive right-derived functors are zero.
Transport across the comparison gives the conclusion. The exact-functor
vanishing step reuses
`isZero_rightDerived_succ_of_preservesHomology`.

This result leaves compact acyclicity for injective coefficient diagrams as an
explicit premise. It proves neither that ordinary restriction preserves
injectives nor an analytic vanishing theorem. No analytic comparison, parent
acyclicity proposition or unproved Library statement is used. Its provenance is
this categorical argument, rather than an attribution to the analytic literature.
