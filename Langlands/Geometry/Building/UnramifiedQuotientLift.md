# Scalar-extension lift into a supplied maximal-unramified building quotient

This internal construction specializes the published universal property in
`ApartmentQuotientComparison` to the actual maximal unramified scalar
extension. It reuses that module's lift and injectivity proof, rather than
introducing a second quotient relation or representative-independence proof.

Let `F` be any nonarchimedean local field in universe `u`, let `G/F` be
affine, and write `φ = GaloisPointComparison.rationalExtend F
(UnramifiedClosure F) G`. The source `B : ValuationBuildingData G` and
target `C : MaximalUnramified.BuildingData F (baseChanged F
(UnramifiedClosure F) G)` are supplied. The latter uses the constructed
integer-valued valuation on the actual inertia fixed field, not a local-field
structure on that generally infinite extension.

For a supplied function `f : B.Apartment → C.Apartment`, assume:

- At every source point and every element `n` of the source normalizer,
  `C.apartmentMap (f (n • x)) = φ n • C.apartmentMap (f x)`.
- At every source point `x`, the source `B.sharpFixer {x}` lies in the
  preimage under `φ` of the target fixer of `C.apartmentMap (f x)`.

`quotientLift` then constructs a function from the existing source reduced
building to the existing target reduced building. Internally, it restricts
the target action along `φ` using Mathlib's `MulAction.compHom` and applies
`ApartmentQuotient.lift` to `C.apartmentMap ∘ f`. The restricted action is
local to the implementation. The public formulas use the original target
action explicitly.

`quotientLift_mk` gives the value on any representative:
`[(g,x)] ↦ φ(g) • C.apartmentMap (f x)`. The apartment formula and
`quotientLift_smul` give its apartment values and scalar-extension
equivariance. `quotientLift_unique` proves uniqueness among functions with
these same apartment values and equivariance, since every source quotient
point is a translate of an apartment point.

`sharpFixer_le_comap_of_rootFiltration` reduces the every-point fixer
comparison to the corresponding inclusions for all actual source depth-zero
root subgroups. It unfolds the sharp fixer as the supremum of the root
fixers and uses the published singleton identity identifying each root fixer
with its depth-zero filtration. It does not obtain this comparison from a
global embedding whose construction would already require it.

Given a source polysimplicial realization satisfying
`B.SatisfiesBuildingAxiom`, `quotientLift_injective` proves global
injectivity when `f` and `C.apartmentMap` are injective. It derives common
translated source apartments from the published
`SatisfiesBuildingAxiom.hasCommonApartments`, then applies the published
`ApartmentQuotient.lift_injective` to the composite apartment map.
`quotientEmbedding` packages this result as an embedding, with the same
underlying function.

The proof route is an internal composition of existing Library quotient and
building-axiom results with Mathlib's action restriction. No new assertion
from the original literature is made. Worker 118 contributed the
source-inspected action-restriction route; Worker 1681 implemented the
specialization and proofs.

Both building bundles, the compatible apartment map, normalizer
compatibility, the every-point root/fixer comparisons, apartment
injectivity, and the source building witness remain inputs. The apartment
map is an arbitrary function here; no affine, root or facet preservation is
asserted. This unit constructs no unconditional building or scalar-extension
embedding, no metric, and no identification of an original supplied integral
model. In particular, it does not prove or replace
`IntegralModel.BuildingComparisonStatement`.
