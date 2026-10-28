# Associated sheaf diagrams on varying finite geometric torsors

Author: Worker 13.

This internal construction assembles the published varying-cover cospans into
actual diagrams of associated small-etale coefficient sheaves. It uses the
proved `etaleAssociatedCoverComparison`, with its full finite geometric torsor
hypotheses, to invert each right cospan leg. No comparison is supplied as an
assumed field.

Let `X : Scheme`, `R` be a commutative ring, `D : I ⥤ GrpCat` and
`Y : EquivariantDiagram D X.Etale`. Assume
`hY : ∀ i, IsFiniteGeometricTorsor X (Y.action i)`.
A coefficient input is `M : EquivariantDiagram D (ModuleCat R)`. The scheme,
ring, coefficient carriers and groups share universe `u`, inherited from the
associated-sheaf and cover-comparison constructions. The index-object and
index-morphism universes `uI` and `vI` are independent.

For `f : i ⟶ j`, write `A_i = Assoc(Y_i,M_i)` and
`B_f = Assoc(Y_i,res(D.map f) M_j)`. The published cospan is

`A_i --β_f--> B_f <--α_f-- A_j`.

`β_f` is coefficient reduction on `Y_i`. `α_f` is the exact published
`etaleCrossCoverMap` for `Y.transition f` and the identity of the restricted
representation. The theorem `etaleAssociatedComparison_app_isIso` applies
`etaleAssociatedCoverComparison` with source torsor `Y_j`, target torsor
`Y_i`, group homomorphism `D.map f` and coefficients `M_j`.
`etaleAssociatedComparisonIso` bundles these components into a natural
isomorphism in the entire coefficient diagram, using the already proved
naturality of `etaleAssociatedComparison`.

`etaleAssociatedTransition` is the natural transformation `β_f ≫ α_f⁻¹`.
`etaleAssociatedTransition_comparison` proves its defining equation
`τ_f ≫ α_f = β_f` on each coefficient input.

`etaleAssociatedInclusion` is the existing invariant inclusion for constant
coefficients, now named on the small-etale associated sheaf. It is a
monomorphism and is natural in equivariant coefficient maps. The comparison
and reduction inclusion lemmas identify both cospan legs on actual sections.
Consequently `etaleAssociatedTransition_inclusion` gives

`τ_f ≫ inc_j ≫ coverPullback(Y.map f) = inc_i ≫ productSheaf(Y_i).map(constantSheaf.map(M.map f))`.

The equality retains the existing product pullback and inverse-deck action
conventions. The cover map points `Y_i → Y_j`, while its section pullback
points from sections over `Y_j` to sections over `Y_i`.

`etaleAssociatedTransition_hom_ext` proves that composing a map into `A_j`
with `inc_j` and that cover pullback detects equality: this composite equals
`α_f` followed by the monomorphism into sections over `Y_i`, and `α_f` is
invertible. The transition identity law follows by applying the displayed
section equation to an identity index arrow. Composition follows by this
equality criterion for `f ≫ g`, the section equation for `g` and `f`,
contravariant composition and coefficient naturality of `coverPullback`, and
the original functor laws of `Y.obj` and `M.obj`. This proof uses actual
section maps and does not assume a separate coherence of chosen inverses.

`etaleAssociatedVaryingSystem` is the resulting functor `I ⥤ Sheaf`, with
object `A_i` and arrow `τ_f`. Thus an inverse index category, for example
`ℕᵒᵖ`, yields an actual inverse sheaf system. No filteredness or preorder
hypothesis on `I` is needed. `etaleAssociatedVaryingSystemFunctor` makes this
construction functorial in `M`; its map on a coefficient-diagram morphism at
`i` is the associated-sheaf functor applied to that morphism's equivariant
component. Naturality across indices is the naturality of `τ_f`. The final
three formula lemmas describe the objects, transition maps and coefficient
morphisms.

The provenance is the categorical composition of
[VaryingCover](VaryingCover.md),
[EtaleCoverComparisonProof](EtaleCoverComparisonProof.md),
[CrossCover](CrossCover.md) and
[EquivariantDiagram](../../CategoryTheory/EquivariantDiagram.md). No new
external-source claim is made. The torsor hypotheses are genuine input data;
this unit does not construct Harris's particular torsors or identify its
associated sheaf system with geometric cohomology. Coefficient-power
specialization, scalar extension, limit comparisons and cohomology remain
separate constructions or theorems.
