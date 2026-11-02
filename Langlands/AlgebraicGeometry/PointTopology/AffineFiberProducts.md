# Actual affine fibre-product point comparisons

Author: Worker 105.

Source: Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), Proposition 2.1 and its proof, printed pages 2–3.
Registered source `conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

For commutative `R`-algebras `C`, `A`, `B`, `S`, with compatible `C`-algebra
structures on `A` and `B`, `SpecFiberProductPoint R C A B S` is the actual set
of morphisms from `Spec S` to the scheme pullback
`Spec A ×[Spec C] Spec B` whose composite to `Spec R` is the prescribed
structure map. The scalar-tower assumptions express compatibility with `R`.
All rings lie in a common universe. There is no `C`-algebra structure imposed
on `S`: its map to `Spec C` varies with the point.

`specFiberProductTensorEquiv` compares these actual points with
`SpecPoint R (A ⊗[C] B) S` using Mathlib's affine scheme pullback
isomorphism. `specAlgebraMap_tower` and `specFiberProduct_hom_base` verify
the equation over `R`. The inverse comparison uses the inverse scheme
isomorphism, and the categorical inverse identities prove that both
composites are identities.

The topology on `SpecFiberProductPoint` is induced from this tensor-coordinate
affine evaluation topology. `specFiberProductTensorHomeomorph` records the
transport; it does not yet compare that topology to a subspace of a product.

`CompatibleSpecPointPair` consists of pairs of actual `R`-points of the
factor schemes whose maps to `Spec C` agree. Its topology is the subspace
topology of the product of the factor evaluation topologies.
`specFiberProductPointPair` uses the actual scheme pullback projections,
while `specFiberProductPointLift` uses the categorical pullback lift.
Their inverse equations give `specFiberProductPointPairEquiv`.
These are algebraic constructions with no finite generation, topological-ring
or separation assumptions. Transporting the topology requires only a topology
on `S`.

This is a derived host construction implementing the actual affine fibre
product used in Conrad's Proposition 2.1, reusing Mathlib's pullback and
tensor product. The topological fibre-product theorem, axiomatic uniqueness,
and the rest of Proposition 2.1 are separate statement and proof obligations.
