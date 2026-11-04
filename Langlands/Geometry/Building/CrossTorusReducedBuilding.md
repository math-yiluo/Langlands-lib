# Actual reduced quotient transport between torus embeddings

Author: Worker 118.

Over an arbitrary field, supply the actual isomorphisms `e : S ≅ S'` and
`f : G ≅ H`, their commuting square with the inclusions `i`, `j`,
monomorphisms on both underlying inclusions, affine ambient structural
morphisms, and `D : KPApartmentData i ω`. The scalar function `ω` stays
unchanged. `D.reducedBuildingTransportEquiv e f h` identifies the existing
quotient types `D.ReducedBuilding` and
`(D.transport e f h).ReducedBuilding`.

For any subset `Ω` of the actual source apartment, root-fixer membership is
preserved and reflected at the transported character and image subset.
This follows by transporting the actual root group and every pointwise
level-zero filtration. The explicit root-group intersection in `rootFixer`
is retained, so this also covers the empty subset. Surjectivity of the
actual ambient point map gives equality of the entire subgroup images.
Mapping subgroup suprema and using the actual relative-root bijection then
identifies the entire generated sharp fixer with its target image.
No equality between a sharp fixer and a full stabilizer is assumed.

The actual normalizer equivalence and apartment action identity identify
the witnesses in the original quotient relation. The sharp-fixer identity
at a singleton and the homomorphism laws preserve its condition
`g⁻¹*g'*n ∈ G(k)^♯_x`. Thus that exact relation is preserved and reflected.
Mathlib's `Quotient.congr` applied to the product of the actual ambient-point
and apartment equivalences constructs the quotient equivalence.

On a representative it sends `[(g,x)]` to
`[(f(g), apartmentTransportEquiv(x))]`. It carries the original canonical
apartment chart to the target chart and intertwines the original
rational-point actions through `rationalPoints.map f.hom`.
The chart identity and the two equivalences preserve and reflect
injectivity of the apartment chart.

The equivariance identity preserves and reflects membership in the full
point stabilizer. Surjectivity of the actual point map gives its exact
subgroup image as the full target stabilizer. These statements concern
full stabilizers; they assert no identification with sharp fixers,
parahorics or intersections with zero/one subgroups.

The provenance is internal. The input quotient, its exact relation,
root/sharp fixers, action and charts are the existing constructions in
`KPBuilding` and `ApartmentQuotient`. This unit transports those constructions;
it does not assume or prove that either quotient satisfies the abstract
building axioms. It constructs no compatible class for a separately chosen
target group, no field-isomorphism comparison, and no building data for
arbitrary reductive groups. Canonical class compatibility, apartment
intersections, full A2, the corrected full validity predicate and general
building existence remain separate obligations.
