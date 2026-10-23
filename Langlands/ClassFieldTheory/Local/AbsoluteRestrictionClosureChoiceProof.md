# Independence of absolute degree-two restriction from the closure embedding

Author: Worker 160.

`Langlands.ClassFieldTheory.Local.absoluteRestrictionClosureIndependence`
proves exactly the published proposition
`AbsoluteRestrictionClosureIndependence.{u}`. For arbitrary fields K and L
in the same arbitrary universe, a fixed K-algebra structure on L, and any two
compatible algebra structures between their specified full algebraic closures,
the two actual `absoluteRestriction K L 2` morphisms are equal.

Each closure algebra has its own scalar-tower certificate. There is no
finite-extension, Galois, perfectness, characteristic, local-field, or
invariant-existence assumption. The equality is in the existing
`TopModuleCat` over `IntegerScalars.{u}`, between the existing continuous
degree-two cohomology objects with discrete additive closure-unit coefficients.

## Implemented proof

The proof first establishes three private bridge lemmas.

`explicitClosureMap_eq_absoluteRestriction` identifies the map
`absoluteRestrictionAlongClosure` for the embedding supplied by an installed
compatible scalar tower with that tower's actual `absoluteRestriction`.
Unfolding the explicit wrapper and `IsScalarTower.toAlgHom` makes the equality
definitional.

`sourceClosureRestriction_eq_conjugation` proves that restriction along a
source-closure automorphism c sends g to c⁻¹ g c. Applying the injective map c
reduces the claim to `restrictionAlongClosure_commutes` and cancellation of c
with its inverse.

`sourceClosureMap_eq_innerConjugation` identifies the resulting actual
cohomology map, in every degree n, with
`innerConjugationMap (absoluteUnits K) c⁻¹ n`. The group maps agree by the
previous lemma. The coefficient maps both act on closure units by c:
the generic inner-conjugation map uses the inverse action of its argument,
which here is c⁻¹. The published `map_congr_of_apply` reduces equality of the
cohomology maps to these two checks.

For the final theorem, the two compatible algebra structures define explicit
K-algebra embeddings ι and κ of the source closure into the target closure.
The first bridge lemma identifies their maps with the two sides of the
target proposition. Put c = `closureChange ι κ`, so ι(c x) = κ(x). The
published comparison theorem `absoluteRestrictionAlongClosure_change` gives

    Rκ = Rc ≫ Rι,

where R denotes the corresponding explicit-embedding cohomology map and the
category notation means first Rc, then Rι. The third bridge lemma identifies
Rc with inner conjugation by c⁻¹. The published theorem
`Langlands.Continuous.innerConjugationH2Triviality` makes that factor the
identity in degree two. `Category.id_comp` finishes the equality.

The generic H² theorem requires compactness and the Hausdorff property of
the actual absolute Galois group. The proof supplies compactness through
`Langlands.GaloisRepresentation.absoluteGaloisGroupCompactness` and the
Hausdorff property through Mathlib's `krullTopology_t2`. In particular,
compactness over imperfect fields is supplied by the arbitrary-field theorem;
it is not inferred by treating the full closure as a separable extension.

## Dependencies and provenance

This is an internal derived proof of the unchanged Library statement. It
imports the explicit closure comparison, the arbitrary-field compactness
proof, and the continuous H² inner-conjugation proof by their Lean module
names. Worker 160 wrote the three bridge lemmas and the final assembly here.
The imported compactness proof is due to Worker 29; the imported H² proof
is due to Worker 134 with Worker 160's formula and convention contributions,
using the separately published continuous prism construction. Those
prerequisites are reused as published results.

The statement's paired Markdown explains its relationship to Serre,
*Local Fields* (1979), X.4, Proposition 5, and VII.5, Proposition 3. This
implementation follows the closure-comparison and inner-conjugation route
using the actual Library maps. It proves degree-two independence for fixed
closure models and arbitrary fields. It supplies neither a local invariant
isomorphism nor its restriction-by-degree law; those are separate arithmetic
obligations in `AbsoluteInvariantExistence`.
