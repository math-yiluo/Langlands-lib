# Pointed morphisms of arbitrary tori

Let `k : Type u` be any field, and let `D` and `H` be group schemes over
`Spec k` satisfying the published predicate `IsTorus`. For a scheme
morphism over the base `p : D.X ⟶ H.X`, suppose
`η[D.X] ≫ p = η[H.X]`. The construction
`IsTorus.homOfPointedMorphism` returns an actual group-scheme homomorphism
`D ⟶ H`, and `IsTorus.homOfPointedMorphism_hom` identifies its underlying
scheme morphism with `p`. No splitness over the ground field, dominance,
perfectness, infinitude, or characteristic hypothesis is assumed.

The proof is an internal deduction from the canonical split-torus
pointed-morphism constructor and faithful field pullback. First,
`IsSplitTorus.isMonHom_of_pointed_morphism` transports the morphism and its
identity equation through two splitting isomorphisms, applies the canonical
constructor, and transports the resulting homomorphism back.
`pointed_morphism_algebraPullback` expresses preservation of the identity
equation by the monoidal field pullback functor.

For a split source and arbitrary torus target, choose a field splitting
the target. The source remains split over this field. The split result
proves that the pulled-back morphism preserves the group laws.
The faithful pullback reflection lemma
`GaloisCocharacterDescent.isMonHom_of_faithfulMap` descends those equations.
This proves `IsSplitTorus.isMonHom_to_torus_of_pointed_morphism`.
Finally, choose a field splitting an arbitrary source; the target remains
a torus under field extension. Apply the preceding result and reflect the
group laws once more. This proves
`IsTorus.isMonHom_of_pointed_morphism`, which the constructor packages
using `Grp.homMk`.

This is an internal prerequisite for the torus step of the host rational
maximal-torus conjugacy proof. It proves no splitness assertion about a
general solvable group or unipotent radical, and does not prove that full
conjugacy statement.
