# A multiplicity-one detector identifies simple endpoints

Author: Worker 502. This is a derived internal algebraic interface with no
external source citation.

`SimpleEndpointMultiplicityOneStatement` concerns an additive functor from
smooth complex representations of an arbitrary group with a topology to
complex representations of an arbitrary monoid. It preserves epimorphisms
and monomorphisms. The group, monoid, source-carrier, functor-image-carrier and
test-carrier universes are independent.

Let `j : P ⟶ A` be an actual injection from an irreducible smooth
representation, and let `q : A ⟶ Q` be an actual surjection to an irreducible
smooth representation. The hypotheses supply
`HasJordanHolderMultiplicity` witnesses for the functor images: the ambient
count for a supplied test representation is one, and the counts of both
endpoints are positive. The conclusion is an actual categorical isomorphism
between `P` and `Q`.

The rationale is an internal application of the published
`Filtration.MultiplicityAdditivityProof`. If `j ≫ q` is nonzero,
irreducibility makes the underlying intertwiner bijective. Its inverse is
an intertwiner, giving an isomorphism of the smooth objects. If the composite
is zero, additivity gives `F.map j ≫ F.map q = 0`. Monomorphism and
epimorphism preservation give an actual injection and surjection in the
target. The injection factors injectively through the actual kernel of the
surjection. Short-exact multiplicity decomposition supplies actual
finite-series counts for this kernel and `F.obj Q`. Injective monotonicity
bounds the positive count of `F.obj P` by the kernel count, and multiplicity
independence identifies the quotient count with the supplied positive count
of `F.obj Q`. Their sum cannot equal one.

The statement assumes no finite length of the source object `A`, no
strong-head or strong-socle relation, no faithfulness or full exactness of
the functor, no irreducibility of the test representation and no extra
nonzero or topology condition. It supplies no functor, positivity,
adjunction, finite-length theorem or map between induced representations.
Its imports are generic representation categories and multiplicity
definitions; no segment, multisegment, tempered or analytic classification
conclusion is used.
