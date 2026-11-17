# Algebra descent from finite affine permutation charts

This internal derived module constructs a multiplicative faithfully flat descent
coaction from actual split charts and their locally permuting transitions. The
base scheme `S` and finitely many chart schemes `U a` are affine. The chart map
is `f a : U a ⟶ S`; the actual group scheme `D` has a split chart over each `f a`
with finite coordinate type `I a`, and every pair satisfies `LocallyPermutes`.
Coordinate types may have different ranks or be empty. Schemes and index types
lie in an arbitrary common universe.

The maps and coaction laws require neither flatness nor joint surjectivity of
the chart maps. The final effective-descent theorem additionally assumes each
`f a` is flat and `Sigma.desc f` is surjective. It imposes no affine hypothesis
on `D` itself.

`coefficientDatumAlong_pullback` proves that pulling back coefficient data along
a composite equals iterated pullback. `coefficientEquivAlong_naturality` transfers
this to the actual glued coefficient equivalences on global sections.

Let `R = Γ(S, ⊤)`, `B = Π a, Γ(U a, ⊤)` and
`C = Π a, I a → Γ(U a, ⊤)`. The ring maps are the canonical `coverRingMap` from
`R` to `B` and `FiniteProductCoefficients.scalarMap` from `B` to `C`.
`overlapEquiv` is the coefficient equivalence on an actual overlap.
`sourceSections` pulls a source component of `C` to that overlap, and
`overlapMap` applies the transition to all pairs. `tensorMap` transports this
ring map through the inverse overlap-tensor equivalence into `B ⊗[R] C`.
`tensorMap_formula` specifies its coordinates on every actual overlap.
`transitionAlgebraMap` proves it is a `B`-algebra map: scalar constants pass
through the overlap equivalence, giving exactly the left tensor factor's action.

`multiplication` is the tensor counit `b ⊗ c ↦ scalarMap b * c`.
`multiplication_diagonal` identifies it with evaluation of overlap tensor
coordinates on each diagonal. Naturality and the repeated-chart identity give
`diagonal_overlapEquiv`, hence `multiplication_tensorMap`, the counit law.

The module also constructs actual triple-overlap tensor coordinates.
`FiniteProductCoefficients.tensorDoubleCoefficients` distributes the twice
extended coefficient algebra into triple tensor cells.
`AffineCoverCoefficientTensors.overlapTensorAlgEquiv` adds the common-base algebra
structure to the overlap tensor equivalence. `tripleCellEquiv` and
`tripleTensorEquiv` then identify the twice extended algebra with coefficient
families on actual right-associated triple overlaps. Their explicit nested pure
tensor formula fixes the three projection orientations.

`duplicate` inserts a middle unit, and `extendTransition` applies the transition
to the inner tensor factor. Both are `B`-algebra maps. `duplicate_formula` is
pullback of the first-third overlap coordinate family. `extendTransition_formula`
is the second-third coefficient equivalence applied to the first-second family.
These formulas are proved by tensor induction, using coefficient naturality and
linearity of the actual algebra equivalences. `tensorMap_coassoc` then applies
`tripleTensorEquiv`'s injectivity and the previously proved coefficient cocycle.

`coaction` packages `transitionAlgebraMap` with both laws in the actual
`FaithfullyFlatAlgebraDescent.Coaction` interface. The counit, comonad duplication,
and extension of the transition linear map are identified with `multiplication`,
`duplicate`, and `extendTransition`, respectively, by pure-tensor calculations.
No coaction or effectivity hypothesis is taken as input.

`exists_coefficientDescent` applies this coaction to the faithfully flat product
map. It constructs the actual invariant subalgebra `E` of `C`, proves `E` finite,
projective, and étale over `R`, and gives a `B`-algebra equivalence
`B ⊗[R] E ≃ₐ[B] C`. The earlier product-coefficient results provide finiteness and
étaleness over `B`; the general faithfully flat algebra-descent results transfer
them and prove projectivity. Zero rings, empty bases, and zero component ranks
are allowed.

This is the coefficient-algebra descent step. Refining an arbitrary étale
permutation atlas to these finite affine charts and constructing the actual
isomorphism from the supplied group scheme to the Weil torus remain separate
obligations. The unchanged relative-Borel Weil-presentation target is not claimed
here.
