# Finite length of the actual cut complex

Author: Worker 164.

This internal adapter proves finite group-algebra length of each degree of the
actual smooth signed complex on finite-length input. It constructs
`ActualCutComplex.finiteDegree` as a genuine `SmoothRep.FiniteLengthObject`.
It asserts neither finite vector-space dimension nor exactness or effectivity.

For a family of representations `ρ j`, `FiniteProduct.evaluation ρ j` is actual
coordinate evaluation from the pointwise product action to `ρ j`. Its linear
part is `LinearMap.proj j`, and its equivariance equation is the defining formula
for that action. The published correspondence
`Representation.IntertwiningMap.equivLinearMapAsModule` turns it into a map
between the actual group-algebra modules. The product of these maps is
`FiniteProduct.groupModuleMap`; equality of every coordinate implies equality
of the original vectors, proving injectivity.

For a finite index type, finite length of each coordinate module implies that
each is Noetherian and Artinian. The standard finite-product instances then make
the product of the coordinate group-algebra modules both Noetherian and
Artinian, hence of finite length. Pulling back along the injective comparison
proves `FiniteProduct.finiteLength` for the actual pointwise representation.
This argument uses no semisimplicity or splitting hypothesis.

`ActualCutComplex.term_hasFiniteLength` applies the published theorem
`Langlands.Aubert.normalizedInductionJacquet_hasFiniteLength` to one actual
normalized induction--Jacquet term. The representation used by `Transition.term`
is definitionally the action on the object obtained from those two actual
normalized functors, so the existing finite-length proof applies to its actual
group-algebra module.

For `degree_hasFiniteLength`, the index type consists of cut sets of cardinality
`k`. The proof performs the same coordinate-map argument with the actual
`degreeRepresentation` as its source and the actual normalized terms as its
targets. The coordinate intertwiners give an injective group-algebra-linear map
into their finite product. Each target has finite length by
`term_hasFiniteLength`, so finite-product Noetherianity and Artinianity and
injective pullback establish finite length of the source. This is exactly the
finite-length predicate of the already constructed `degreeObject`.

`finiteDegree F T A hA k` pairs that actual smooth object with this proof. Its
underlying carrier, action and differential indexing are unchanged. The
parameters retain arbitrary primes, the supplied field/topology, independent
field and carrier universes and saturated carriers `Type (max uF uV)`. The empty
index set causes no exception: its product is a zero module. Rank zero is
included. The sole additional input to the degree finite-length theorem is the
finite length of `A`; the final effectivity application obtains this from its
existing irreducibility hypothesis.

The provenance is internal. The module composes the established actual-functor
finite-length theorem with the standard algebraic characterization of module
finite length as Noetherian plus Artinian and its finite-product/injective-map
consequences. Every comparison map used here is explicit. No composition-class
Euler identity, actual support filtration, graded-map comparison, homology
concentration or signed-effectivity claim is made.
