# A common complete field for a family of ultrametric extensions

The entry `Langlands.Analytic.ValuedField.CommonFieldFamily K E` is a chosen
common complete ultrametric normed extension for a family of complete
ultrametric normed extensions of a complete ultrametric normed field `K`.
The coefficient field `K`, index type `I`, each `E i`, and the resulting field
all belong to the same arbitrary universe `Type u`. Every `E i` carries a
`NormedAlgebra K (E i)` structure. No countability, nonemptiness of `I`,
nontriviality of the norm, characteristic, or algebraicity assumption is made.

The construction supplies coherent `NormedField`, `IsUltrametricDist`,
`CompleteSpace`, and `NormedAlgebra K` instances on the chosen field.
`CommonFieldFamily.embedding K E i` is a `BoundedAlgHom K (E i)` into it;
`isometry_embedding` proves that map is isometric, and `norm_embedding` gives
its exact norm identity. The bounded algebra homomorphism includes compatibility
with the given coefficient maps from `K`. This module does not assert that the
common field is algebraically closed.

This is a derived construction for the common analytic point field problem.
Its field-theoretic inputs are the published `completeFieldAmalgamation` and
`seminormRealization` theorems. Its compactness input is Mathlib's product
compactness and directed compact intersection theorem. It does not introduce
an additional field extension hypothesis or rely on an unpublished mathematical
statement. The proof route below is internal to this construction, rather than
an asserted transcription of a particular original source.

For a finite subset `s` of `I`, `FiniteModel` records a common complete
ultrametric normed `K`-field and isometric bounded algebra maps from every `E i`
with `i ∈ s`. Finite induction constructs a model. The empty model is `K`.
The insertion step amalgamates the preceding common field and the new member
over `K`, using the structural coefficient embeddings as the two isometries.
Old embeddings are composed with the first amalgam inclusion and the new
embedding is the second inclusion. The finite models are chosen independently;
no compatibility between different finite subsets is asserted or needed.

Let `R = MvPolynomial (Sigma E) K`, with a generator for each element of each
family member. For each finite subset `s`, `finiteEvaluation` evaluates
coefficients by the structural map into its finite model. A generator
corresponding to `(i,x)` evaluates to the chosen image of `x` if `i ∈ s`,
and to zero otherwise. `finiteSeminorm s p` is the norm of this evaluation.
It is normalized, nonnegative, multiplicative, invariant under negation, and
ultrametric. For all `s`, the norm of the generator `(i,x)` is at most `‖x‖`.
Polynomial induction on constants, sums, and multiplication by a variable then
gives a nonnegative real upper bound `B p` for `finiteSeminorm s p`,
independently of `s`.

The internal lemma `exists_cofinal_limit` considers any such family of real
functions. The functions lie in the compact product of the intervals
`[0,B p]`. For a finite subset `s`, take the closure of the range over all
finite `t` containing `s`. These tail closures are nonempty, closed, and compact.
They form a decreasing directed family, since the tail at `s ∪ t` is contained
in both original tails. The compact intersection theorem supplies a function
belonging to every tail closure. Consequently it belongs to any closed set
containing all functions on one tail.

The conditions for a nonnegative normalized multiplicative ultrametric
seminorm are closed in the product topology: each is an equality or inequality
between continuous coordinate evaluations, products, or maxima. The function
given by compactness satisfies them, and therefore defines a `MulRingSeminorm`
`q`. In addition, whenever the value of one polynomial is constant on a tail,
`q` has exactly that value at the polynomial. This follows by applying the
closed-set property to a single coordinate equality.

`seminormRealization` realizes `q` by a ring homomorphism `r : R →+* L` into a
complete ultrametric normed field `L : Type u`, with `‖r p‖ = q p`.
Constants have their original norm on every finite model. The generator
`(i,x)` has norm `‖x‖` on the tail containing `i`. Hence the same norm identities
hold in `L`.

For every fixed `i`, all relations for zero, one, addition, multiplication,
and coefficient compatibility of its generators vanish in every finite model
containing `i`. Their seminorm is therefore zero in the limit, and their image
under `r` is zero. Thus `x ↦ r(X(i,x))` is a ring homomorphism from `E i`.
The image of the coefficient ring defines the `K`-algebra structure on `L`.
The norm identity for constants supplies its normed algebra structure, and
the coefficient relation makes each family map a `K`-algebra homomorphism.
Its generator norm identity gives bound one and isometry.

`exists_commonFieldFamily` proves existence with all structures and maps
chosen together. `CommonFieldFamily` and its instances and embeddings select
successive witnesses from that one existence theorem, so they use the same
norm, algebra structure, and embeddings throughout. Every carrier used for a
polynomial ring, finite model, realization, or selected field remains in
`Type u`.
