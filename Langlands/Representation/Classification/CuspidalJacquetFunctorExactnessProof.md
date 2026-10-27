# Additivity and preservation of mono/epi for actual Jacquet functors

This proof implements the six properties in
`CuspidalJacquetFunctorExactnessStatement`. It preserves all field, topology,
rank, block-shape and carrier-universe parameters of that statement.

Each additivity instance follows by evaluating the descended maps on quotient
representatives. The quotient projection is linear, so its value on a sum
is the sum of its values.

For monomorphisms, the source smooth category identifies monomorphisms with
injective intertwiners. The existing smooth coinvariant injection theorem
applies to the radical restriction of the target representation. In the upper
case, the already proved finite-containment theorem for the actual intrinsic
block radical and the existing smooth-restriction lemma supply its hypotheses.
The normalizing twist leaves the underlying quotient linear map unchanged.
Mathlib's injective/monomorphism criterion then supplies the target instance.

For the opposite case, the proof first constructs a continuous group
equivalence from the actual opposite ambient radical to the intrinsic upper
radical. It composes inverse transpose, which exchanges the actual upper
and opposite ambient radicals, with the inverse of the existing
`unipotentRadicalAmbientEquiv`. A finite subset is sent through this
equivalence; the upper finite-containment theorem places its image in a
compact open subgroup; the preimage subgroup gives the opposite
finite-containment property. Smooth restriction along the actual subgroup
inclusion then permits the same coinvariant injection theorem.

For epimorphisms, the source criterion gives a surjective intertwiner.
The generic algebraic surjectivity theorem for coinvariant maps applies
without any additional topological assumption. The target criterion converts
this to an epimorphism. In both cases the underlying map is precisely the
actual quotient map in the functor definition.

The exact final theorem assembles the six proved instances. This is an
internal categorical consequence of existing exactness and inverse-transpose
results. It supplies no Jacquet finite length, multiplicity value or
positivity, adjunction, actual nonzero induction map, or segment constituent.
The proof imports the exactness statement, the existing actual upper
normalized Jacquet exactness proof, and inverse-transpose results. Its
70-module project import closure contains only five Classification modules:
this proof, its statement, `CuspidalJacquetFunctors`,
`CuspidalJacquetMultiplicityStatement`, and `Supercuspidal`. The multiplicity
statement is used only for its actual quotient object definitions. No
segment analytic classification, multisegment exhaustion, ordered special-head
existence, quotient coverage, tempered block uniqueness, square-integrable
classification or exhaustion, or regular exhaustion conclusion occurs in
the proof or its transitive proof dependencies.
