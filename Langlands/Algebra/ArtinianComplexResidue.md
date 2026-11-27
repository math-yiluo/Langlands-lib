# Exactness and freeness over a local Artinian ring

A basis of the residue reduction of a flat module lifts to a basis.
The resulting map from a free module is bijective because an injection
into a flat target can be detected after tensoring with the residue
field and the maximal ideal is nilpotent. The same nilpotence detects
surjectivity. If a map into a flat module is injective on reduction, a
linear retraction over the residue field lifts from the free target.
Its composite with the original map is invertible because its reduction
is the identity. Composing with the inverse gives a retraction.

For a pair of differentials, residue exactness makes the map from the
first cokernel into the next term injective on reduction by right
exactness of tensor product. The map is therefore a split injection,
and the cokernel is flat. Splitting the two short exact sequences of
the first differential gives a flat kernel. In the four-term case,
residue injectivity of the first differential also splits its map into
that kernel. The cohomology quotient is then a direct summand of a flat
module and is free by the basis argument. The constructions use
`residueTensorNilpotentInjectivity` and `surjective_of_nilpotent_baseChange`.
