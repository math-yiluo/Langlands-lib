# Compatible quotient kernels on products of local full domains

This internal construction starts with two original full local domains `U,V`, full domains `S,T` over their unchanged algebras, and an already proved `IntersectionData` for `U.extend S` and `V.extend T`. It does not assume an intersection for `U,V`.

`ProductIntersection.quotientMap` composes the constructed product-to-coproduct comparison with the actual coproduct presentation of the supplied local intersection. Its composites with the two original product legs are exactly the stored intersection restrictions. If the genuine completed-tensor map of those restrictions is admissible, this quotient map is admissible by the bounded comparison maps and controlled-lift factor criterion.

For two such product pieces and any full domain `E` including into both, `exists_factor_to_baseChange` considers the actual affinoid base change of the first quotient to `E`. The pushout square and both product structural equations identify the two original-container maps with the maps through the first intersection. The proved common-witness factorization through the second intersection then supplies both complete bounded-map identities. The product coproduct universal property identifies the resulting quotient composite.

The actual pushout lift gives a map between the two quotient base changes over `E`. Constructing it in both directions proves equality of their exact ring kernels by evaluating the two structural identities at a kernel element. No inverse identities are required. For admissible local quotients, the exact pushout kernel formula converts this to equality of the closed extensions of their original kernels. These are the actual closed ideal extensions, retaining the original norm topologies and nilpotents.

The result is a prerequisite for finite-cover ideal compatibility. It supplies neither ideal effectiveness nor a global intersection. Coefficient, ambient-space, and original-index universes remain independent; trivial valuations and empty domains are allowed.
