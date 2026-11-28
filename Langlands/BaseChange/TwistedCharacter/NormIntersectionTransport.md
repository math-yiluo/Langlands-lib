# Compact intertwining under open subgroup image charts

Let \(i:G\to H\) be an open embedding of groups into a topological group.
For open subgroups \(K,L\) of \(G\), pull representations on \(i(K)\) and
\(i(L)\) back via the open subgroup image equivalences. Suppose the
homomorphism \(\beta:G\to G\) satisfies \(i(\beta g)=y^{-1}i(g)y\).
`openImageConjugateIntertwining` takes a nonzero intertwiner on
\(i(K)\cap y i(L)y^{-1}\) to a nonzero intertwiner on
\(K\cap\beta^{-1}(L)\). The second representation acts there by
\(\beta\), followed by its open image chart.

The restriction homomorphism on the intersection sends a unit to its
image in \(i(K)\). The second action agrees because \(\beta\) implements
inverse ambient conjugation. These two identities transport the
intertwining equations for the same linear map.

`openImageSliceIntertwining` carries out the analogous restriction in
slice coordinates. For a continuous homomorphism \(f:M\to G\), the
slice intersection \(f^{-1}(K)\) maps into the ambient slice intersection
for \(i\circ f\). The pullback has the same nonzero linear map, now with
the first compact type acting via \(f\) and the open subgroup image
chart. These are the subgroup identifications used for the compact
interactions in Clozel's descent. [Clozel 1987, §3.4 and §3.6, printed pp. 154, 158](https://doi.org/10.4153/CJM-1987-008-3)
