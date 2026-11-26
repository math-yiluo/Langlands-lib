# Actual Whittaker identity evaluations on two place maps

`proportional_cuspWhittaker_one_of_placeEmbeddings` compares two equivariant linear maps of the same irreducible admissible place module into an actual cuspidal realization with unitary central character. Equivariance is for the place compact and complexified Lie actions. The first map is injective and has nonzero identity evaluation on a reference vector. Each map has a finite compact open level, and the second map may have zero identity evaluation throughout.

The determinant-band form and compact Sobolev estimate give a mixed smooth Whittaker functional that evaluates the original cusp Whittaker integral at identity. The compact and finite covariance of the adelic completion carries the two algebraic maps to that completion. The standard adelic additive character has a unitary local component at the selected place. The real or complex comparison for the paired embeddings then applies `unitaryWhittakerMultiplicityOne` to the two continuous pullbacks. Evaluation on the algebraic module gives the asserted single scalar.

The local uniqueness input is Shalika, *The Multiplicity One Theorem for GL(n)*, Annals of Mathematics 100 (1974), Theorem 3.1, pp. 183–185. The registered source is `shalika-1974-multiplicity-one` with SHA-256 `788c5d124024c768aa47c4e8b179475fbcf5b0882a518ae60b19cdc88089f087`.
