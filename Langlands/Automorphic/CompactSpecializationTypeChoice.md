# Choosing a nonzero compact type in a specialization quotient

`exists_nonzero_jointCompactType` chooses a simple compact submodule in the nonzero semisimple quotient. Its orbit span is finite dimensional, so a basis gives the compact type on a standard coordinate space. A nonzero vector in the simple submodule lies in this isotypic part. Intersecting its open finite stabilizer with the supplied compact open level gives a compact open subgroup fixing the vector.

`jointCompactQuotientLift` applies the joint projection on the numerator. Naturality for the inclusion into the inducing representation gives the projected inducing vector. Naturality for the quotient map preserves the prescribed quotient vector because the two compact projections fix it.

These derived compact-type choices implement the finite level and infinite compact projection used in the constituent argument of Langlands, proof of Proposition 2, printed p. 206 (Corvallis Part I PDF p. 201).
