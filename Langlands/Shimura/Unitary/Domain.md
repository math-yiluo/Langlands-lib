# Corrected archimedean homomorphisms and actual conjugacy domains

This module develops the standard real-group model for the Harris domain.
It imports the accompanying `CMData` and `Signature` constructions and the
published `Langlands.Shimura.Unitary.Similitude` prerequisite. It does not
construct the complex manifold or the global canonical scheme.

`ComplexHom` contains an actual real algebra map from the complex numbers
with a proof that the specified algebra involution intertwines complex
conjugation. `toSimilitudes` constructs its map on complex units, recording
the real norm-square multiplier and proving that this multiplier is positive. The similitude equation follows from the
algebra-homomorphism laws and `z * conjugate(z) = normSq(z)`.

`correctedComplexHom n r` is a diagonal algebra map: complex conjugation on
the first `r` coordinates and identity on the others. Its compatibility with
the actual diagonal-Hermitian adjoint is proved. The product construction
places signature `(n-1,1)` at the distinguished index and `(n,0)` at the other
indices; its multiplier is the same real norm square at every factor. For
the intended specialization, indices are real embeddings of the totally real
field and `n > 1`. The general definitions also make sense for other indices
and dimensions, without asserting a Shimura datum in those cases.

The direction of conjugation is deliberate. Harris 1997, Section 2, printed
page 89 (PDF page 15), displays the earlier homomorphism with `z` on the
positive block and its conjugate on the negative block. Harris 1998,
Erratum, printed pages 180–182 (PDF pages 4–6), explicitly replaces it by
its complex conjugate to agree with Rapoport–Zink and the chosen prime.
Harris 1999, Section 4, printed pages 308–309 (PDF pages 10–11), uses that
corrected datum. The present coordinate map therefore uses the conjugate
on the positive block. It is a map on real points; no claim of an algebraic
Deligne-torus morphism or reflex-field computation is made here.

`ConjugationHom` is a wrapper around actual group homomorphisms, with
conjugation by the target group. The group-action certificates are proved.
The stabilizer equals the centralizer of the homomorphism's actual range.
`Domain` is the quotient by that stabilizer, with its inherited group action
and quotient topology when the target group has a topology. `realization`
maps a coset to its actual conjugated homomorphism; its injectivity,
equivariance and equivalence with the full orbit reuse Mathlib's
orbit-stabilizer construction. No arbitrary space is supplied as an output.

`StandardArchimedeanDomain` applies this construction to the concrete corrected
product homomorphism. `HarrisArchimedeanDomain` specializes its indices to the
actual real embeddings of a totally real number field and takes the source
dimension hypothesis `1 < n` explicitly. Identifying it with the domain of a prescribed global
CM algebra, proving the complex ball description, and constructing canonical
models and coefficient systems remain further work.

Source correspondence: Harris 1997 p.89, Harris 1998 pp.180–182, Harris 1999
pp.308–309, and Kottwitz 1992 p.654 (conjugacy class and centralizer quotient).
These original passages have been read; Kottwitz p.654 was visually checked.
All new implementations and intrinsic proofs are by Worker 57.

## Exact source and environment record

The retained originals are:

- Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
  J. Math. Kyoto Univ. 39-2 (1999), pp.299-318;
  source `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`,
  SHA-256 `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.
- Harris, *Supercuspidal representations in the cohomology of Drinfeld upper
  half spaces; elaboration of Carayol's program*, Invent. Math. 129 (1997),
  pp.75-119; source `harris-1997-drinfeld-cohomology`,
  SHA-256 `aea284b917442459028b710dbfd9ae537631490504f3bc6d54a1e76ee697e0d9`.
- Harris, *The local Langlands conjecture for GL(n) over a p-adic field, n < p*,
  Invent. Math. 134 (1998), pp.177-210; source `harris-1998-local-langlands`,
  SHA-256 `7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`.
- Kottwitz, *On the lambda-adic representations associated to some simple
  Shimura varieties*, Invent. Math. 108 (1992), pp.653-665;
  source `kottwitz-1992-lambda-adic-simple-shimura`,
  SHA-256 `749af5541a59187e6f9d1089dec9a0e591a2059173da739c7384ff3a7d0dd799`.

The exact relevant passages and declaration correspondence are stated above.
The formal environment is Lean 4.34.0 and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
