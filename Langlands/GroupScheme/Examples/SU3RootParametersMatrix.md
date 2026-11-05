# The SU3 root coordinate matrix embedding

This file constructs the upper matrix of Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), §2.7, printed pp.108–110 (PDF pp.139–141), especially the upper matrix preceding (2.7.2). Source `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`. The book matrix on PDF p.141 was visually read; its (0,1), (0,2), (1,2) entries are `u`, `v`, `bar(u)` in zero-based indices. The generic ring formulation and intrinsic proofs are derived from these formulas.

`Parameters.embedding` is a group homomorphism to Mathlib's actual `GL (Fin 3) A`. Its underlying matrix is `[[1,u,v],[0,1,bar(u)],[0,0,1]]`; its unit inverse is constructed from the already proved coordinate inverse. Matrix multiplication proves the homomorphism law. Reading entries (0,1) and (0,2) proves injectivity. The three-by-three determinant formula proves determinant one.

`gram A` is `[[0,0,1],[0,-1,0],[1,0,0]]`. `conjugateTranspose c` applies the specified automorphism entrywise and transposes. `conjugateTranspose_eq` compares this definition directly with Mathlib's `Matrix.conjTranspose` using `c.bar` as star. `PreservesForm c M` means `bar(M)^t * J * M = J`. Expansion reduces preservation for the coordinate matrix to `v+bar(v)=u*bar(u)`.

`IsUpperUnipotent` requires diagonal entries one and entries strictly below the diagonal zero. `mem_range_embedding` characterizes the image among actual invertible matrices by this predicate and the Hermitian equation. For the converse, write an upper unipotent matrix with entries `u,v,w`; the (1,2) Hermitian equation gives `w=bar(u)` and the (2,2) equation gives the coordinate trace-norm equation. `embedding_map` proves naturality for every involution-compatible ring homomorphism via Mathlib's `GeneralLinearGroup.map`.

Every argument works for arbitrary commutative rings, including characteristic two; source and target ring universes are independent. These statements concern the constructed coordinate group. They do not identify it with a root subgroup of an arbitrary reductive group or assert representability.
