# Embedding coordinates for tensor-valued affine points

Let `F`, `k`, and `Ω` be commutative rings in an arbitrary common universe, with
specified `F`-algebra structures on `k` and `Ω`. Assume the family of `F`-algebra
maps `k → Ω` is finite and the canonical evaluation homomorphism
`Ω ⊗[F] k → ((k →ₐ[F] Ω) → Ω)` is bijective. These are explicit algebraic
splitting hypotheses. For an `Ω`-algebra `R` with the compatible `F`-algebra
structure, `tensorEmbeddingEquiv` is the ring equivalence
`k ⊗[F] R ≃+* ((k →ₐ[F] Ω) → R)` obtained by extending that evaluation
decomposition. Its `τ` coordinate sends `b ⊗ r` to the image of `τ(b)` times `r`.

For any commutative `k`-algebra `D`, define `EmbeddingPointFamily` to be families
of ring homomorphisms `fτ : D →+* R` satisfying
`fτ(algebraMap k D b) = algebraMap Ω R (τ b)` for every `b : k`.
This records the conjugate scalar actions explicitly, without identifying
the different `k`-algebra structures on the same coefficient ring.
`tensorPointEmbeddingEquiv` identifies the actual algebra maps
`D →ₐ[k] k ⊗[F] R` with exactly these families. The forward map composes with
coordinate evaluation. The inverse assembles the family as a homomorphism to
the function ring and composes with the inverse tensor decomposition.
The scalar equations prove that this inverse is a `k`-algebra map. Both inverse
laws follow from the actual ring equivalence.

`mapEmbeddingPointFamily` applies an `Ω`-algebra map to every coordinate and
retains the conjugate scalar equations. Tensor induction proves that embedding
evaluation commutes with this coefficient change, so the point equivalence is
natural for all coefficient-algebra maps.

This is an internal generalization from the existing coefficient decomposition
in `Torus.WeilRestrictionEmbeddings` to arbitrary affine coordinate algebras.
The current module assumes bijectivity of canonical embedding evaluation; it
does not prove it from finite separability. It constructs ring and algebra-point
coordinates only, and does not yet construct a group-scheme splitting or prove
connectedness, reductivity or local Kneser–Tits.
