# A single coefficient label for Hodge–Tate decompositions

The published `HodgeTate.HasHodgeTateDecomposition` tensors over
`ℚ_p` and compares all coefficient labels at once. For the cuspidal Harris
reduction the separate labelled condition suffices. For a finite extension
`F` of `ℚ_p` and an `F`-linear representation of `Gal(F̄/F)`, the identity
label forms `C_F ⊗[F] V`, where `C_F` is the published completed algebraic
closure. The coefficients of the representation enter through the given
embedding of `F` in `C_F`. The extension of the Galois action to `C_F`
fixes `F`, which is the fact implemented by `galoisLinearOverBase`.
Uniform continuity of each scalar multiplication gives the `F`-algebra
structure on the completion.

`HodgeTate.HasLabelledHodgeTateDecomposition` asks for a `C_F`-linear
equivariant isomorphism from `n` cyclotomic twists each repeated `m` times
to this tensor product. The action on the target is `σ ⊗ ρ(σ)`. On the source
component at `i` it is `χ_cyc(σ)^(k i) σ`. Distinctness of weights is a
separate premise on `k` for consumers that require it.

`HasLabelledHodgeTateAt` uses the actual completion `L_λ` of a number field
of coefficients `L`. It pulls a representation of the absolute Galois
group of `E` back along a field embedding `E → L_λ`. For the fixed
archimedean label in the geometric branch this embedding comes from
`E → L → L_λ`. `HasLabelledHodgeTateOver` uses the same label composed with
the specified coefficient extension `L_λ → Λ`, with the actual composed
`ℚ_p`-algebra structure on `Λ`.

This is a derived interface for the single selected label in Taylor's
multiplicity argument. It refines the notation needed in the proof and
does not assert the existence, descent or comparison of any Hodge–Tate
decomposition.

## Sources

- M. Harris, *Supercuspidal representations in the cohomology of Drinfel'd
  upper half spaces*, Invent. Math. 129 (1997), §3, pp. 102–103, for the
  cyclotomic twists in the Hodge–Tate comparison used by Taylor's argument.
  Registered `harris-1997-drinfeld-cohomology`, SHA256
  `aea284b917442459028b710dbfd9ae537631490504f3bc6d54a1e76ee697e0d9`.
- M. Harris and R. Taylor, *The Geometry and Cohomology of Some Simple
  Shimura Varieties* (2001), VII.1.9, pp. 227–228, for the Hodge–Tate
  graded pieces at a selected embedding in the regular algebraic case.
  Registered `harris-taylor-2001-geometry-cohomology-simple-shimura`,
  SHA256 `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
