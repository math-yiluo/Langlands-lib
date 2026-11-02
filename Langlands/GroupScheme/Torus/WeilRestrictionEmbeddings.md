# Embedding coordinates for the Weil-restricted multiplicative group

Worker 207.

This internal adapter takes commutative rings `k`, `K`, and `Ω` in the
same universe, with `k`-algebra structures on `K` and `Ω`, and an explicit
proof `h` that `embeddingEvaluation k K Ω` is bijective. The definition
`embeddingDecomposition` regards that same map as an `Ω`-algebra
equivalence, so its formula is still `c ⊗ x ↦ (τ ↦ c * τ(x))`.
No existence or bijectivity theorem is supplied here.

For a commutative `Ω`-algebra `R` with a compatible `k`-algebra structure,
and a finite type of homomorphisms `K →ₐ[k] Ω`,
`embeddingDecompositionTensorEquiv_apply` identifies the tensor
decomposition map of `WeilRestrictionDecomposition` with
`tensorCoordinate (IsScalarTower.toAlgHom k Ω R) τ` at each index `τ`.
In particular, on the original tensor it sends `x ⊗ r` to
`algebraMap Ω R (τ(x)) * r`. This purely algebraic part does not require
finite projectivity of `K` over `k`.

The scheme constructions additionally assume that `K` is finite projective
as a `k`-module and that the homomorphism index is finite. `embeddingIso`
and `embeddingCommIso` identify the actual base change of
`WeilGm.groupScheme (CommRingCat.of k) K`, or its commutative version, with
the split torus indexed by all `k`-algebra homomorphisms `K → Ω`.
`embeddingPointsEquiv` gives its coordinates on every test scheme `T`
over `Spec Ω`. The coefficient map `embeddingCoefficientMap k Ω T` is
the structural map `Ω → Γ(T.left, ⊤)`, regarded as a map of `k`-algebras
using the restricted `k`-structure.

`embeddingPointsEquiv_apply` identifies each coordinate with the unit map
of `tensorCoordinate` applied to the original point: first use
`baseChangePointsEquiv` to regard the point over `Spec k`, then use
`WeilGm.pointsEquiv` to obtain its unit in `K ⊗[k] Γ(T.left, ⊤)`.
`embeddingCommIso_hom_points` proves agreement with the actual scheme
isomorphism. `embeddingPointsEquiv_naturality` proves compatibility with
every map of test schemes, including nonreduced tests.

For any `σ : Ω ≃ₐ[k] Ω`, changing the structure of `T` to
`T.hom ≫ Spec σ` changes its coefficient map to the old coefficient map
composed with `σ`. The lemmas `embeddingCoefficientMap_descent` and
`embeddingCoefficientMap_descent_eq` express this using the sections map
of the canonical `descentTestIso`. That sections map is the identity on
the underlying ring, while retaining the correct `k`-algebra structures.

The resulting all-test formula `embeddingPointsEquiv_descentPoint` says
that the coordinate at `τ` of the same original point, now seen with the
changed `Ω`-structure, is its old coordinate at `σ ∘ τ`. The proof uses
the just-established tensor-coordinate comparison, naturality of the
original Weil point model along `descentTestIso`, and
`tensorCoordinate_natural` and `tensorCoordinate_comp`.

All constructions and laws are intrinsic consequences of the canonical
tensor map, the supplied bijectivity, and the existing decomposition and
descent APIs. They impose no field or separability assumption. They do
not derive bijectivity from finite separability or assert a lattice
Galois-equivariance, continuity, or classification theorem. Those remain
separate obligations.
