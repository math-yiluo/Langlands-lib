# Galois-equivariant cocharacter tensor evaluation

This module is a derived internal construction from `Torus.PointsTensor`,
`Torus.LatticeGalois`, `CocharacterTransport`, `GaloisPointRational`,
`GaloisCocycle`, and the actual unit representation in
`ClassFieldTheory.Local.Cohomology`. It uses their existing scheme maps,
cocharacter transport, and point comparisons; no additional structural
assertion about algebraic groups is assumed. All fields and schemes have
arbitrary common universe `u`, and scalars are `ULift.{u} ℤ` with the
ordinary integer action. The extension `L/k` need not be finite or Galois.
The acting group is the actual automorphism group `L ≃ₐ[k] L`.

`baseChanged k L T` is the actual commutative base change of `T` along
`Spec L → Spec k`. `unitsPointEquiv L` identifies additive field units
with additive identity-test points of the multiplicative group over `L`.
The linear map `coefficientEvaluation k L T` applies this identification
in the first tensor factor, evaluates the actual cocharacter using
`TorusPointsTensor.tensorEvaluation`, and projects to the existing
coefficient points of `T`. The pure-tensor formula is

`x ⊗ ν ↦ Additive.ofMul (baseChangeCoeffEquiv (unitPoint(x) ≫ ν))`.

`coefficientPointEquiv` is a linear equivalence when the actual base
change satisfies `IsSplitTorus`. It composes the existing tensor-point
linear equivalence with the two point identifications. Its forward map
is exactly `coefficientEvaluation`; the map therefore does not depend on
the splitting chosen in the bijectivity proof.

The equivariance proof starts with the actual map `changedTestArrow`
from the identity test scheme with structure changed by `Spec σ` back
to the identity test scheme. Its underlying scheme map is `Spec σ`.
`unitPoint_galois` proves that pulling back a unit point along this map
is the unit point for `Units.map σ x`. The proof applies the naturality
of the multiplicative-group points equivalence and the naturality of
the global-sections comparison `Γ(Spec L) ≅ L`.

`transportEvaluation_left` applies `transportCocharacter_points` to
that transformed unit point. Projecting the resulting equality to the
original group scheme gives the underlying scheme-map identity

`unitPoint(σx) ≫ transport(ν) ≫ projection = Spec σ ≫ unitPoint(x) ≫ ν ≫ projection`.

The published coefficient action is precomposition by that same spectrum
map, as recorded by `algSpec_galois_left`. The pure-evaluation projection
formula is `coefficientEvaluation_tmul_left`. Together these give
`coefficientEvaluation_galois_tmul`: evaluation intertwines the diagonal
action on units and transported cocharacters with the actual coefficient
action. The projection lemmas keep the categorical conversions separate
when the kernel checks the proof.

`latticeRepresentation` packages the actual cocharacter lattice with
its existing integral transport action, restricted to the lifted integer
scalars. For an actually split base change, `tensorPointIso` is the
isomorphism of representations

`unitsRepresentation k L ⊗ latticeRepresentation k L T ≅ pointRepresentation T`.

Its underlying linear equivalence is `coefficientPointEquiv`.
Equivariance follows by checking pure tensors and applying the proved
Galois evaluation formula. This supporting construction supplies no
unconditional cohomology vanishing or proof of Steinberg quasi-splitness.
Those remain separate obligations of the host task.
