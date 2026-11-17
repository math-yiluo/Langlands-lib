# Base change of actual diagonalizable-source coordinate maps

For an actual homomorphism `f : D_R(M) → G` to an affine group,
`diagonalSourceScalarMap S f` is the scalar extension of its canonical
coordinate map, written as `S ⊗[R] O(G) → S[M]`. The construction is defined
for arbitrary commutative rings and any abelian character group `M`.

`tensorMap_bijective_of_baseChange_isIso` first handles arbitrary maps of
affine spectra. The published tensor-coordinate naturality isomorphisms
express the actual base-changed scheme map as the spectrum of its tensor
coordinate map, conjugated by isomorphisms. If the actual base change is an
isomorphism, so is that spectrum. Full faithfulness of `Spec` reflects the
isomorphism back to the ring map, making its underlying function bijective.

`diagonalSourceScalarMap_bijective` applies this criterion to the canonical
coordinate map of `f`. The exact Hopf-spectrum comparison expresses its
actual base change as the base change of `f`, conjugated by the source and
target coordinate isomorphisms. The canonical group-algebra scalar-extension
equivalence then identifies its tensor coordinate map with
`diagonalSourceScalarMap`. Thus an isomorphism of the actual base-changed
morphism gives a bijective standard scalar-extended coordinate map.

`diagonalSourceCoordinates_mem_smul_of_baseChange_isIso` applies to any base
ideal `J` when the actual reduction of `f` over `R/J` is an isomorphism.
If the coordinate image of `a` belongs to `J · R[M]`, its tensor reduction
vanishes. The bijective scalar-extended map therefore makes `1 ⊗ a` vanish.
The standard kernel identity `LinearMap.ker_tensorProductMk` gives
`a ∈ J · O(G)`. No flatness or nilpotence assumption is required for this
membership implication.

Over a local base ring,
`diagonalSourceCoordinates_unit_coeff_of_special_isIso` uses surjectivity
of the residue-field coordinate map and the published nonvanishing
coefficient theorem to find a coefficient nonzero in the residue field in
every character degree. The local-ring residue criterion says exactly that
these coefficients are units. Separately, `coordinate_isNoetherianRing`
derives noetherianity of `O(G)` from finite type over a noetherian base using
the published actual-coordinate finite-type instance.

These are internal derived comparisons between actual scheme morphisms and
the algebraic input conditions for the complete-local immersion argument.
They use published tensor-spectrum naturality, Hopf-coordinate comparisons,
scalar-extension of group algebras, right-exactness of tensor products, and
finite-type noetherianity. They do not assert surjectivity or an
idempotent-generated kernel for the original coordinate map, and hence do
not by themselves prove the complete-local immersion conclusion.
