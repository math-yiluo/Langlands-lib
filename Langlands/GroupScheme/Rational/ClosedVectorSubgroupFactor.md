# Capturing vector retracts of closed vector subgroups

This internal construction produces an actual vector retract for every closed
subgroup `i : H ⟶ Vₙ` over an arbitrary field `k` in universe `u`. After base
change to `SeparableClosure k`, its section captures all maps from the affine
line taking zero to the identity. The factoring maps are relative-scheme
morphisms; they need not be group homomorphisms. No smoothness, connectedness,
reducedness, characteristic, infinitude or perfection premise is required.

`exists_annihilating_polynomialRow_of_affine` extends the corepresented
additive-row adapter to any affine source. The canonical affine coordinate
isomorphism transports the proper closed embedding to the corepresented model.
The nonzero additive row there, followed by the inverse coordinate isomorphism,
annihilates the original embedding as an actual group homomorphism on all tests.

`exists_lowering_separableClosure` first obtains affineness from the closed
embedding into the standard vector group. If the embedding is not an
isomorphism, the preceding adapter gives a nonzero additive polynomial row
annihilating it. The existing
`Unipotent.exists_polynomialKernelAmbientCapture` constructs a vector envelope
of rank strictly less than `n`, a retraction from the whole ambient vector
group, and capture of pointed affine-line maps killed by the changed row.
Each changed pointed map of `H` becomes such an ambient map, since the row
annihilates `i`. This supplies the required strict lowering rule.

`exists_capturing_separableClosure` applies the generic ambient-dimension
induction with base map `Spec (SeparableClosure k) ⟶ Spec k`, affine-line test
object and its zero section. It obtains an integer `r`, actual homomorphisms
`l : Vᵣ ⟶ H` and `q : H ⟶ Vᵣ`, the identity `l ≫ q = id`, and capture by the
changed `l` of every pointed affine-line map of the changed `H`.

`SeparableLineRetraction H` packages this dimension, section, retraction,
splitting identity and capture property. `separableLineRetraction n H i hi`
chooses an inhabitant from the proved existence theorem. The construction
allows `r = 0`.

The provenance is internal: the contribution composes the affine-coordinate
comparison, primitive additive-relation adapter, strict polynomial-row ambient
capture, and scheme-theoretic-intersection induction. Worker 864 supplied the
ambient polynomial-kernel factors and capture; Worker 1371 supplied the
generic pointed affine-line capture and constant-kernel adapter used by that
dependency. This contribution does not yet assert smoothness, unipotence or
constancy of a complementary full kernel, or the host's unconditional theorem
for groups without a supplied vector embedding.
