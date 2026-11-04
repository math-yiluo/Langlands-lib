# Lifting arbitrary target tori through a central isogeny

`CentralIsogenyTorusLiftStatement.{u}` asserts the following over every
field `k : Type u`. Let `π : G ⟶ H` be an actual central isogeny with
affine source. Every actual commutative torus `S` with a closed subgroup
embedding `i : S.toGrp ⟶ H` admits an actual commutative torus `T`, a
closed subgroup embedding `j : T.toGrp ⟶ G`, and an isogeny
`f : T.toGrp ⟶ S.toGrp` satisfying `j ≫ π = f ≫ i`.
`centralIsogenyTorusLiftStatement` proves this proposition, and
`IsCentralIsogeny.exists_isogeny_torus_lift` supplies the direct interface.

Here an isogeny means finite, flat and surjective on underlying schemes;
centrality concerns the full scheme-theoretic kernel on every test
scheme. The result allows nonsplit and rank-zero tori, imperfect fields,
positive characteristic and inseparable isogenies. It assumes no
reductivity, connectedness, smoothness or finite-type hypothesis on the
ambient group schemes. Affineness of `G` is the stated ambient
geometric hypothesis.

## Derived provenance and implemented proof

The proof combines the existing kernel exponent, power lift, actual
torus-image, and scheme-morphism interfaces. This is a derived
supporting result; it introduces no additional literature assertion.

`IsCentralIsogeny.exists_pow_eq_one_kernel` supplies a positive integer
`N` that kills every point of the scheme-theoretic kernel of `π`.
`IsCentralIsogeny.exists_comp_eq_multiplication_comp` then gives a
homomorphism `Φ : S.toGrp ⟶ G` with
`Φ ≫ π = [2N] ≫ i`. The theorem
`IsTorus.flat_and_surjective_multiplication` from `Torus.Multiplication`
makes `[2N]` surjective even when `S` is nonsplit or the characteristic
divides `2N`.

The helper
`exists_subtorus_lift_of_surjective_torusParametrization` takes the
actual schematic image of `Φ`. The actual torus-image theorem makes
this image a torus `T`, and the schematic image construction supplies
its closed inclusion `j` and schematically dominant projection `p`.
Since `p ≫ j ≫ π` factors through the closed immersion `i`,
`SubgroupFunctor.range_comp_le_iff_of_isSchemeTheoreticallyDominant`
descends this containment to `j ≫ π`. Representability of the range of
`i` gives an actual group-scheme homomorphism `f` with `f ≫ i = j ≫ π`.
Cancellation of the closed inclusion identifies `p ≫ f` with `[2N]`.
Surjectivity of that composite implies surjectivity of `f`.

The composite `f ≫ i = j ≫ π` is finite because both `j` and `π` are
finite. The closed immersion `i` is separated, so `IsFinite.of_comp`
makes `f` finite.

The helper `IsTorus.flat_of_surjective_hom` proves flatness of a
surjective homomorphism between arbitrary actual field tori. Torus
geometry supplies smoothness, affineness and finite type. The target is
therefore reduced and locally noetherian, and the map is quasi-compact,
locally of finite type and dominant. The published theorem
`DominantHomFlat.flat_of_isDominant` proves its flatness. Applying this
to `f` completes the required isogeny.

## Consumer boundary

The conclusion has exactly the all-target-torus form used by
`SemisimpleIsogenyReductionStatement`. It discharges that clause for
each applicable central isogeny. It does not construct the structural
isogeny to a nilpotent group or a group with a geometric noncentral
semisimple Lie element, prove termination of such a construction, or
prove Cartan generation.
