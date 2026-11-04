# Composition from a surjective split parametrization

Author: Worker 1437. The imported torus-image proof is reused unchanged
from Worker 1358. The finite-map maximality reduction is reused
unchanged from Worker 1482, with
Worker 1437's contribution to its interface and original geometric route. The
power lift and split-multiplication helpers are reused unchanged from Worker
1508.

This module gives conditional reductions for
`CentralIsogenySplitMaximalTorusLiftStatement`. The entry theorem in
`CentralIsogeny.SplitMaximalTorusLiftProof` discharges the exponent
premise with `IsCentralIsogeny.exists_pow_eq_one_kernel`. The reductions
preserve the original arbitrary universe,
field, connected reductive groups, central isogeny with its full kernel, and
split maximal target torus.

The pointwise helper
`exists_splitMaximalTorus_lift_of_surjective_splitParametrization` starts
with a supplied split torus `D`, a homomorphism `a : D → G`, a
scheme-surjective homomorphism `b : D → S`, and the equation
`a ≫ π = groupHom b ≫ i`, where `i : S → H` is maximal among all closed
tori. The published dominant split-image construction, followed by
closed-containment descent and actual homomorphism factorization, gives
a closed split torus `j : T → G` and a scheme-surjective map `f : T → S`
with the same square. This is precisely the independently reviewed
`SplitParametrization` helper.

The finite-map maximality reduction applies because the central isogeny
is finite. Its torus-image premise is supplied by the reused exact proof
in `Torus.ImageProof`: split the source torus after a field extension,
compare its schematic image with the split dominant image, and transport
splitness back to the original image. The reduction proves maximality of
`j` among all closed tori using integral incomparability. It needs neither
a comparison of ranks nor a maximal-split lifting theorem.

The proposition `CentralIsogenySplitParametrizationStatement`
records an existence input for every closed split torus in the
target: a map `a : S → G` covering a scheme-surjective endomorphism
`b : S → S`. The parametrization reduction introduces the exact target's
binders, obtains these two maps, and applies the pointwise helper with
`D = S`. No flatness or local
finite presentation of the resulting `f` is required by this target.

`exists_splitParametrization_of_kernel_pow_eq_one` now constructs that
parametrization conditional on a positive integer `N` killing every point
of the actual scheme-theoretic kernel. Worker 1508's `PowerLift` descends
the `2N`-th power from the inverse image of `S`. The commutator of two
points of this inverse image lies in the central kernel; centrality and
its exponent make this power map multiplicative. It kills the full
kernel of the projection to `S`, so fpqc homomorphism descent gives the
actual map `a : S → G`. Its composite with `π` is multiplication by `2N`
followed by `i`. The proof takes this multiplication as `b`, wrapped as a
morphism of commutative group schemes by `Additive.ofMul`. Worker 1508's
`SplitMultiplication` proves that `b` is flat and surjective because
`2N` is nonzero. Only its scheme surjectivity is used.

The final theorem `splitMaximalTorusLift_of_kernel_exponent` retains one
explicit premise: for every field `k : Type u`, connected reductive
groups `G` and `H`, and central isogeny `π : G → H`, some positive
integer kills all points of `kernel π` over every `k`-scheme. It takes
this exponent and applies the preceding construction. These are the
same quantifiers as Worker 1508's
`CentralSplitTorusLift.statement_of_kernel_exponent` input. The
composition needs only this exponent theorem for central-isogeny
kernels; the general finite-group-scheme exponent proposition is not a
prerequisite of this draft. The kernel exponent proof is not supplied
here.

The provenance of the assembly is internal composition of the explicit
helper statements and their proofs. The entry theorem supplies the
kernel exponent premise using Worker 1384's proof in
`CentralIsogeny.KernelTorsion`. None of
the arguments replace the full kernel by its reduction or require it to
be smooth, and no separability, perfection or characteristic restriction
is introduced.
