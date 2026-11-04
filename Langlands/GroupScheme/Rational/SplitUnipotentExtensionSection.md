# Homomorphic sections of split unipotent extensions of tori

This internal construction gives homomorphic sections of torus quotients with
split-unipotent full kernel. The field `k : Type u` is arbitrary. The two exact
propositions `RelativeRoot.SplitUnipotentStableVectorSubgroupStatement.{u}` and
`RelativeRoot.TorusVectorActionLinearizationStatement.{u}` remain explicit inputs.

`IsTorus.exists_splitUnipotentExtensionSection` takes group schemes `U`, `E`
and `H` over `Spec k`, a smooth connected affine `E`, a smooth connected `U`,
a homomorphism `n : U ⟶ E` monomorphic as a map of relative schemes, and
`q : E ⟶ H` satisfying
`RelativeRoot.IsFppfQuotient (SubgroupFunctor.range n) q`. Thus `n` represents
the full scheme-theoretic kernel on every relative test scheme. The hypotheses
also include `IsUnipotent U`, `RelativeRoot.IsSplitUnipotent U`, `IsTorus H`,
and the two propositions above. It produces `s : H ⟶ E` with
`s ≫ q = 𝟙 H`. In particular this is a group-scheme morphism over the original
field. No separate affineness assumption on `U` is required.

`IsTorus.splitUnipotentExtensionSection` chooses such a morphism from the
existence theorem. `IsTorus.splitUnipotentExtensionSection_comp` records the
same identity after composition with the original `q`. The fppf quotient's
flatness, surjectivity and local finite presentation are part of the existing
predicate; smoothness of `q` follows internally from the smooth represented kernel.

The lower-level theorem
`TorusUnipotentExtension.exists_section_of_smooth_kernel` instead assumes a
smooth surjective `q`, smooth connected affine `E`, and a connected actual
`kernel q` which is unipotent and split unipotent. Its conclusion is the same
section identity, with `IsTorus H` and the two exact propositions retained.

The proof uses strong induction on the smooth dimension of the actual kernel.
The trivial-kernel case uses `TorusUnipotentExtension.isIso_of_trivial_kernel`.
That helper assumes a flat, surjective, quasi-compact map and triviality of the
identity range of its actual kernel on all tests; it proves monicity on test
points and applies the flat surjective monomorphism criterion. In the induction,
quasi-compactness of `q` follows from affineness of `E`. Otherwise ambient
conjugation supplies a stable positive-dimensional
vector subgroup of the kernel. Its composite inclusion in the extension group
is a normal closed subgroup. The published normal quotient theorem constructs
the smooth affine quotient by this subgroup. Homomorphism descent factors the
original torus map through that quotient.

The published factored-kernel pullback supplies a smooth surjective map between
the two actual kernels. The new kernel is smooth, connected, affine, unipotent
and split unipotent. The relative dimension of this map is the positive vector
dimension, so the new kernel has strictly smaller dimension. Induction gives
a section in the quotient. It is closed since it is a section of a separated
map. The vector quotient torus lift construction lifts this section to the
original group and its composite is the original identity on the torus.

For the fppf-kernel adapter, the existing `KernelRepresentative.iso` identifies
the actual kernel with `U`, preserving connectedness, unipotence and splitness.
The represented-kernel smoothness theorem supplies smoothness of `q`.
The lower-level theorem then applies.

The provenance is internal: the construction combines the Library's normal
subgroup quotient, fpqc homomorphism descent, factored-kernel pullback, smooth
surjective split-unipotent image, vector quotient torus lift, represented-kernel
comparison and smooth relative-dimension results. It retains every field and
characteristic, including finite and imperfect fields and nonsplit tori.
This is supporting work for rational maximal-torus conjugacy. The stable-vector
and linearization propositions, and the unconditional conjugacy theorem, remain
proof obligations.
