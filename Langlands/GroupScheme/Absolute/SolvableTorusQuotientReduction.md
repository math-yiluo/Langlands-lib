# Constructing a split-torus quotient of a solvable group

Authors: Worker 1438, Worker 1432 and Worker 1456.

This internal construction combines the published Lie–Kolchin embedding and
split-torus image factorization. It constructs an actual fppf quotient without
assuming kernel geometry or closed-subgroup unipotence. Its final theorem
retains precisely those two mathematical prerequisites as explicit hypotheses.
It does not prove the unconditional `SolvableTorusQuotientStatement` or
`CentralizerBorelIntersectionStatement`.

`TriangularTorusQuotientData H` records a dimension `N`, a closed embedding
`j : H ⟶ T_N` into the concrete triangular group, a split torus `D`, a
homomorphism `q : H ⟶ D`, and a closed inclusion `m : D ⟶ D_N`. Here `D_N`
is the block Levi for the descending weights `i ↦ -(i.val : ℤ)`, and `d`
is its block diagonal projection. The fields assert `q ≫ m = j ≫ d`,
closedness of the actual inclusion of `kernel (j ≫ d)`, and
`RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (kernelι (j ≫ d))) q`.
This last property includes flatness, scheme surjectivity and local finite
presentation of `q`, together with equality of the kernel subgroup functors
on every test scheme. Smoothness, connectedness and unipotence of that
kernel are not part of the data.

For a smooth connected affine solvable group `H` over an algebraically closed
field `k`, `IsSolvableGroupScheme.triangularTorusQuotient` chooses these data.
The published `solvableTriangularEmbeddingStatement` supplies `N`, `j` and
its closedness. The descending weights are injective, so the existing
`GeneralLinear.diagonalTorusIso` identifies `D_N` with the split torus
indexed by `ULift (Fin N)`. Applying the published
`IsSplitTorus.exists_fppfQuotient_factor` to `j ≫ d` supplies `D`, `q`,
`m`, the factorization and the fppf quotient assertion. Since a split torus
is affine and hence separated, the diagonal kernel inclusion is closed.
Classical choice selects these actual objects.

`TriangularTorusQuotientData.isUnipotent_kernel` works over any field and
explicitly assumes `UnipotentClosedSubgroupStatement`. The pullback
universal property gives a map from `kernel (j ≫ d)` to `kernel d`.
Its composite with the second kernel inclusion is the first kernel inclusion
followed by `j`. That composite is closed, and the second kernel inclusion
is a monomorphism, hence separated. Cancellation against that separated
morphism makes the comparison map closed. Composing with the inverse of
`GeneralLinear.blockUnipotentIsoKernel` presents the smaller kernel as a
closed subgroup of the concrete unitriangular group. The existing closed
inclusion into `GL_N` makes the ambient unitriangular group affine and
locally of finite type; smoothness of `GL_N` supplies the latter property.
The published `unitriangularUnipotent` and the explicit inheritance premise
therefore give unipotence of the diagonal kernel. Dimension zero is included.

Finally, `solvableTorusQuotient_of_kernel_prerequisites` assumes
`TriangularDiagonalKernelGeometryStatement` and
`UnipotentClosedSubgroupStatement`, at arbitrary universe `u`. The first
supplies smoothness and connectedness of the chosen actual diagonal
kernel. The preceding lemma supplies unipotence. The published
`HopfPrimitive.isNormal_range_kernelι` supplies normality on every test.
The chosen kernel, its actual inclusion, `D` and `q` then satisfy every
clause of the unchanged `SolvableTorusQuotientStatement`.

The provenance is internal: the construction composes the cited Library
interfaces and retains the missing inputs. The restricted-kernel proof
and the elementary triangular adapters specialize the unreviewed
`SolvableUnipotentAdapters`, `SolvableUnipotentKernelAssembly` and
`SolvableUnipotentPart` draft of Workers 1432 and 1456, revision 3. Their
general helper declarations are not copied into a parallel API here.
No additional assertion from the literature is used.
