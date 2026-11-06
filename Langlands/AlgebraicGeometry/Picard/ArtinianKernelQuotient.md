# Actual ideal and cohomology maps for an elementary kernel quotient

This internal construction gives the actual ideal-module and cohomology maps
for quotienting an elementary Artinian kernel by a residue-field subspace.
It retains the source-ring actions and the already descended residue-field
actions on the original cohomology groups.

Fix a commutative ring `k`, a field `K` with its specified `k`-algebra
structure, an actual scheme morphism `f : X → Spec k`, and an elementary
surjection `q : A → B` of augmented Artinian tests. Let `W` be any
`K`-linear subspace of the actual kernel of `q`. All objects have the
arbitrary common universe `u`. The elementary hypothesis is supplied as
`Fact (IsElementarySurjection q)`.

The imported `ElementaryKernelSubspaceQuotient` constructs the actual
quotient test `Q = A/W`, where the image of `W` in `A` is an ideal, and
the elementary arrows `π : A → Q` and `r : Q → B`. Their composite is
`q`. No section of the augmentation and no `K`-algebra structure on `A`
or `Q` is chosen. The zero and whole kernel subspaces are included.

Write `X_A`, `X_Q` and `X_B` for the actual relative schemes.
Contravariance gives morphisms `h : X_Q → X_A` and `j : X_B → X_Q`.
The lemma `factorization` proves `j ≫ h = X(q)` by functoriality and
`projection_reduction`.

The actual kernel module `J_q` is the sectionwise kernel of the structure
map for `X(q)`; likewise `J_r` is the structure kernel of `j`.
`idealMap` is a morphism

```text
J_q → h_* J_r.
```

It uses the actual factorization map `compositionMap`, with equality
transport identifying the composite kernel with `J_q`. A private generic
helper performs this transport before specializing to the Artinian
quotient. The public `idealMap_eq_kernelModuleMap` makes its exact
equality transport and the existing `kernelModuleMap` explicit, by applying
a generic reflexive identity before specializing the scheme objects. Its section formula and inclusion square follow by equality
elimination from those of `compositionMap`.

For every open `U` of `X_A`, `idealMap_app` says that a kernel section
`a` maps to `h.app U a.val`. The lemma `idealMap_ι` proves that this map
commutes with the actual kernel inclusions and the structure-module map
`O_X_A → h_* O_X_Q`. Thus the map is defined by the genuine quotient
structure map on sections.

Let `p_A : X_A → Spec A` and `p_Q : X_Q → Spec Q` be the actual
projections, and let `φ : A → Q` be the ring homomorphism of `π`.
The lemma `projection_square` is naturality of these projections:
`h ≫ p_A = p_Q ≫ Spec.map φ`.

For each natural number `n`, `relativeCohomologyMap` is the
`A`-linear morphism

```text
H_A^n(X_A, J_q) → Res_φ H_Q^n(X_Q, J_r).
```

Both `h` and `j` are closed immersions because their ring arrows are
surjective. In particular they are affine, and `J_r` is quasi-coherent.
The implemented cohomology map first applies actual relative cohomology
to `idealMap`, then applies the inverse affine-pushforward cohomology
isomorphism, and finally the forward base-ring comparison for
`projection_square`. These orientations give the displayed target with
restriction of scalars through the specified quotient map.

The groups `Cohomology f q n` and `Cohomology f r n` are the unchanged
actual ideal-cohomology groups from `ArtinianPicardObstructionFinite`.
`cohomologySemilinearMap` uses their existing `relativeEquiv`
identifications to express `relativeCohomologyMap` as a `φ`-semilinear
map of those groups, with the original source-ring actions. Additivity
and semilinearity follow from the three linear maps in the construction.
No flatness or properness of `f` is needed up to this point.

Assuming `IsProper f`, `cohomologyLinearMap` is `K`-linear for the
previously defined `ArtinianPicardObstructionFinite.residueModule`
actions on both cohomology groups. The proof keeps the same additive
map. For a scalar `c : K`, augmentation surjectivity supplies
`a : A` mapping to `c`. The existing `augmentation_smul` identifies the
source `K`-action with the `A`-action; semilinearity moves that action
through the map; the equality
`A.augmentation a = Q.augmentation (φ a)` and the target
`augmentation_smul` recover the target `K`-action. Thus no action is
transported through newly chosen coordinates.

The provenance is internal: this specializes the actual structure-kernel
factorization map to the imported elementary quotient and combines
existing affine-pushforward, base-ring and scalar-descent comparisons.
It asserts no further geometric existence theorem. Compatibility with
residue-fibre tensor coordinates, naturality of Picard obstruction
classes, a complete local hull, effectivity, algebraization and the
exact Picard-stack atlas remain separate obligations.
