# Actual Picard families over successive quotients of one local source

This internal construction extends an actual pointed Picard family from one
Artinian quotient of a fixed Noetherian local source to another quotient of the
same source. It uses the smallest subspace that kills the actual obstruction,
retains a full pointed restriction isomorphism, and controls both equation
ideals. It does not assert formal versality or construction of an atlas.

Fix a commutative ring `k`, a field `K` with its given `k`-algebra structure,
a commutative Noetherian local `k`-algebra `R`, and a surjective augmentation
`ε : R →ₐ[k] K`. Let `f : X → Spec k` be an actual flat proper scheme morphism
and `M` an actual line bundle on its residue-fibre relative scheme. All objects
have arbitrary common universe `u`. No section of an augmentation, coefficient
field inside `R`, or `K`-algebra structure on a source test is chosen.

`Stage ε f M` records an actual augmented Artinian test `A`, an actual
surjective algebra map `π : R → A`, its exact augmentation equation
`A.augmentation.comp π = ε`, and an actual pointed deformation `L_A` of `M`
over `A`. The `Stage` data itself needs only the ring and geometric structures
that occur in these fields; the local and Noetherian hypotheses on `R`, and
the flat and proper hypotheses on `f`, are used to construct its successor.
`Stage.equations` is the actual ideal `J = ker π`.

The imported `ElementarySourceExtension` provides the actual augmented test
`D = R/(mJ)`, where `m` is the maximal ideal of `R`, a surjective projection
from `R`, and an elementary surjection `q : D → A`. The declarations
`sourceTest`, `sourceProjection`, and `sourceReduction` retain exactly these
constructions for a stage. Elementary-kernel finiteness supplies a finite
basis of the actual kernel of `q`; proper coherent cohomology supplies a finite
basis of the actual residue-fibre structure-sheaf H².

`Stage.obstructionSubspace` applies the existing
`ArtinianKernelQuotientObstruction.obstructionCoefficientSubspace` to the
actual obstruction of `L_A` for `q`, with the existing chosen free bases of
these two finite-dimensional spaces. Its dimension is at most the dimension
of residue-fibre H², by `obstructionSubspace_finrank_le`.

For every `K`-linear subspace `W` of that actual elementary kernel,
`quotient_lift_iff` says that an actual pointed lift of `L_A` to the actual
subspace quotient `D/W` exists if and only if
`obstructionSubspace ≤ W`. This is the imported exact pointed lifting
criterion for these chosen bases. Thus the chosen subspace is the least one
allowing a pointed lift among all these subspace quotients. The criterion
retains the full isomorphism from the restriction of the lift to `L_A`,
including its prescribed residue identification.

Write `W₀` for this least subspace and `Q = D/W₀`. A private `liftData` chooses
an actual pointed family over `Q` and an actual pointed restriction
isomorphism, using `quotient_lift_iff` and reflexive containment.
`Stage.next` is the resulting actual stage over `Q`. Its source cover is the
composite `R → D → Q`; surjectivity is composition of the two existing
surjections, and its augmentation equation follows from the two original
augmentation equations. Its family is the chosen pointed family.

`Stage.reduction` is the actual elementary quotient reduction `Q → A`.
`reduction_elementary` reuses the existing elementary quotient theorem.
`reduction_cover` proves that the composite of the new cover with this
reduction is exactly the original cover, using `projection_reduction` and
`ElementarySourceExtension.reduction_projection`.
`Stage.transition` retains the actual pointed isomorphism from restriction
of the new family to the old family. The implementation transports the
chosen isomorphism through explicit equalities of the reduction and family,
using a generic congruence construction. These transports change no bundle
or residue datum.

Finally the two equation-ideal bounds are

```text
m * J ≤ J_next ≤ J.
```

`maximalIdeal_mul_equations_le` observes that the projection `R → D` kills
`mJ`, so its further quotient to `Q` also kills that ideal.
`next_equations_le` evaluates `reduction_cover` on a new equation, showing
that the old cover kills it as well. These are containments of the actual
kernels of the two fixed-source presentations.

The provenance is internal: the construction combines the existing actual
elementary source extension, obstruction coefficient subspace, exact pointed
lifting criterion and augmented quotient maps. Iteration, comparison with
adic thickenings of a complete Noetherian local hull, formal versality,
effectivity, algebraization and the exact field Picard-stack atlas remain
separate obligations.
