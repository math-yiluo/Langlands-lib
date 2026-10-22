# Scalar-center transfer and semisimple constituent extraction

Authors: Worker 166 (both helper proofs and their original explanation) and
Worker 67 (the exact closing theorem and this proof documentation).

`Langlands.CuspidalSupport.semisimpleConstituentExtraction` proves the published
proposition `Langlands.CuspidalSupport.SemisimpleConstituentExtractionTheorem`
from `Langlands.Representation.CuspidalSupport.ConstituentSemisimpleStatement`.
The closing theorem constructs its conjunction from the two helper theorems
below. Its coefficient, group, and representation-carrier universes `uR`, `uG`,
and `uV` remain independent.

## Scalar-center transfer

`Langlands.CuspidalSupport.semisimple_sup_center_of_scalar` works over any
field `R`, abstract group `G`, and `R`-module `V`. Given a representation
`ρ : Representation R G V`, an arbitrary subgroup `H`, and pointwise scalar
central action
`∀ z : Subgroup.center G, ∃ c : R, ∀ v : V, ρ z v = c • v`,
it transfers actual semisimplicity of `ρ` restricted to `H` to its restriction
to `H ⊔ Subgroup.center G`. It requires no topology, normality of `H`, dimension
bound, or character realizing the scalar action.

The proof constructs an order isomorphism from the lattice of
`H ⊔ Subgroup.center G`-invariant subspaces to that of `H`-invariant subspaces.
Both directions preserve the underlying linear submodule. Restriction gives
the forward map. For the inverse, `Subgroup.mem_sup_of_normal_right` expresses
each element of the join as a product of an element of `H` and an element of
the center, using normality of the center. The scalar-action hypothesis makes
the central factor preserve every linear submodule, and `H`-invariance handles
the other factor. Injectivity of `Subrepresentation.toSubmodule` proves the
inverse laws; the order relation is unchanged. Finally,
`OrderIso.complementedLattice_iff` transports the complemented-lattice property
that defines `Representation.IsSemisimpleRepresentation`.

## Actual subrepresentation and quotient

`Langlands.CuspidalSupport.constituent_of_semisimple` takes any field `R`, a
group `G` with a topology, and actual smooth representations
`A D : SmoothRep.{uR, uG, uV} R G`. From semisimplicity of `A.representation`
and `SmoothRep.IsSubquotient D A`, it proves both
`SmoothRep.IsSubrepresentation D A` and `SmoothRep.IsQuotient D A`.
These conclusions provide an actual injective intertwiner `D ⟶ A` and an
actual surjective intertwiner `A ⟶ D`. Only `[Group G] [TopologicalSpace G]`
are required on the group carrier; no continuity of the group operations,
irreducibility, finite dimension, finite length, or admissibility is assumed.

The implementation first uses
`Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule`
to view the ambient representation as a semisimple module over the group
algebra `R[G]`. The published `SmoothRep.isSubquotient_iff_exists` supplies an
intermediate smooth representation `C`, an injection `i : C ⟶ A`, and a
surjection `q : C ⟶ D`. The equivalence
`Representation.IntertwiningMap.equivLinearMapAsModule` turns these into
group-algebra linear maps `j` and `f`.

`IsSemisimpleModule.of_injective` makes the intermediate module semisimple.
The extension property supplies a retraction `r : A → C` of `j`, and the
lifting property supplies a section `s : D → C` of `f`. Evaluating the
resulting linear-map identities gives the left-inverse identities. Thus
`j.comp s` is injective and `f.comp r` is surjective. Converting these maps
back to intertwiners and applying `SmoothRep.ofHom` gives the required smooth
representation morphisms.

## Provenance and scope

The two helper proofs are reused unchanged from Worker 166's shared
constituent proof draft, revision 11. The added closing theorem applies them
directly to the two conjuncts of the published target, with no additional
theorem-valued assumptions. The published statement pair and its imports
are unchanged.

These are internal algebraic deductions from the published representation
and smooth-category definitions and the pinned Mathlib semisimple-module
theory. Their motivating application is Bernstein and Zelevinsky,
*Representations of the group GL(n,F) where F is a non-Archimedean local
field*, Russian Mathematical Surveys 31:3 (1976), 1–68, section 3.30(2),
printed page 37 (registered source
`bernstein-zelevinsky-1976-representations-gln`, SHA-256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`).

The module implements the scalar-center extension and final extraction steps
in that case, in the generality of the published target. Finite-index ascent
from the join to the full group, reduction to a cuspidal summand, and the
general central-action argument remain separate. This module does not prove
`Langlands.CuspidalSupport.LeviCuspidalConstituentTheorem` or assert that an
arbitrary admissible representation is semisimple.
