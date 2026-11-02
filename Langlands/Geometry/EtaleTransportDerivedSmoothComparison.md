# Derived smooth sections and their natural algebraic comparison

Author: Worker 13.

This internal construction compares the actual derived smooth global sections
of a transport module sheaf with its derived algebraic global sections. The
inputs are `Y : Scheme.{u}`, a topological group `G : Type w` with
`IsTopologicalGroup G`, the action `ρ : G →* (Aut Y)ᵐᵒᵖ`, an explicit
`Small.{u} G` assumption, and a commutative ring `R : Type u`. The scheme and
group universes are independent; all module and representation carriers lie
in universe `u`. The source is `ModuleSheaf.{u,w,u,u} ρ R`, the existing
algebraic module-sheaf category on the labelled scheme small-etale transport
site. Its local actions are not required to satisfy a continuity condition.

Write `A = sectionRepresentation ρ R`,
`S = SmoothSections.sections ρ R`, and
`U = SmoothRep.toRep : SmoothRep R G ⥤ Rep R G`.
The actual functor `S` is `A` followed by the smooth-part functor. Its
sections are those fixed by some open subgroup under the labelled
whole-scheme action. `SmoothSections.inclusion` is the constructed natural
map `ι : S ⋙ U ⟶ A`, given by inclusion of smooth vectors. The functor `U`
is exact: `HyperextScalarExtension` supplies its homology-preservation
instance because smooth representations are closed under kernels and
cokernels. The local finite-colimit-preservation instance follows from that
result; finite-limit preservation is already available. This uses exact
forgetting of smoothness, without any exactness hypothesis on smoothing.

For `q : ℕ`, `cohomologyForgetIso q` is the natural isomorphism

`S.rightDerived q ⋙ U ≅ (S ⋙ U).rightDerived q`.

It applies `DerivedComparison.rightDerivedCompIso` to the identity source
functor and the inverse left unitor. The identity source is exact and
preserves injectives. Composing its result with the left unitor gives the
displayed target. `cohomologyMap q` then composes this isomorphism with
`NatTrans.rightDerived ι q` to obtain a natural map from forgotten smooth
section cohomology to algebraic section cohomology. For every genuine
transport-sheaf injective resolution `I` of `F`, `cohomologyMap_app I q`
computes it as `cohomologyForgetIso.hom`, followed by the standard
resolution-cohomology comparison for `S ⋙ U`, the homology map of the
termwise inclusion on `I`, and the inverse comparison for `A`.

The bounded-below constructions use independent Mathlib
`HasDerivedCategory` localization choices for transport sheaves, smooth
representations and algebraic representations. These are categorical
availability hypotheses with standard realizations. Only comparisons that
use the actual derived smooth representation object require the smooth
representation localization.

`algebraicSmoothDerivedSections` is the actual right derived complex of
`S ⋙ U`, applied to a transport sheaf placed in degree zero, with values in
`DerivedCategory.Plus (Rep R G)`. Exactness of `U` gives `derivedForgetIso`:
forgetting the actual derived smooth representation object agrees with
this algebraic model after both are included in the unbounded derived
category of algebraic representations. This is the specialization of
`DerivedPlus.derivedPostcompIso S U`; it is computed using the same
transport-sheaf injective resolutions on both sides.

`inclusionSquare` presents `ι` as a square
`S ⋙ U ⟶ identity ⋙ A` using the inverse left unitor.
`algebraicDerivedMap` applies `DerivedPlusSource.derivedMap` to this square
and removes the identity source by the left unitor. It is a natural map
from `algebraicSmoothDerivedSections` to
`DerivedSections.derivedSections`, both valued in the actual bounded-below
derived category of algebraic representations. `algebraicDerivedMap_app`
states that every injective resolution computes its component: use the
resolution comparison for `S ⋙ U`, localize the extended termwise square,
and use the inverse comparison for `A` on the identity-mapped resolution.
`algebraicDerivedMap_homology` gives the corresponding nonnegative homology
formula with the resolution-cohomology comparisons on both sides.

`algebraicDerivedMap_homology_classical` proves that the induced homology
map agrees with `NatTrans.rightDerived ι q` under the natural homology
identifications. The implementation compares the identity-mapped
resolution with the original resolution by the canonical identity-functor
complex isomorphism. Its augmentation compatibility is proved in degree
zero. Naturality of the resolution-cohomology comparison then replaces the
identity-mapped target resolution by the original one. Composing the
resolution square with this complex map is the termwise map induced by
`ι`; functoriality of homology and Mathlib's formula for right-derived
natural transformations give the equality.

`algebraicHomologyNatIso q` naturally identifies homology of the algebraic
model with `DerivedSmoothSections.cohomology ρ R q ⋙ U` by composing the
generic derived/classical homology comparison with
`cohomologyForgetIso.symm`. The equation
`algebraicDerivedMap_homologyMap` consequently states that the actual
bounded-below comparison induces exactly `cohomologyMap q` under this
identification and `DerivedSections.homologyNatIso` on the target. Its
proof uses the previous classical agreement and cancels the forgetting
isomorphism with its inverse.

`derivedMap` composes `derivedForgetIso.hom` with
`algebraicDerivedMap` after inclusion in the unbounded derived category.
Its source is the actual derived smooth representation object, included
in the unbounded smooth representation category and then mapped by
`U.mapDerivedCategory`; its target is the actual algebraic derived section
object included in the unbounded algebraic representation category.
`diagramDerivedMap` whiskers this natural map by any coefficient-sheaf
diagram, allowing independent indexing object and morphism universes.
It forms no inverse limit.

The provenance is internal categorical assembly from the actual section
inclusion and the established exact forgetting functor. Classical
comparison uses `DerivedComparison` and Mathlib's right-derived natural
transformations. The actual derived objects and their natural homology
identifications use `DerivedPlus` and `DerivedPlusNaturality`; the
resolution-square map uses `DerivedPlusSource`, and exact target
postcomposition uses `DerivedExactPostcomposition`. All maps are built
from actual sheaf functors, injective resolutions, extension by zero and
localization. No new assertion is attributed to Harris or Berkovich.

This is a comparison map; it is not asserted to be an isomorphism. There
is no identification of smooth cohomology with the smooth part of
algebraic cohomology, no exactness of smoothing, and no claim that
smoothing preserves quasi-isomorphisms. The full smooth equivariant
small-etale sheaf category, compact supports, analytic uniformization,
arithmetic coefficient systems, level towers and Harris specialization
remain separate obligations.
