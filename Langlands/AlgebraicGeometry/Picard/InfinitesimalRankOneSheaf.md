# Associated sheaves of patched free rank-one modules

This internal construction takes commutative rings `R`, `A`, `B`, and `C`
in an arbitrary common universe `u`, actual `R`-algebra structures on `A`
and `B`, ring maps `a : A → C` and `b : B → C`, and a categorical pullback
square whose projections are the two algebra maps. For a specified unit
`c : Cˣ`, the published `InfinitesimalRankOnePatching.patchedModule` is the
actual `R`-submodule of `A × B` defined by `a(x) = c * b(y)`.

## Actual sheaf and pullback constructions

`patchedSheaf` is the associated module sheaf of this pair module on `Spec R`.
It does not depend on a unit lift. If an actual `v : Bˣ` maps to `c`, the
published module frame sends `r` to `(algebraMap R A r,
v⁻¹ * algebraMap R B r)`. Applying the associated-sheaf functor to the inverse
frame gives `frameIso`, an actual isomorphism to the structure sheaf.
`patchedLineBundle` packages that same sheaf with its local rank-one property.

`framePullbackIso` pulls the frame back using the ordinary scheme-module
pullback along any affine morphism and composes with the published canonical
structure-sheaf comparison `pullbackUnitIso`. `firstPullbackIso` specializes
this construction to `Spec A → Spec R`. `secondPullbackIso` specializes it to
`Spec B → Spec R` and then multiplies by `v⁻¹`. `inverseUnitIso` constructs
that multiplication isomorphism by applying the associated-sheaf functor to
the actual linear equivalence given by multiplication by the inverse unit.

The all-open formulas `firstPullbackIso_adjoint_toOpen` and
`secondPullbackIso_adjoint_toOpen` describe the adjoints of these ordinary
pullback maps. On every open `U` of `Spec R`, the generator of an actual pair
`z` maps to the structure-sheaf generator of `z.val.1` or `z.val.2`,
respectively, on the inverse-image open. These identities identify the actual
coordinate projections, including the chosen orientation of the multiplier.

## Uniqueness and prescribed maps

`firstPullbackIso_unique` and `secondPullbackIso_unique` state that these
adjoint formulas on global generators determine each isomorphism uniquely.
The corresponding `independent` lemmas identify the isomorphisms obtained
from any two unit lifts of the same `c`. The global frame itself is allowed
to depend on its lift; the coordinate pullback isomorphisms are independent.

For `c`, `d`, and compatible scalars `x : A`, `y : B` satisfying
`a(x) * c = d * b(y)`, `diagonalSheafMap` is the associated sheaf of the
published componentwise map `(z₁,z₂) ↦ (x*z₁,y*z₂)`. The all-open generator
formula retains this actual pair map. `affineScalarHom` is the affine
structure-sheaf morphism induced by multiplication by its specified ring
element, with its own all-open generator formula. The two
`diagonalSheafMap` naturality lemmas are equalities of actual sheaf morphisms:
pulling back the diagonal map and applying the target coordinate
trivialization equals the source coordinate trivialization followed by
multiplication by `x` or `y`. Compatible unit multipliers give the actual
isomorphism `diagonalSheafIso`; both naturality identities are also stated
for its underlying morphism.

`exists_lineBundle_and_pullbackIsos` assumes surjectivity of `b` and nilpotence
of its actual kernel ideal. For every specified `c`, it proves the local
rank-one property of `patchedSheaf` and supplies both ordinary pullback
isomorphisms with the coordinate identities on every open. Surjectivity and
nilpotence are used only to obtain a unit lift. The other constructions and
identities require only the stated pullback square and actual lift.

## Implemented proof and provenance

This is derived internal content, with no additional literature theorem used.
The input module, its frame and its diagonal maps are the published
`InfinitesimalRankOnePatching` constructions. The associated-sheaf functor,
its generator naturality, and `tildeSelf` are Mathlib constructions.
`tildePullback_hom_ext` from `TildePullback` determines ordinary pullback maps from
their adjoints on global generators. `pullbackUnitAdjunction` from `PullbackUnitProofs`
and Mathlib's `StructureSheaf.toOpen_comp_comap` compute the pulled-back frame
on every open. Applying each coordinate to the module-frame inverse identity
then proves the two coordinate formulas. Extensionality proves uniqueness
and independence. Adjunction naturality, the diagonal generator formula, and
coordinate evaluation prove the morphism identities; unit versions specialize
those identities. Finally the published
`NilpotentUnitReduction.unitsMap_surjective` supplies the lift for the
existence theorem. The construction imports no scalar-extension prerequisite.

## Remaining geometric obligations

This provides sheaves and ordinary leg pullback isomorphisms for patched free
rank-one modules with a lifted overlap unit. Coherence of the two iterated
ordinary pullbacks over `Spec C`, general line-bundle patching, the equivalence
of actual Picard groupoids, and the augmented pointed deformation comparison
remain separate obligations. This result does not prove representability of
the actual fppf Picard sheaf.
