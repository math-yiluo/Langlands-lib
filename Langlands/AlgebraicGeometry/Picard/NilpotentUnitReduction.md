# Actual unit sheaves and nilpotent reduction

This module constructs actual abelian-group sheaves of units and proves local
surjectivity of unit reduction for closed immersions with nilpotent kernel.
All declarations are in
`Langlands.AlgebraicGeometry.Picard.NilpotentUnitReduction`.

For commutative rings `R : Type u` and `S : Type v`, a surjective ring map
`f : R →+* S`, and `IsNilpotent (RingHom.ker f)`,
`unitsMap_surjective` proves surjectivity of
`Units.map f.toMonoidHom : Rˣ →* Sˣ`. It chooses a lift `r` of the
value of the target unit, transports its invertibility across
`f.quotientKerEquivOfSurjective`, and applies
`IsNilpotent.isUnit_quotient_mk_iff` to show that `r` is a unit.
The resulting unit maps to the original target unit because their values agree.

`ringUnitsFunctor : CommRingCat.{u} ⥤ AddCommGrpCat.{u}` is the composite of the multiplicative-monoid
forgetful functor, the units functor, and the equivalence from commutative
groups to additive commutative groups. Each preserves limits, so their
composite preserves the sheaf condition.
For `X : TopCat.{u}` and `F : X.Presheaf CommRingCat.{u}`,
`unitsPresheaf F` is their composite with `F`; its group over `U` is
`Additive ((F.obj U)ˣ)`. Its restriction maps are the induced actual unit maps.
`unitsPresheaf_isSheaf` proves the sheaf condition from that of `F` using
`CategoryTheory.Presheaf.isSheaf_comp_of_isSheaf`.
`unitsSheaf F hF` bundles the presheaf and its sheaf proof.
For a natural transformation of ring sheaves `η : F ⟶ G`,
`unitsSheafMap η hF hG` has components induced by `Units.map` applied to
the actual ring maps `η.app U`. Additive notation changes the notation
for the group operation, not the sections or their maps.

For `X Y : Scheme.{u}` and any morphism `i : Y ⟶ X`,
`unitsReduction i` is the map induced
by the actual structure-ring natural transformation `i.c`, with target the
units of the actual pushforward structure sheaf. On an open `U`, its
underlying multiplicative map is
`Units.map (i.app U).hom.toMonoidHom`, with codomain
`Γ(Y, i ⁻¹ᵁ U)ˣ`.

Now assume `[IsClosedImmersion i]` and `hi : IsNilpotent i.ker`.
Here `i.ker` is Mathlib's ideal-sheaf data and nilpotence means that a
single exponent makes its power zero. `nilpotentKernel_app i hi U hU`
uses `Scheme.Hom.ker_apply` and `IdealSheafData.ideal_pow` to show that
`RingHom.ker (i.app U).hom` is nilpotent for every affine open `U`.
Closed immersions are quasi-compact, as required by the kernel API.
`Scheme.Hom.app_surjective` supplies surjectivity of the actual ring map
on `U`; the ring lemma therefore gives `unitsReduction_app_surjective`.

`unitsReduction_isLocallySurjective i hi` proves local surjectivity on
every open: for a target unit section on `U` and a point `x ∈ U`, choose
an affine neighbourhood `x ∈ V ⊆ U` and lift the restricted section on
`V`. Finally `unitsReduction_epi i hi` uses
`CategoryTheory.Sheaf.epi_of_isLocallySurjective` to obtain an epimorphism
of the actual abelian-group sheaves.

This is derived infrastructure for the square-zero deformation sequence
in Oort, *Sur le schéma de Picard* (1962), §6 Lemma 3 and proof, printed
pp.6–7/PDF pp.7–8, registered as `oort-1962-sur-le-schema-de-picard`,
SHA-256 `1322c0cfac1bdd6163122345c60f9a57c5778cc23e6091227a4357678c5a2d30`.
Oort's lemma gives the additive description of the square-zero unit kernel
and restriction compatibility. This module supplies a separate derived
input for the surrounding deformation sequence: local surjectivity of
actual unit reduction. The extension from square-zero to nilpotent
kernels uses Mathlib's nilpotent-ideal induction. The sheaf construction
and affine-neighbourhood proof are supplied here.

No splitting, field, reducedness, properness or projectivity assumption is
used. The surjectivity on affine opens and local surjectivity do not assert
surjectivity on arbitrary nonaffine opens or on global sections.
The module does not identify the unit kernel with an ideal sheaf, classify
line-bundle deformations, compare cohomology, or prove Picard representability.
