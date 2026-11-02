# Renard II.2.1: canonical section-to-germ maps and natural units

Worker 1215 implements the canonical maps and their intrinsic laws. Worker 6
contributed the original-source audit, the focused specification and the
universe-transport design.

The governing original is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, II.2.1, printed p.36 / PDF p.42:
the definition of the canonical map and the following naturality square.
The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
PDF pp.41–43 were read directly. The registered supplementary 2010-edition
*Corrections et compléments*,
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF pp.2–3, were also read, together with the public source-error note
`notes/renard/basis-sheafification-source.md`. The separation error in the
subsequent descent argument is not used in this construction.

`sectionGerms F U` is the actual additive homomorphism from original sections
on the basis open `U` to the published `GermSections F U.obj`. Its dependent
function is literally `fun x => rawGerm F U x.val x.property s`.
`sectionGerms_locallyRepresented` chooses `U` itself and the same original
section as the local witness at every point. That witness represents the
family throughout the whole chosen neighborhood, as the source requires.
`sectionGerms_apply` is the defining pointwise formula. Additivity is checked
pointwise by `rawGerm_zero` and `rawGerm_add`; the zero, addition and negation
formulas, both as sections and at each point, follow from the resulting
additive homomorphism. `sectionGerms_empty` proves every section of any raw
input on an empty basis open maps to zero, the unique empty family. This
proof eliminates a putative domain point and never uses normalization of the
source empty value.

`sectionGerms_restriction` evaluates the two families at each point and uses
the published `rawGerm_restriction`. It proves that restricting the canonical
family on a larger basis open is the canonical family of the original
restricted section. `sectionGerms_map` similarly uses `rawStalkMap_germ`:
applying the actual pointwise stalk map gives the original germs of the
component image section. These formulas establish naturality both in basis
opens and in the source presheaf, without equality detection by germs.

The space universe `u` and original-section universe `v` are independent.
The component additive map may connect carriers in different universes:

```text
sectionGerms :
  {X : Type u} → [TopologicalSpace X] → {B : OpenBasis X} →
  (F : RawPresheaf.{u,v} B) → (U : BasisOpen B) →
  Sections F U →+ GermSections F U.obj
```

An actual natural transformation requires its two functors to have the same
codomain category. The published `rawLiftJoint` and `presheafLiftJoint` supply
that common category, by actual postcomposition with the additive `ULift`
functor at lift level `u`. The full transformation types are:

```text
rawGermSheafLiftUnit :
  {X : Type u} → [TopologicalSpace X] → (B : OpenBasis X) →
  rawLiftJoint.{u,v} B ⟶
    rawGermSheafFunctor.{u,v} B ⋙ sheafForget.{u,max u v} B ⋙
      presheafInclusion.{u,max u v} B

germSheafLiftUnit :
  {X : Type u} → [TopologicalSpace X] → (B : OpenBasis X) →
  presheafLiftJoint.{u,v} B ⟶
    germSheafFunctor.{u,v} B ⋙ sheafForget.{u,max u v} B

germSheafUnit :
  {X : Type u} → [TopologicalSpace X] → (B : OpenBasis X) →
  𝟭 (Presheaf.{u,max u v} B) ⟶
    germSheafFunctor.{u,max u v} B ⋙ sheafForget.{u,max u v} B
```

The raw lifted component first applies `ULift.down` and then `sectionGerms`.
`rawGermSheafLiftUnit_app_app` states this for every lifted input, and its
`_up` and pointwise `_apply` formulas recover the original-section map.
Its restriction and naturality theorems expose the two commuting squares,
including the evaluated morphism formula. The underlying proofs are exactly
`sectionGerms_restriction` and `sectionGerms_map`, since the published lift
restricts and maps sections using the original operations under `ULift`.

`germSheafLiftUnit` wraps those raw components in the existing normalized
full subcategory. `germSheafLiftUnit_app_hom` identifies its erasure with the
raw component. The transformation equation `germSheafLiftUnit_erasure`
compares right whiskering through `presheafInclusion` with left whiskering
the raw unit by the source inclusion, using the hom of the published
`presheafLiftCompInclusionIso.{u,v,u}`. That comparison has identity
components. The normalized evaluation, restriction and naturality theorems
give the same formulas, including the original-section germ formula after
`ULift.up`.

At value universe `max u v`, taking germ sections has that same value
universe. `germSheafUnit` is constructed separately with the identity source:
its component applies `sectionGerms` directly to an unlifted original section.
`germSheafUnit_app_app`, `_apply`, `_restriction`, `_naturality` and
`_naturality_apply` expose this formula and both naturalities.
`germSheafUnit_eq_relift` proves equality of actual natural transformations:
the inverse of `presheafReliftJoint` followed by
`germSheafLiftUnit.{u,max u v}` equals `germSheafUnit.{u,v}`. After erasing
the subcategory wrapper and evaluating on a basis open, this is the
definitional cancellation of `ULift.up` followed by `ULift.down`.

The raw-input extension, actual universe transport and categorical packaging
are internal formalization choices, rather than additional assertions printed
by Renard. The source-normalized specialization retains the original topology
and chosen basis. The construction permits arbitrary raw and normalized
inputs, empty spaces and empty basis opens, including nontrivial raw empty
values and bases without an empty member. It adds no separation, sheaf,
intersection-closure, cardinality or universe-comparison assumption.

Here “unit” names the canonical natural map. Descent, universal factorization,
the Hom equivalence, an adjunction, invertibility on sheaves, support and the
basis/all-open equivalence remain separate results. In particular no
value-lowering functor on arbitrary larger-valued objects is asserted.
