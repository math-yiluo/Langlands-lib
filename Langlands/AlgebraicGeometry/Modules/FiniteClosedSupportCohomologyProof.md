# Cohomology and zero detection for scheme modules with finite closed support: proof

Author: Worker 716.

`Langlands.AlgebraicGeometry.Modules.finiteClosedSupportCohomology` proves the Library
proposition
`Langlands.AlgebraicGeometry.Modules.FiniteClosedSupportCohomologyStatement.{u}` from
`Langlands.AlgebraicGeometry.Modules.FiniteClosedSupportCohomologyStatement`, for every
universe `u`. The theorem's type is exactly that proposition, with no further parameters
or hypotheses.

The proved assertion is the statement's exact scope. Let `X : Scheme.{u}` and
`M : X.Modules`, and assume `HasFiniteClosedSupport M`: the stalk support
`stalkSupport M` (the points where the abelian stalk of `M.presheaf` is not a zero
object) is finite and each of its points is closed. Then

1. `(DerivedSections.cohomology X (n + 1)).obj M` is a zero object for every `n : ℕ`;
2. `(DerivedSections.globalSections X).obj M` is a zero object if and only if `M` is a
   zero object of `X.Modules`;
3. for every `R : CommRingCat.{u}` and every `f : X ⟶ Spec R`,
   `(DerivedSections.relativeCohomology f (n + 1)).obj M` is a zero object for every
   `n`, and `(DerivedSections.relativeGlobalSections f).obj M` is a zero object if and
   only if `M` is.

No coherence, quasi-coherence, finite-generation, noetherian, separation, properness,
smoothness or flatness hypothesis is used. The empty scheme, the empty support and every
`R` and `f` are included. The result detects the zero module by its global sections; it
does not say that modules with finite closed support are zero.

## Proof inputs

The proof uses two published theorems. It does not repeat their arguments.

- `Langlands.Cohomology.finiteClosedSupportSheaf :
  Langlands.Cohomology.FiniteClosedSupportSheafStatement.{u}`, from
  `Langlands.Cohomology.FiniteClosedSupportSheafProof`. For an abelian sheaf `F` on a
  topological space `X` and a finite set `S` of closed points outside which all stalks of
  `F.obj` are zero, it gives `TopCat.Presheaf.IsFlasque F.obj` and
  `IsZero (F.obj.obj (op ⊤)) ↔ IsZero F`.
- `Langlands.AlgebraicGeometry.Modules.PushforwardInjectiveAcyclic.isZero_cohomology_succ_of_isFlasque`,
  from `Langlands.AlgebraicGeometry.Modules.PushforwardInjectiveAcyclicProof`. For
  `F : X.Modules` with an instance `TopCat.Presheaf.IsFlasque F.presheaf`, it gives
  `IsZero ((DerivedSections.cohomology X (n + 1)).obj F)` for every `n`.

It also uses `isZero_iff_forall_isZero_stalk` from
`Langlands.AlgebraicGeometry.Modules.ModuleSupport` and the comparison isomorphisms
`DerivedSections.relativeCohomologyRestrictScalarsIso` and
`DerivedSections.relativeGlobalSectionsIso` from
`Langlands.AlgebraicGeometry.Modules.DerivedSections`.

## The implemented proof

The helper lemmas are in the namespace
`Langlands.AlgebraicGeometry.Modules.FiniteClosedSupportCohomology`.

1. `toSheaf_finiteClosedSupport`: given `h : HasFiniteClosedSupport M`, the published
   sheaf theorem is applied to the space `X.toTopCat`, the abelian sheaf
   `(SheafOfModules.toSheaf X.ringCatSheaf).obj M` and `S := stalkSupport M`. The
   underlying presheaf of this abelian sheaf is `M.presheaf` by definition, so the
   hypotheses and conclusions are stated for `M.presheaf`. The two components of `h`
   give finiteness of `S` and closedness of its singletons. A point outside `S` has
   `¬¬ IsZero` stalk by the definition of `stalkSupport`, and `not_not` turns this into
   a zero stalk. The lemma returns flasqueness of `M.presheaf` and the equivalence
   `IsZero (M.presheaf.obj (op ⊤)) ↔ IsZero ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)`.

2. `isFlasque`: the first component of step 1.

3. `isZero_iff_isZero_toSheaf`: `IsZero M` holds exactly when the underlying abelian
   sheaf is a zero object. Both sides are equivalent to the vanishing of every abelian
   stalk of `M.presheaf`: the left side by `isZero_iff_forall_isZero_stalk` from
   `ModuleSupport`, and the right side by Mathlib's
   `TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero`.

4. `isZero_globalSections_iff`: the module `(DerivedSections.globalSections X).obj M`,
   which is `SheafOfModules.evaluation X.ringCatSheaf (op ⊤)` applied to `M`, and the
   abelian group `M.presheaf.obj (op ⊤)` have the same underlying type. A module and an
   abelian group are zero objects exactly when they are subsingletons
   (`ModuleCat.isZero_iff_subsingleton`, `AddCommGrpCat.isZero_iff_subsingleton`), so
   one is zero exactly when the other is; after these rewrites the goal closes by `rfl`.

5. `isZero_restrictScalars_iff`: for a ring homomorphism `φ : R →+* S` and an
   `S`-module `N`, `(ModuleCat.restrictScalars φ).obj N` is a zero object exactly when
   `N` is. The restricted module has the same underlying type, so the same subsingleton
   rewrite and `rfl` apply.

6. `isZero_cohomology_succ`: step 2 installs the flasqueness instance for
   `M.presheaf`, and `isZero_cohomology_succ_of_isFlasque n M` gives the vanishing of
   `Hⁿ⁺¹(X, M)`.

7. `isZero_globalSections_iff_isZero`: rewriting with steps 4 and 3 turns the goal into
   the second component of step 1. Both directions of the equivalence come from the
   published sheaf theorem.

The closing theorem `finiteClosedSupportCohomology` introduces `X`, `M` and `h`. The
first two components are steps 6 and 7. For `R` and `f`:

- In degree `n + 1`, step 5 shows that
  `(ModuleCat.restrictScalars (DerivedSections.structureRingHom f).hom).obj
  ((DerivedSections.cohomology X (n + 1)).obj M)` is a zero object, since step 6 says
  the unrestricted module is. The component at `M` of
  `DerivedSections.relativeCohomologyRestrictScalarsIso f (n + 1)` is an isomorphism from
  this module to `(DerivedSections.relativeCohomology f (n + 1)).obj M`, and `IsZero.of_iso`
  transfers the vanishing.
- For global sections, the component at `M` of `DerivedSections.relativeGlobalSectionsIso f`
  identifies `(DerivedSections.relativeGlobalSections f).obj M` with the restriction of
  scalars of `(DerivedSections.globalSections X).obj M` along the same ring map.
  `Iso.isZero_iff`, `Functor.comp_obj` and step 5 reduce the goal to step 7.

## Provenance and scope

The proof is derived and follows the route recorded in the statement's Markdown: apply
the abelian-sheaf result to the sheaf underlying `M` with `S = stalkSupport M`, use the
flasque-module acyclicity theorem in positive degrees, and transfer both assertions to
the affine base by restriction of scalars. The support convention is that of the Stacks
Project, Tag 01AT, as recorded in `ModuleSupport.md`. The proof cites no further source.

Only standard axioms are used: `propext`, `Classical.choice` and `Quot.sound`. The module
imports the statement module and the published modules
`Langlands.AlgebraicGeometry.Modules.PushforwardInjectiveAcyclicProof` and
`Langlands.Cohomology.FiniteClosedSupportSheafProof`; it changes no existing Library file.

This module proves no Leray comparison, no finite-support property of higher direct
images along other morphisms, and no base-change assertion.
