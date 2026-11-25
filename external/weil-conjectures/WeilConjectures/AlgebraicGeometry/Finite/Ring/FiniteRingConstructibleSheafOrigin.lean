/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

/-!
# Constructible finite-ring sheaves have etale origin

Source: Stacks Project, Tags 09AK and 099Y, with the blueprint's global finite partitions
(blueprint: lem-weil-pbc-finite-ring-constructible-sheaf-origin).

The two recorded constructibility predicates use different equivalent encodings of
constant-coefficient module sheaves. The equivalence below is identified with the
recorded comparison pullback on underlying additive sheaves, and the last clause
requires that identification to respect the constant scalar action. Thus it specifies
the given pullback, including its module structure.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- The comparison pullback induces the equivalence of constructible module sheaves.
The finite ring is allowed to be zero and the scheme is arbitrary, including empty.
The natural isomorphism identifies the equivalence with `comparisonUpperStar`;
its constant-scalar compatibility makes this an identification of module sheaves.
Source: Stacks Project, Tag 09AK, lemma-compare-constructible, and Tag 099Y,
lemma-compare-locally-constant, with global finite partitions as in the blueprint
(blueprint: lem-weil-pbc-finite-ring-constructible-sheaf-origin).

Proof: restrict the intrinsic module sheaf to the constant scalars. Module
sheafification makes this an equivalence with fixed-module-valued sheaves. It
preserves the underlying additive sheaf and identifies local constancy, finite
geometric stalks, and canonical pullback. Thus it identifies the two pro-etale
constructibility predicates, with the same finite global strata. On the etale side
use the existing comparison of the two constructibility predicates. The existing
fixed-module constructible-origin theorem supplies essential surjectivity, while
full faithfulness of comparison pullback supplies full faithfulness. Restrict these
functors to the constructible full subcategories and take the resulting equivalence.
Its additive comparison is the inverse encoding counit. This counit is linear over
the original constant ring, so its sectionwise linearity is exactly the asserted
constant-scalar formula. Empty schemes, empty strata and the zero ring are included;
no affine-local constructibility criterion replaces the global partition.
-/
theorem finiteRing_constructibleSheaf_origin (T : Scheme.{u})
    (B : Type u) [CommRing B] [Finite B] :
    ∃ e :
      ObjectProperty.FullSubcategory (IsConstructibleEtaleModuleSheaf (T := T)
        (Λ := ULift.{u + 1, u} B)) ≌
      ObjectProperty.FullSubcategory (IsConstructibleProEtaleModuleSheaf T B),
    ∃ α :
      ObjectProperty.ι (IsConstructibleEtaleModuleSheaf (T := T)
          (Λ := ULift.{u + 1, u} B)) ⋙
        ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) T ⋙
        sheafCompose (ProEt.topology T)
          (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) AddCommGrpCat.{u + 1}) ≅
      e.functor ⋙ ObjectProperty.ι (IsConstructibleProEtaleModuleSheaf T B) ⋙
        SheafOfModules.toSheaf
          ((sheafCompose (ProEt.topology T)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing T B)),
    ∀ (G : ObjectProperty.FullSubcategory (IsConstructibleEtaleModuleSheaf (T := T)
        (Λ := ULift.{u + 1, u} B)))
      (U : T.ProEtᵒᵖ) (b : ULift.{u + 1, u} B)
      (m : ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) T).obj G.obj).obj.obj U),
      ((α.hom.app G).hom.app U) (b • m) =
        ((toSheafify (ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{u + 1, u} B)))).app U).hom b •
          (@id ((e.functor.obj G).obj.val.obj U) (((α.hom.app G).hom.app U) m)) := by
  classical
  let E := proEtaleModuleEncoding T B
  let P : ObjectProperty (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) := IsConstructibleEtaleModuleSheaf
  let Q : ObjectProperty (proEtaleRingModules T (proEtaleConstantRing T B)) :=
    IsConstructibleProEtaleModuleSheaf T B
  let L := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) T
  let F := P.ι ⋙ L ⋙ E.inverse
  have hF (G : P.FullSubcategory) : Q (F.obj G) := by
    apply (proEtaleModuleRestriction_constructible_iff T B _).mpr
    have hG := (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf G.obj).mp G.property
    have hL := ProEtale.isConstructible_comparisonUpperStar_obj G.obj
    exact ProEtale.isConstructible_of_iso (E.counitIso.app (L.obj G.obj)).symm hL
  let H := Q.lift F hF
  have : H.EssSurj := ⟨fun M ↦ by
    have hM := (proEtaleModuleRestriction_constructible_iff T B M.obj).mp M.property
    obtain ⟨G, hG, ⟨e⟩⟩ :=
      ProEtale.exists_isConstructibleSheaf_iso_comparisonUpperStar_obj
        (ULift.{u + 1, u} B) hM
    let G' : P.FullSubcategory :=
      ⟨G, (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf G).mpr hG⟩
    exact ⟨G', ⟨Q.isoMk (E.inverse.mapIso e ≪≫ (E.unitIso.app M.obj).symm)⟩⟩⟩
  have : H.IsEquivalence := {}
  let e := H.asEquivalence
  let V := sheafCompose (ProEt.topology T)
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) AddCommGrpCat.{u + 1})
  let α : P.ι ⋙ L ⋙ V ≅ e.functor ⋙ Q.ι ⋙ SheafOfModules.toSheaf _ :=
    Functor.isoWhiskerLeft (P.ι ⋙ L) (Functor.isoWhiskerRight E.counitIso.symm V)
  refine ⟨e, α, ?_⟩
  intro G U b m
  exact ((E.counitIso.inv.app (L.obj G.obj)).hom.app U).hom.map_smul b m

end AlgebraicGeometry.Scheme
