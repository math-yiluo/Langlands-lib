/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Topology.QuasiSeparated
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionQCoh
import WeilConjectures.AlgebraicGeometry.SupportedQCohTriangulated
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.AlgebraicGeometry.DerivedDirectImagePreservesQCoh

/-! # The support triangle for restriction to an open subscheme

Source: Stacks Project, Duality for Schemes, Tag 0E4G, proof of Lemma 48.4.3;
Derived Categories of Schemes, Lemma 36.4.1 and Definition 36.6.1
(blueprint: lem-sc-open-restriction-support-triangle).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Pretriangulated

set_option autoImplicit false
set_option synthInstance.maxSize 2048

namespace AlgebraicGeometry

-- Transport between the scheme-module and sheaf-module category instances is expensive.
/-- Complete the open-restriction unit to a distinguished triangle with quasi-coherent
vertices. Its third vertex has cohomology supported on the closed complement and is
bounded below whenever the first vertex is bounded below.
Source: Stacks Project, Tag 0E4G, proof of Lemma 48.4.3; Lemma 36.4.1 and
Definition 36.6.1 (blueprint: lem-sc-open-restriction-support-triangle).

Proof:
1. Transport the open-immersion restriction/direct-image adjunction along the
   over-site equivalence, then apply the unbounded derived-adjunction construction.
   Direct image preserves K-injective complexes because it is right adjoint to exact
   restriction, and its derived functor is fully faithful.
2. Exact restriction commutes with cohomology and preserves quasi-coherence. The
   compact open inclusion is quasi-compact, and is separated, so its derived direct
   image preserves quasi-coherent cohomology. Apply triangulated closure of supported
   quasi-coherent objects with support set equal to the whole scheme to complete the
   unit to a distinguished triangle whose cone is quasi-coherent.
3. Full faithfulness of derived direct image makes the derived counit invertible.
   The triangle identity makes restriction of the unit invertible. Exact restriction
   preserves distinguished triangles, so the restricted cone is zero. Commutation
   with cohomology and the open-immersion stalk isomorphism show that every stalk of
   every cohomology sheaf of the cone vanishes at a point of V.
4. If K is bounded below, exact restriction preserves its lower bound. Compatibility
   of unbounded and bounded-below right derived functors shows that its derived direct
   image is bounded below. The bounded-below subcategory is triangulated, so the cone
   is bounded below as well. -/
theorem openRestriction_support_triangle (Y : Scheme.{u})
    [CompactSpace Y] [QuasiSeparatedSpace Y] (V : Y.Opens)
    (hV : IsCompact (V : Set Y))
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    (K : schemeDerivedCategory Y) (hK : schemeDerivedQCohProperty Y K) :
    ∃ (adj : (schemeOpenRestriction Y V).mapDerivedCategory ⊣ schemeDerivedDirectImage V.ι)
      (Q : schemeDerivedCategory Y)
      (β : (schemeDerivedDirectImage V.ι).obj
        ((schemeOpenRestriction Y V).mapDerivedCategory.obj K) ⟶ Q)
      (δ : Q ⟶ K⟦(1 : ℤ)⟧),
      Triangle.mk (adj.unit.app K) β δ ∈ distTriang (schemeDerivedCategory Y) ∧
      schemeDerivedQCohProperty Y
        ((schemeDerivedDirectImage V.ι).obj
          ((schemeOpenRestriction Y V).mapDerivedCategory.obj K)) ∧
      schemeDerivedQCohProperty Y Q ∧
      (∀ (n : ℤ) (x : Y), x ∈ V →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) n).obj Q).val.presheaf x))) ∧
      ((∃ a : ℤ, K.IsGE a) → ∃ b : ℤ, Q.IsGE b) := by
  classical
  let L := schemeOpenRestriction Y V
  let R := RingedSpace.moduleDirectImage V.ι.toLRSHom.toShHom
  let a : L ⊣ R := (Scheme.Modules.restrictAdjunction V.ι).ofNatIsoLeft
    (Scheme.Modules.overFunctorEquiv V).symm
  let adj := a.mapDerivedCategoryRightDerivedAdjunction
  have : R.PreservesKInjectiveComplexes := a.preservesKInjectiveComplexes
  have : R.Full := (Scheme.Modules.restrictAdjunction V.ι).fullyFaithfulROfIsIsoCounit.full
  have : R.Faithful :=
    (Scheme.Modules.restrictAdjunction V.ι).fullyFaithfulROfIsIsoCounit.faithful
  have hLK : schemeDerivedQCohProperty V.toScheme (L.mapDerivedCategory.obj K) := by
    apply (schemeDerivedQCoh_openRestriction_iff Y V K).mpr
    intro n
    have := hK n
    exact SheafOfModules.isQuasicoherent_over _ V
  have : CompactSpace V := isCompact_iff_compactSpace.mp hV
  have : QuasiCompact V.ι := quasiCompact_of_compactSpace V.ι
  have hM := schemeDerivedDirectImage_preserves_QCoh V.ι _ hLK
  let P := supportedProperty Y Set.univ
  have : P.IsTriangulated := supported_qcoh_isTriangulated Y Set.univ
  have hPK : P K := ⟨hK, by simp⟩
  have hPM : P (R.rightDerivedFunctor.obj (L.mapDerivedCategory.obj K)) :=
    ⟨hM, by simp⟩
  obtain ⟨Q, hQ, β, δ, hT⟩ := P.distinguished_cocone_triangle (adj.unit.app K) hPK hPM
  refine ⟨adj, Q, β, δ, hT, hM, hQ.1, ?_, ?_⟩
  · have hLQ : IsZero (L.mapDerivedCategory.obj Q) := by
      have : IsIso adj.counit := adj.counit_isIso_of_R_fully_faithful
      have : IsIso (L.mapDerivedCategory.map (adj.unit.app K)) :=
        isIso_of_comp_hom_eq_id _ (adj.left_triangle_components K)
      let T := Triangle.mk (adj.unit.app K) β δ
      exact Triangle.isZero₃_of_isIso₁
        (L.mapDerivedCategory.mapTriangle.obj T)
        (L.mapDerivedCategory.map_distinguished T hT) (by
          change IsIso (L.mapDerivedCategory.map (adj.unit.app K))
          infer_instance)
    intro n x hx
    let H := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) n).obj Q
    have hLH : IsZero (L.obj H) := by
      exact ((DerivedCategory.homologyFunctor _ n).map_isZero hLQ).of_iso
        ((L.mapDerivedCategoryHomologyFunctorIso n).app Q)
    let e : L.obj H ≅ (Scheme.Modules.restrictFunctor V.ι).obj H :=
      (Scheme.Modules.overFunctorEquiv V).app H
    have hRH := hLH.of_iso e.symm
    let F := Scheme.Modules.toPresheaf V.toScheme ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (⟨x, hx⟩ : V)
    have : (Scheme.Modules.toPresheaf V.toScheme).Additive :=
      ⟨by intros; rfl⟩
    have : F.Additive := by dsimp [F]; infer_instance
    have hz := F.map_isZero hRH
    let eStalk := (Scheme.Modules.restrictStalkNatIso V.ι (⟨x, hx⟩ : V)).app H
    exact AddCommGrpCat.subsingleton_of_isZero (hz.of_iso eStalk.symm)
  · rintro ⟨a, ha⟩
    have := ha
    have hLa := L.isGE_mapDerivedCategory_obj K a
    let E : DerivedCategory.Plus
        (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace)) :=
      ⟨L.mapDerivedCategory.obj K, a, hLa⟩
    have hRM : ∃ b : ℤ, (R.rightDerivedFunctor.obj E.obj).IsGE b := by
      obtain ⟨b, hb⟩ := (R.rightDerivedFunctorPlus.obj E).property
      have hs : DerivedCategory.TStructure.t.IsGE
          ((R.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).obj E) b := hb
      exact ⟨b, DerivedCategory.TStructure.t.isGE_of_iso
        (R.rightDerivedFunctorPlusCompatibility.app E) b⟩
    exact (DerivedCategory.TStructure.t.plus).ext_of_isTriangulatedClosed₃ _ hT
      ⟨a, ha⟩ hRM

end AlgebraicGeometry
