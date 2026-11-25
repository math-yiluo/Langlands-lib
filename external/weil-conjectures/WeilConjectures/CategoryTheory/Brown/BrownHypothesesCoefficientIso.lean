/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Brown.BrownHypothesesDefinitions
import WeilConjectures.CategoryTheory.Brown.BrownHypothesesCriteria
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.CategoryTheory.Brown.BrownHypothesesStructural
import WeilConjectures.CategoryTheory.Triangulated.CompactBoundedHom

/-!
# Coefficient-isomorphism invariance of Brown hypotheses

Source: blueprint latest, sk-lem-brown-hypotheses.proof.md, paragraphs 1--2,
and the coefficient identifications in sk-lem-brown-hypotheses-generation.proof.md.
The proof uses an equivalence of localizing categories and the compact-object
adjunction theorem, independently of the geometric finite-field compactness inputs.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace CategoryTheory

attribute [local instance 30000] brownHypothesesCondensedMonoidal
  brownHypothesesCondensedBraided brownHypothesesSheafMonoidal
  brownHypothesesSheafBraided brownHypothesesCoefficientMonObj
  brownHypothesesModuleMonoidalClosed
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory
attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
  AlgebraicGeometry.ProEtale.CondensedRing.upperStar BrownHypothesesFor

/-- Exact coproduct-preserving functors carry the generating localizing intersection
into the localizing intersection of the image generators. -/
private theorem localizingClosure_map_of_preservesColimits
    {C D : Type v} [Category.{w} C] [Category.{w} D]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    [PreservesColimitsOfSize.{w, w} F]
    (S : ObjectProperty C) (T : ObjectProperty D) (hST : S ≤ T.inverseImage F) :
    localizingClosure S ≤ (localizingClosure T).inverseImage F := by
  intro M hM P hP hTP
  let _ := hP.1
  let _ := hP.2.1
  have hPF : IsLocalizingSubcategory (P.inverseImage F) := by
    refine ⟨inferInstance, inferInstance, ?_⟩
    intro I G hG hGP
    let _ := hG
    have hFG : HasColimit (G ⋙ F) :=
      ⟨F.mapCocone (colimit.cocone G), isColimitOfPreserves F (colimit.isColimit G)⟩
    exact P.prop_of_iso (preservesColimitIso F G).symm (hP.2.2 (G ⋙ F) hFG hGP)
  exact hM _ hPF (fun N hN ↦ hTP _ (hST N hN))

/-- One direction of coefficient transport, with the coefficient instances fixed. -/
private theorem brownHypothesesFor_of_coefficientIso
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [MonObj Λ'] [IsCommMonObj Λ] [IsCommMonObj Λ']
    (e : Mon.mk Λ ≅ Mon.mk Λ') (X : Scheme.{u}) (hB : BrownHypothesesFor Λ' X) :
    BrownHypothesesFor Λ X := by
  let S := constantModelBoundedConstructible Λ X ⊓
    fun K ↦ DerivedCategory.finiteTorAmplitude _ K
  let S' := constantModelBoundedConstructible Λ' X ⊓
    fun K ↦ DerivedCategory.finiteTorAmplitude _ K
  obtain ⟨ht, hi, hr, hs, _, _⟩ := (brownHypothesesFor_iff Λ' X).mp hB
  let q : condensedRingObj Λ X ≅ condensedRingObj Λ' X :=
    (upperStarFromPoint X).mapIso ((Mon.forget _).mapIso e)
  have _ : IsMonHom q.hom :=
    inferInstanceAs (IsMonHom ((upperStarFromPoint X).map e.hom.hom))
  have _ : IsMonHom q.inv :=
    inferInstanceAs (IsMonHom ((upperStarFromPoint X).map e.inv.hom))
  let H : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) ≌
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X) :=
    Equivalence.mk (Mod.comap q.inv) (Mod.comap q.hom)
      ((Mod.comapId _).symm ≪≫ Mod.comapCongr q.hom_inv_id.symm ≪≫
        Mod.comapComp q.hom q.inv)
      ((Mod.comapComp q.inv q.hom).symm ≪≫ Mod.comapCongr q.inv_hom_id ≪≫ Mod.comapId _)
  have _ : H.functor.Additive :=
    inferInstanceAs ((Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) q.inv).Additive)
  have _ : H.inverse.Additive :=
    inferInstanceAs ((Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) q.hom).Additive)
  let d := H.mapDerivedCategory
  let _ : H.functor.mapDerivedCategory.CommShift ℤ := inferInstance
  let _ : H.functor.mapDerivedCategory.IsTriangulated := inferInstance
  let _ : H.inverse.mapDerivedCategory.CommShift ℤ := inferInstance
  let _ : H.inverse.mapDerivedCategory.IsTriangulated := inferInstance
  have hiS : S.IsClosedUnderIsomorphisms := by
    let _ := (constantModelConstructibleFiniteTor_wellDefined Λ X).2.1
    dsimp only [S]
    infer_instance
  let _ := hiS
  have hp : S'.inverseImage d.functor = S := by
    funext K
    apply propext
    constructor
    · intro hK
      have hInv : S (d.inverse.obj (d.functor.obj K)) :=
        constantModelCtf_coefficientIso e.symm X ⟨d.functor.obj K, hK⟩
      exact S.prop_of_iso (d.unitIso.app K).symm hInv
    · intro hK
      exact constantModelCtf_coefficientIso e X ⟨K, hK⟩
  let _ : S'.IsTriangulated := ht
  let _ : S'.IsClosedUnderIsomorphisms := hi
  let _ : S'.IsStableUnderRetracts := hr
  have htS : S.IsTriangulated := by
    rw [← hp]
    change (S'.inverseImage H.functor.mapDerivedCategory).IsTriangulated
    infer_instance
  have hrS : S.IsStableUnderRetracts := by
    rw [← hp]
    exact ⟨fun r hK ↦ S'.prop_of_retract (r.map d.functor) hK⟩
  have hsS : ObjectProperty.EssentiallySmall.{u + 1} S := by
    obtain ⟨J, hJ, ⟨eJ⟩⟩ := (ObjectProperty.exists_equivalence_iff S').mpr hs
    exact (ObjectProperty.exists_equivalence_iff S).mp
      ⟨J, hJ, ⟨(d.congrFullSubcategory hp).trans eJ⟩⟩
  obtain ⟨_, htri, hiso, _, hcop, _⟩ := brownHypotheses_structural Λ X
  obtain ⟨_, htri', hiso', _, _, _⟩ := brownHypotheses_structural Λ' X
  let _ := htri
  let _ := hiso
  let _ := htri'
  let _ := hiso'
  let _ := hcop
  let L := localizingClosureProEtale Λ X
  let L' := localizingClosureProEtale Λ' X
  have hforward : L ≤ L'.inverseImage d.functor :=
    localizingClosure_map_of_preservesColimits H.functor.mapDerivedCategory S S'
      (fun K hK ↦ constantModelCtf_coefficientIso e X ⟨K, hK⟩)
  have hbackward : L' ≤ L.inverseImage d.inverse :=
    localizingClosure_map_of_preservesColimits H.inverse.mapDerivedCategory S' S
      (fun K hK ↦ constantModelCtf_coefficientIso e.symm X ⟨K, hK⟩)
  have hlocal : L'.inverseImage d.functor = L := by
    funext K
    apply propext
    exact ⟨fun hK ↦ L.prop_of_iso (d.unitIso.app K).symm (hbackward _ hK),
      hforward K⟩
  let dL := d.congrFullSubcategory hlocal
  have _ : dL.functor.Additive :=
    ⟨fun {_ _ f g} ↦ ObjectProperty.hom_ext _
      (H.functor.mapDerivedCategory.map_add (f := f.hom) (g := g.hom))⟩
  have _ : dL.inverse.Additive :=
    ⟨fun {_ _ f g} ↦ ObjectProperty.hom_ext _
      (H.inverse.mapDerivedCategory.map_add (f := f.hom) (g := g.hom))⟩
  have _ : dL.symm.functor.Additive := inferInstanceAs dL.inverse.Additive
  obtain ⟨_, _, _, _, hcop', hc'⟩ := (brownHypothesesFor_iff Λ' X).mp hB
  let _ := hcop'
  apply (brownHypothesesFor_iff Λ X).mpr
  refine ⟨htS, hiS, hrS, hsS, hcop, fun K hK ↦ ?_⟩
  have hc := (isCompactObject_iff_isCompactObj (dL.functor.obj K)).mp
    (hc' _ (constantModelCtf_coefficientIso e X ⟨K.obj, hK⟩))
  exact (isCompactObject_iff_isCompactObj K).mpr
    ((hc.of_adjunction dL.symm.toAdjunction).of_iso (dL.unitIso.app K))

open scoped CategoryTheory.Obj in
/-- Brown's bundle is invariant under isomorphisms of commutative condensed rings.
No admissibility, Noetherian, finite-type, or field hypothesis is required.

Source: blueprint latest, sk-lem-brown-hypotheses.proof.md, paragraphs 1--2,
and sk-lem-brown-hypotheses-generation.proof.md, coefficient identifications.
(blueprint: lem-sfb-brown-coefficient-iso-invariance).

Proof: scalar restriction along the inverse ring isomorphism is an exact monoidal
equivalence. Its derived functor preserves and reflects constructibility, boundedness,
and finite Tor amplitude. Consequently Dctf is the inverse image of Dctf for the other
coefficient. Triangulation and closure under retracts pull back along this functor;
the induced equivalence of full subcategories transports essential smallness.
Compactness transports across the induced equivalence of localizing full subcategories
by the compact-object adjunction theorem. The objectwise Brown
criterion supplies generation and the other structural clauses. Repeat with the inverse
ring isomorphism for the converse. No arbitrary-field compactness assertion is used. -/
theorem brownHypothesesFor_coefficientIso_iff
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [MonObj Λ'] [IsCommMonObj Λ] [IsCommMonObj Λ']
    (e : Mon.mk Λ ≅ Mon.mk Λ') (X : Scheme.{u}) :
    BrownHypothesesFor Λ X ↔ BrownHypothesesFor Λ' X := by
  exact ⟨fun hB ↦ @brownHypothesesFor_of_coefficientIso Λ' Λ _ _ _ _ e.symm X hB,
    fun hB ↦ @brownHypothesesFor_of_coefficientIso Λ Λ' _ _ _ _ e X hB⟩

end CategoryTheory
