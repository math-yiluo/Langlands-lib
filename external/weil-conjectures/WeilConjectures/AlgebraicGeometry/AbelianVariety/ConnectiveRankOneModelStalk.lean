/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
import WeilConjectures.AlgebraicGeometry.PerfectAffineMapRepresentative
import WeilConjectures.AlgebraicGeometry.AbelianVariety.RankOneResidueStalkComponent
import Mathlib.Algebra.Category.Grp.EpiMono

/-! # The local stalk calculation for a connective rank-one model

Source: Stacks Project, Tag 0E62, local argument; Tag 0BCD.
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private theorem strictlyPerfect_single_restricted_unit (S : Scheme.{u}) (U : S.Opens) :
    Scheme.IsStrictlyPerfect S U
      ((CochainComplex.singleFunctor
        (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) 0).obj
          ((SheafOfModules.overFunctor.{u}
            (moduleRings S.toRingedSpace) U).obj (SheafOfModules.unit S.ringCatSheaf))) := by
  classical
  let R := (moduleRings S.toRingedSpace).over U
  let M := (SheafOfModules.overFunctor.{u}
    (moduleRings S.toRingedSpace) U).obj (SheafOfModules.unit S.ringCatSheaf)
  let A := (CochainComplex.singleFunctor (SheafOfModules.{u} R) 0).obj M
  refine ⟨⟨0, 0, fun n hn ↦ ?_⟩, ?_⟩
  · exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  · intro n
    by_cases hn : n = 0
    · subst n
      let e : A.X 0 ≅ SheafOfModules.free (R := R) (ULift.{u} (Fin 1)) :=
        HomologicalComplex.singleObjXSelf (.up ℤ) 0 M ≪≫
          (coproductUniqueIso (fun _ : ULift.{u} (Fin 1) ↦ SheafOfModules.unit R)).symm
      exact ⟨1, e.hom, e.inv, e.hom_inv_id⟩
    · have hz : IsZero (A.X n) :=
        HomologicalComplex.isZero_single_obj_X _ _ _ _ hn
      exact ⟨0, 0, 0, by simpa using (hz.eq_of_src (0 : A.X n ⟶ A.X n) (𝟙 _))⟩

private theorem epi_homologyMap_of_epi_component_zero_outgoing
    {A B : CochainComplex AddCommGrpCat.{u} ℤ} (α : A ⟶ B)
    (hA : IsZero (A.X 1)) [Epi (α.f 0)] :
    Epi (HomologicalComplex.homologyMap α 0) := by
  have hdA : A.d 0 1 = 0 := hA.eq_of_tgt _ _
  have hdB : B.d 0 1 = 0 := by
    apply (cancel_epi (α.f 0)).mp
    rw [α.comm 0 1, hdA, zero_comp, comp_zero]
  have : IsIso (A.iCycles 0) := A.isIso_iCycles 0 1 (by simp) hdA
  have : IsIso (B.iCycles 0) := B.isIso_iCycles 0 1 (by simp) hdB
  have hc : Epi (HomologicalComplex.cyclesMap α 0 ≫ B.iCycles 0) := by
    rw [HomologicalComplex.cyclesMap_i]
    infer_instance
  have : Epi (HomologicalComplex.cyclesMap α 0) :=
    (epi_comp_iff_of_isIso _ _).mp hc
  apply ShortComplex.epi_homologyMap_of_epi_cyclesMap'
  change Epi (HomologicalComplex.cyclesMap α 0)
  infer_instance

private theorem epi_map_of_natIso {C : Type*} [Category C]
    {F G : C ⥤ AddCommGrpCat.{u}} (t : F ≅ G) {X Y : C} (f : X ⟶ Y)
    [Epi (G.map f)] : Epi (F.map f) := by
  have hfac : F.map f = (t.app X).hom ≫ G.map f ≫ (t.app Y).inv := by
    apply (cancel_mono (t.app Y).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact t.hom.naturality f
  rw [hfac]
  infer_instance

-- The composed homology/stalk functors require substantial definitional-equality checking.
/-- The local unit calculation for an already supplied strictly perfect representative.
Source: Stacks Project, Tag 0E62, local argument, and Tag 0BCD.
(blueprint: lem-sc-connective-rank-one-model-stalk).

Proof: Restrict the structure-sheaf single complex and the given arrow to U. The
restriction of the source is the single structure-sheaf complex on the localized site.
It is strictly perfect. Conjugate the restricted arrow by that identification and e,
and apply perfect_affine_map_representative to obtain a chain map into P. Take stalks
at s; the degree-zero source and target are free of rank one. Since P has zero negative
terms, its residue H^0 is the kernel of its outgoing degree-zero differential, with
no quotient by incoming boundaries. The assumed residue H^0 isomorphism implies that
the degree-zero chain-map component has nonzero residue: it sends the generator to a
nonzero element of the rank-one residue term. Its coefficient in the local ring is
therefore a unit. The chain-map equation says that the outgoing differential composed
with this invertible degree-zero component is zero, so the outgoing differential at
the stalk is zero. There are no incoming boundaries. Every degree-zero cohomology germ
is consequently a vector in P^0_s, and the inverse unit gives a source preimage.
Restriction preserves the stalk at a point of U. Exactness of stalks identifies stalks
of cohomology with cohomology of the stalk complex. Naturality of these identifications
and the representing equality Q.map α = f transport each preimage back along e to the
original H^0(a)_s. Higher terms and all other fibres are unrestricted. -/
theorem surjective_stalk_homology_of_connective_rank_one_model (S : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [∀ U : S.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    [∀ x : S, HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (S.residueField x)).toRingedSpace))]
    (E : schemeDerivedCategory S)
    (a : (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj
        (SheafOfModules.unit S.ringCatSheaf) ⟶ E) (s : S)
    (U : S.Opens) (hs : s ∈ U) (hU : IsAffineOpen U)
    (P : CochainComplex
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) ℤ)
    (hP : Scheme.IsStrictlyPerfect S U P)
    (hnegative : ∀ i : ℤ, i < 0 → IsZero (P.X i))
    (hzero : Nonempty (P.X 0 ≅ SheafOfModules.free
      (R := (moduleRings S.toRingedSpace).over U) (ULift.{u} (Fin 1))))
    (e : (SheafOfModules.overFunctor.{u}
      (moduleRings S.toRingedSpace) U).mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj P)
    (ha : IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (S.residueField s)).toRingedSpace)) 0).map
        ((derivedPullback (S.fromSpecResidueField s)).map a))) :
    Function.Surjective (Scheme.Modules.Hom.stalkLinearMap
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).map a) s) := by
  let r := SheafOfModules.overFunctor.{u} (moduleRings S.toRingedSpace) U
  let M := SheafOfModules.unit S.ringCatSheaf
  let A := (CochainComplex.singleFunctor
    (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) 0).obj (r.obj M)
  let c : r.mapDerivedCategory.obj ((DerivedCategory.singleFunctor _ 0).obj M) ≅
      DerivedCategory.Q.obj A :=
    (r.mapDerivedCategorySingleFunctor 0).app M ≪≫
      (DerivedCategory.singleFunctorIsoCompQ _ 0).app (r.obj M)
  obtain ⟨α, hα⟩ := Scheme.perfect_affine_map_representative S U hU A P
    (strictlyPerfect_single_restricted_unit S U) hP
    (c.inv ≫ r.mapDerivedCategory.map a ≫ e.hom)
  let F := localizedModuleStalk S U ⟨s, hs⟩
  obtain ⟨hadd, hlim, hcolim, hst⟩ :=
    localized_homology_stalk_comparison S U ⟨s, hs⟩
  have := hadd
  have := hlim
  have := hcolim
  have hf : IsIso (F.map (α.f 0)) :=
    isIso_localized_stalk_component_of_residue_homology S E a s U hs P hP
      hnegative hzero e ha c α hα
  let T := F.mapHomologicalComplex (.up ℤ)
  have hA : IsZero ((T.obj A).X 1) := F.map_isZero
    (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega))
  have : Epi ((T.map α).f 0) := by
    change Epi (F.map (α.f 0))
    exact IsSplitEpi.epi _
  have hαH : Epi (HomologicalComplex.homologyMap (T.map α) 0) :=
    epi_homologyMap_of_epi_component_zero_outgoing (T.map α) hA
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) 0 ⋙ F
  let b := Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactors _ 0) F ≪≫
    (F.mapHomologicalComplexHomologyIso (.up ℤ) 0).symm
  have : Epi ((F.mapHomologicalComplex (.up ℤ) ⋙
      HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℤ) 0).map α) := hαH
  have hQ : Epi (H.map (DerivedCategory.Q.map α)) := epi_map_of_natIso b α
  have : IsIso (H.map c.inv) := Functor.map_isIso H c.inv
  have : Epi (H.map c.inv) := IsSplitEpi.epi _
  have : IsIso (H.map e.hom) := Functor.map_isIso H e.hom
  have hr : Epi (H.map (r.mapDerivedCategory.map a)) := by
    rw [hα, Functor.map_comp, Functor.map_comp] at hQ
    exact (epi_comp_iff_of_isIso _ _).mp
      ((epi_comp_iff_of_epi _ _).mp hQ)
  obtain ⟨t⟩ := hst 0
  let G := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0 ⋙
      Scheme.Modules.toPresheaf S ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} s
  have : Epi ((r.mapDerivedCategory ⋙ H).map a) := hr
  have hg : Epi (G.map a) := epi_map_of_natIso t a
  exact (AddCommGrpCat.epi_iff_surjective (G.map a)).mp hg

end AlgebraicGeometry
