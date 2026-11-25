/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LocalizedResidueHomology
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import WeilConjectures.AlgebraicGeometry.OpenModuleStalkFreeProjective
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Homology.KFlatStalkCriterion
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import WeilConjectures.Topology.PointModuleEvaluationEquivalence
import WeilConjectures.AlgebraicGeometry.ResiduePullbackGlobalSections

/-! # Natural residue homology comparison for localized strictly perfect complexes

## References

* Stacks Project, Tags 06YJ and 0098
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem inverse_naturality_of_isIso_app
    {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (τ : F ⟶ G) {P Q : C} (α : P ⟶ Q) [IsIso (τ.app P)] [IsIso (τ.app Q)] :
    G.map α ≫ inv (τ.app Q) = inv (τ.app P) ≫ F.map α := by
  apply (cancel_epi (τ.app P)).mp
  rw [← Category.assoc, ← τ.naturality α, Category.assoc, IsIso.hom_inv_id,
    Category.comp_id, IsIso.hom_inv_id_assoc]

private theorem strictlyPerfect_overEquiv_isKFlat (S : Scheme.{u}) (U : S.Opens)
    (P : CochainComplex
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) ℤ)
    (hP : Scheme.IsStrictlyPerfect S U P) :
    letI : (Scheme.Modules.overEquiv U).functor.Additive :=
      Functor.additive_of_preserves_binary_products _
    CochainComplex.IsAcyclicTensorKFlat (R := U.toScheme.sheaf)
      (((Scheme.Modules.overEquiv U).functor.mapHomologicalComplex (.up ℤ)).obj P) := by
  classical
  let O := (Scheme.Modules.overEquiv U).functor
  have : O.Additive := Functor.additive_of_preserves_binary_products _
  let K := (O.mapHomologicalComplex (.up ℤ)).obj P
  apply (RingedSpace.isKFlat_iff_stalk_isKFlat U.toScheme.toRingedSpace K).2
  intro y B hB
  let T := RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace y
  let C := (T.mapHomologicalComplex (.up ℤ)).obj K
  have hbounded : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (C.X i) := by
    obtain ⟨a, b, hab⟩ := hP.1
    exact ⟨b, fun i hi ↦ T.map_isZero (O.map_isZero (hab i (Or.inr hi)))⟩
  have hflat : ∀ i : ℤ, Module.Flat (U.toScheme.presheaf.stalk y) (C.X i) := by
    intro i
    obtain ⟨m, ι, π, hιπ⟩ := hP.2 i
    let R := ModuleCat.restrictScalars (U.ι.stalkMap y).hom
    let er := (asIso (U.ι.stalkMap y)).commRingCatIsoToRingEquiv
    have : R.IsEquivalence := ModuleCat.restrictScalars_isEquivalence_of_ringEquiv er
    have hfree : Projective (T.obj (O.obj (SheafOfModules.free
        (R := (moduleRings S.toRingedSpace).over U) (ULift.{u} (Fin m))))) := by
      apply R.projective_of_map_projective
      exact openModuleStalk_free_projective S U y m
    have hret : Retract (C.X i) (T.obj (O.obj (SheafOfModules.free
        (R := (moduleRings S.toRingedSpace).over U) (ULift.{u} (Fin m))))) :=
      ⟨T.map (O.map ι), T.map (O.map π), by
        rw [← T.map_comp, ← O.map_comp, hιπ, O.map_id]
        exact T.map_id (O.obj (P.X i))⟩
    have : Projective (C.X i) := hret.projective
    have : Module.Projective (U.toScheme.presheaf.stalk y) (C.X i) := inferInstance
    infer_instance
  exact CochainComplex.acyclic_mapBifunctor_of_boundedAbove_flat C hbounded hflat B hB

/-- An invertible counit on selected complexes gives natural homology comparisons. -/
private theorem exists_homology_comparison_of_counit
    {C A B D : Type*} [Category* C] [Category* A] [Category* B] [Category* D]
    [Abelian C] [Abelian A] [Abelian B] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory A] [HasDerivedCategory B]
    (O : C ⥤ A) [O.Additive] [PreservesFiniteLimits O] [PreservesFiniteColimits O]
    (F : A ⥤ B) [F.Additive] (L : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Qh ⋙ L ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (Γ : B ⥤ D) [Γ.Additive] [Γ.PreservesHomology]
    (R : C ⥤ D) [R.PreservesZeroMorphisms] (d : O ⋙ F ⋙ Γ ≅ R)
    (p : CochainComplex C ℤ → Prop)
    (hε : ∀ K, p K → IsIso (ε.app ((HomotopyCategory.quotient A (.up ℤ)).obj
      ((O.mapHomologicalComplex (.up ℤ)).obj K)))) :
    ∃ t : ∀ (K : CochainComplex C ℤ) (_hK : p K),
        ((R.mapHomologicalComplex (.up ℤ)).obj K).homology 0 ≅
          (O.mapDerivedCategory ⋙ L ⋙ DerivedCategory.homologyFunctor B 0 ⋙ Γ).obj
            (DerivedCategory.Q.obj K),
      ∀ K K' (hK : p K) (hK' : p K') (α : K ⟶ K'),
        HomologicalComplex.homologyMap ((R.mapHomologicalComplex (.up ℤ)).map α) 0 ≫
            (t K' hK').hom =
          (t K hK).hom ≫
            (O.mapDerivedCategory ⋙ L ⋙ DerivedCategory.homologyFunctor B 0 ⋙ Γ).map
              (DerivedCategory.Q.map α) := by
  let Oc := O.mapHomologicalComplex (.up ℤ)
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let H := DerivedCategory.homologyFunctor B 0
  let HM := HomologicalComplex.homologyFunctor D (.up ℤ) 0
  let hΓ := (Γ.mapHomologicalComplexHomologyIso (.up ℤ) 0).symm
  let v := NatIso.mapHomologicalComplex d (.up ℤ)
  let z := Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (Oc ⋙ Fc) (DerivedCategory.homologyFunctorFactors B 0)) Γ ≪≫
    Functor.isoWhiskerLeft (Oc ⋙ Fc) hΓ ≪≫ Functor.isoWhiskerRight v HM
  let εc : DerivedCategory.Q ⋙ L ⟶ Fc ⋙ DerivedCategory.Q :=
    (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso A).symm L).hom ≫
      Functor.whiskerLeft (HomotopyCategory.quotient A (.up ℤ)) ε ≫
      (Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (.up ℤ))
        DerivedCategory.Qh).hom ≫
      (Functor.isoWhiskerLeft Fc (DerivedCategory.quotientCompQhIso B)).hom
  have hεc (K : CochainComplex C ℤ) (hK : p K) : IsIso (εc.app (Oc.obj K)) := by
    have := hε K hK
    dsimp only [εc, NatTrans.comp_app, Functor.whiskerLeft_app]
    infer_instance
  let η : DerivedCategory.Q ⋙ O.mapDerivedCategory ⋙ L ⟶
      Oc ⋙ Fc ⋙ DerivedCategory.Q :=
    (Functor.isoWhiskerRight O.mapDerivedCategoryFactors L).hom ≫
      Functor.whiskerLeft Oc εc
  have hη (K : CochainComplex C ℤ) (hK : p K) : IsIso (η.app K) := by
    have := hεc K hK
    dsimp only [η, NatTrans.comp_app, Functor.whiskerLeft_app]
    infer_instance
  let τ : DerivedCategory.Q ⋙ O.mapDerivedCategory ⋙ L ⋙ H ⋙ Γ ⟶
      R.mapHomologicalComplex (.up ℤ) ⋙ HM :=
    Functor.whiskerRight η (H ⋙ Γ) ≫ z.hom
  have hτ (K : CochainComplex C ℤ) (hK : p K) : IsIso (τ.app K) := by
    have := hη K hK
    change IsIso ((H ⋙ Γ).map (η.app K) ≫ (z.app K).hom)
    infer_instance
  let t := fun K hK ↦ by
    have := hτ K hK
    exact (asIso (τ.app K)).symm
  refine ⟨t, ?_⟩
  intro K K' hK hK' α
  have := hτ K hK
  have := hτ K' hK'
  dsimp only [t, Iso.symm_hom, asIso_inv]
  exact inverse_naturality_of_isIso_app τ α

/-- Termwise residue stalk homology of strictly perfect localized complexes agrees
naturally with localized derived residue homology. The comparisons are simultaneous
for all strictly perfect complexes and all their chain maps. -/
theorem exists_localizedStrictPerfectResidueHomology_iso (S : Scheme.{u}) (U : S.Opens)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    (x : U.toScheme) :
    letI : (Scheme.Modules.overEquiv U).functor.Additive :=
      Functor.additive_of_preserves_binary_products _
    letI : (ModuleCat.extendScalars (IsLocalRing.residue
        (U.toScheme.presheaf.stalk x))).Additive :=
      (ModuleCat.extendRestrictScalarsAdj (IsLocalRing.residue
        (U.toScheme.presheaf.stalk x))).left_adjoint_additive
    letI : (RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace x).PreservesZeroMorphisms :=
      RingedSpace.moduleStalkFunctor_preservesZeroMorphisms U.toScheme.toRingedSpace x
    letI : ((Scheme.Modules.overEquiv U).functor ⋙
        RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace x ⋙
        ModuleCat.extendScalars (IsLocalRing.residue
          (U.toScheme.presheaf.stalk x))).PreservesZeroMorphisms :=
      { map_zero := by
          intro M N
          simp only [Functor.comp_map]
          rw [Functor.map_zero, Functor.map_zero, Functor.map_zero] }
    let F := ((Scheme.Modules.overEquiv U).functor ⋙
      RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace x ⋙
      ModuleCat.extendScalars (IsLocalRing.residue (U.toScheme.presheaf.stalk x)))
    ∃ t : ∀ (P : CochainComplex
        (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) ℤ)
        (_hP : Scheme.IsStrictlyPerfect S U P),
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P).homology 0 ≅
            (localizedResidueHomology S U x).obj (DerivedCategory.Q.obj P),
      ∀ (P Q : CochainComplex
          (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) ℤ)
        (hP : Scheme.IsStrictlyPerfect S U P) (hQ : Scheme.IsStrictlyPerfect S U Q)
        (α : P ⟶ Q),
        HomologicalComplex.homologyMap
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map α) 0 ≫ (t Q hQ).hom =
          (t P hP).hom ≫ (localizedResidueHomology S U x).map (DerivedCategory.Q.map α) :=
  by
    classical
    let C := SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)
    let A := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)
    let B := SheafOfModules.{u}
      (moduleRings (Spec (U.toScheme.residueField x)).toRingedSpace)
    let : Abelian C := inferInstanceAs (Abelian C)
    let : Abelian A := inferInstanceAs (Abelian A)
    let : Abelian B := inferInstanceAs (Abelian B)
    let O := (Scheme.Modules.overEquiv U).functor
    have : O.Additive := Functor.additive_of_preserves_binary_products _
    have : (ModuleCat.extendScalars (IsLocalRing.residue
        (U.toScheme.presheaf.stalk x))).Additive :=
      (ModuleCat.extendRestrictScalarsAdj (IsLocalRing.residue
        (U.toScheme.presheaf.stalk x))).left_adjoint_additive
    have : (RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace
        x).PreservesZeroMorphisms :=
      RingedSpace.moduleStalkFunctor_preservesZeroMorphisms U.toScheme.toRingedSpace x
    have : (O ⋙ RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace x ⋙
        ModuleCat.extendScalars (IsLocalRing.residue
          (U.toScheme.presheaf.stalk x))).PreservesZeroMorphisms :=
      { map_zero := by
          intro M N
          simp only [Functor.comp_map]
          rw [Functor.map_zero, Functor.map_zero, Functor.map_zero] }
    let : HasDerivedCategory.{u + 1} U.toScheme.Modules := HasDerivedCategory.standard _
    let : HasDerivedCategory.{u + 1} A := HasDerivedCategory.standard _
    let : HasDerivedCategory.{u + 1} B := HasDerivedCategory.standard _
    let : HasDerivedCategory.{u + 1} (Spec (U.toScheme.residueField x)).Modules :=
      HasDerivedCategory.standard _
    let f := U.toScheme.fromSpecResidueField x
    obtain ⟨_, _, _, _, _, _, _, F, hF, hmap, hAdd, ε, _, _, hcompute⟩ :=
      (derivedPullback_spec.{u, u + 1} f)
    have hF' : F = Scheme.Modules.tensorPullback f :=
      CategoryTheory.Functor.ext hF (fun M N a ↦ hmap a)
    subst F
    let F := Scheme.Modules.tensorPullback f
    have : F.Additive := hAdd
    let Γ : B ⥤ ModuleCat.{u} (U.toScheme.residueField x) :=
      SheafOfModules.evaluation
        (moduleRings (Spec (U.toScheme.residueField x)).toRingedSpace) (Opposite.op ⊤) ⋙
      ModuleCat.restrictScalars (Scheme.ΓSpecIso (U.toScheme.residueField x)).inv.hom
    have : (RingedSpace.globalSectionsFunctor
        (Spec (U.toScheme.residueField x)).toRingedSpace).IsEquivalence :=
      RingedSpace.globalSectionsFunctor_isEquivalence_of_unique _
    have : PreservesFiniteLimits
        (SheafOfModules.evaluation
          (moduleRings (Spec (U.toScheme.residueField x)).toRingedSpace) (Opposite.op ⊤)) :=
      inferInstanceAs (PreservesFiniteLimits (RingedSpace.globalSectionsFunctor
        (Spec (U.toScheme.residueField x)).toRingedSpace))
    have : PreservesFiniteColimits
        (SheafOfModules.evaluation
          (moduleRings (Spec (U.toScheme.residueField x)).toRingedSpace) (Opposite.op ⊤)) :=
      inferInstanceAs (PreservesFiniteColimits (RingedSpace.globalSectionsFunctor
        (Spec (U.toScheme.residueField x)).toRingedSpace))
    have : PreservesFiniteLimits Γ := comp_preservesFiniteLimits _ _
    have : PreservesFiniteColimits Γ := comp_preservesFiniteColimits _ _
    have : Γ.Additive := Functor.additive_of_preserves_binary_products _
    have : Γ.PreservesHomology := inferInstance
    obtain ⟨d⟩ := Scheme.nonempty_residuePullback_globalSections_iso U.toScheme x
    exact exists_homology_comparison_of_counit O F (derivedPullback f) ε Γ
      (O ⋙ RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace x ⋙
        ModuleCat.extendScalars (IsLocalRing.residue (U.toScheme.presheaf.stalk x)))
      (Functor.isoWhiskerLeft O d) (Scheme.IsStrictlyPerfect S U)
      (fun P hP ↦ hcompute _ (strictlyPerfect_overEquiv_isKFlat S U P hP))

end AlgebraicGeometry
