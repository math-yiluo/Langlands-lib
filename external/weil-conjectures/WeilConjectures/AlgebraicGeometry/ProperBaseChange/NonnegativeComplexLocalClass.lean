/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageSectionPresheaf
public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoices
public import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap
import all WeilConjectures.AlgebraicGeometry.Section.SectionCohomologyCycleFormula
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryLocalClassCycles

/-! # Ordinary local classes and extension by zero

## References

* Stacks Project, Cohomology, Tag 01E4
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
noncomputable section
namespace AlgebraicGeometry
open Scheme.Modules

private theorem map_comp_through {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {K L M N P : C} {Q : D}
    (k : Q ⟶ F.obj K) (i : K ⟶ L) (j : M ⟶ P) (f : K ⟶ M)
    (a : L ⟶ N) (b : N ⟶ P) (i' : Q ⟶ F.obj L)
    (hf : f ≫ j = i ≫ a ≫ b) (hk : k ≫ F.map i = i') :
    k ≫ F.map f ≫ F.map j = i' ≫ F.map a ≫ F.map b := by
  rw [← F.map_comp, hf]
  simp only [F.map_comp, ← Category.assoc, hk]

private theorem mapExtend_comp_component
    {C D E T : Type*} [Category C] [Category D] [Category E] [Category T]
    [Abelian C] [Abelian D] [Abelian E] [Abelian T]
    (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ T) [F.Additive] [G.Additive] [H.Additive]
    (L : CochainComplex C ℕ) (q : ℕ) :
    let B := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj L
    let Γ := (F ⋙ G) ⋙ H
    let A := (Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj L
    (A.extendXIso ComplexShape.embeddingUpNat (i := q) rfl).inv ≫
        (L.mapExtendIso ComplexShape.embeddingUpNat Γ).inv.f (q : ℤ) ≫
        H.map (G.map ((L.mapExtendIso ComplexShape.embeddingUpNat F).hom.f (q : ℤ))) ≫
        H.map (G.map (B.extendXIso ComplexShape.embeddingUpNat (i := q) rfl).hom) =
      𝟙 (A.X q) := by
  intro B Γ A
  have hr : ComplexShape.embeddingUpNat.r (q : ℤ) = some q :=
    ComplexShape.embeddingUpNat.r_f q
  dsimp only [HomologicalComplex.mapExtendIso, HomologicalComplex.Hom.isoOfComponents,
    HomologicalComplex.extendXIso, HomologicalComplex.extend.XIso]
  erw [HomologicalComplex.mapExtendX_hom_eq L Γ hr,
    HomologicalComplex.mapExtendX_hom_eq L F hr]
  simp only [eqToIso.hom, eqToIso.inv, eqToHom_map, eqToHom_trans, eqToHom_refl]

private theorem localClass_of_cycles {C : Type*} [Category C]
    {Z H ZA HA T ZJ HJ ZB HB : C}
    (π : Z ⟶ H) [Epi π] (m : H ⟶ HB) (a : H ⟶ HA) (α : ZA ⟶ HA)
    (z : Z ⟶ ZA) (η : HA ⟶ T) (c : T ⟶ HJ) (k : ZA ⟶ ZJ)
    (πJ : ZJ ⟶ HJ) (d : HJ ⟶ HB) (zD : ZJ ⟶ ZB) (πB : ZB ⟶ HB)
    (zM : Z ⟶ ZB) (hleft : π ≫ m = zM ≫ πB) (ha : π ≫ a = z ≫ α)
    (hclass : α ≫ η ≫ c = k ≫ πJ) (hd : πJ ≫ d = zD ≫ πB)
    (hz : z ≫ k ≫ zD = zM) : m = a ≫ η ≫ c ≫ d := by
  apply (cancel_epi π).mp
  rw [hleft, ← Category.assoc π a, ha]
  simp only [Category.assoc]
  rw [← Category.assoc α η, ← Category.assoc (α ≫ η) c,
    Category.assoc α η c, hclass]
  simp only [Category.assoc]
  rw [hd, ← Category.assoc z k, ← Category.assoc (z ≫ k) zD,
    Category.assoc z k zD, hz]

-- Transport cycles through extension and the two section forgetful functors.
/-- The module cocycle class map is the abelian sheafification class map, compatibly
with extension by zero and exact evaluation. No derived category or acyclicity
hypothesis is used. -/
theorem nonnegativeComplex_localClass {X Y : Scheme.{u}}
    (D : SheafOfModules.{u} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings Y.toRingedSpace)) [D.Additive]
    (L : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℕ)
    (q : ℕ) (V : Y.Opens) :
    let P := D ⋙ RingedSpace.localAbelianSections Y.toRingedSpace
    letI : P.Additive := inferInstanceAs
      (D ⋙ RingedSpace.localAbelianSections Y.toRingedSpace).Additive
    let E := (CategoryTheory.evaluation Y.Opensᵒᵖ AddCommGrpCat.{u}).obj (op V)
    let Γ := P ⋙ E
    letI : Γ.Additive := inferInstanceAs (P ⋙ E).Additive
    let B := (D.mapHomologicalComplex (ComplexShape.up ℕ)).obj L
    let a :=
      (((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj L).extendHomologyIso
        ComplexShape.embeddingUpNat (j := q) rfl).symm ≪≫
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ)
        (q : ℤ)).mapIso (L.mapExtendIso ComplexShape.embeddingUpNat Γ).symm ≪≫
      (((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (L.extend ComplexShape.embeddingUpNat)).sc (q : ℤ)).mapHomologyIso E
    let J := (D.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (L.extend ComplexShape.embeddingUpNat)
    let d :=
      (HomologicalComplex.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ) (q : ℤ)).mapIso
        (L.mapExtendIso ComplexShape.embeddingUpNat D) ≪≫
      B.extendHomologyIso ComplexShape.embeddingUpNat (j := q) rfl
    (((((SheafOfModules.forget Y.ringCatSheaf).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj B).sc q).mapHomologyIso
        (PresheafOfModules.toPresheaf Y.ringCatSheaf.obj ⋙ E)).hom ≫
        ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map
          (sectionCohomologyTheta B q)).app (op V) =
      a.hom ≫
        ((sheafificationAdjunction (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).unit.app
          (((RingedSpace.localAbelianSections Y.toRingedSpace).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj J |>.homology (q : ℤ))).app (op V) ≫
        ((sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).map
          (RingedSpace.localSectionComplexSheafificationIso Y.toRingedSpace (q : ℤ) J).hom).app
            (op V) ≫
        ((RingedSpace.localAbelianSections Y.toRingedSpace).map d.hom).app (op V) := by
  intro P E Γ B a J d
  let F := RingedSpace.localAbelianSections Y.toRingedSpace
  let : F.Additive := inferInstanceAs
    (RingedSpace.localAbelianSections Y.toRingedSpace).Additive
  let : P.Additive := inferInstanceAs (D ⋙ F).Additive
  let : Γ.Additive := inferInstanceAs (P ⋙ E).Additive
  let I := L.extend ComplexShape.embeddingUpNat
  let A := (P.mapHomologicalComplex (.up ℤ)).obj I
  let C := (Γ.mapHomologicalComplex (.up ℕ)).obj L
  let z := (C.extendCyclesIso ComplexShape.embeddingUpNat (j := q) rfl).inv ≫
    HomologicalComplex.cyclesMap (L.mapExtendIso ComplexShape.embeddingUpNat Γ).inv
      (q : ℤ) ≫ ((A.sc (q : ℤ)).mapCyclesIso E).hom
  have hπ : C.homologyπ q ≫ a.hom = z ≫ E.map (A.homologyπ (q : ℤ)) := by
    dsimp only [a, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    erw [HomologicalComplex.homologyπ_extendHomologyIso_inv_assoc,
      HomologicalComplex.homologyπ_naturality_assoc]
    erw [homologyπ_mapHomologyIso_hom E (A.sc (q : ℤ))]
    rfl
  have hz : z ≫ E.map (A.iCycles (q : ℤ)) =
      C.iCycles q ≫ (C.extendXIso ComplexShape.embeddingUpNat (i := q) rfl).inv ≫
        (L.mapExtendIso ComplexShape.embeddingUpNat Γ).inv.f (q : ℤ) := by
    dsimp only [z]
    simp only [Category.assoc]
    erw [ShortComplex.mapCyclesIso_hom_iCycles,
      HomologicalComplex.cyclesMap_i,
      HomologicalComplex.extendCyclesIso_inv_iCycles_assoc]
  let zD := HomologicalComplex.cyclesMap
      (L.mapExtendIso ComplexShape.embeddingUpNat D).hom (q : ℤ) ≫
    (B.extendCyclesIso ComplexShape.embeddingUpNat (j := q) rfl).hom
  have hdπ : J.homologyπ (q : ℤ) ≫ d.hom = zD ≫ B.homologyπ q := by
    dsimp only [d, Iso.trans_hom, Functor.mapIso_hom]
    erw [HomologicalComplex.homologyπ_naturality_assoc,
      HomologicalComplex.homologyπ_extendHomologyIso_hom]
    rfl
  have hdz : zD ≫ B.iCycles q = J.iCycles (q : ℤ) ≫
      (L.mapExtendIso ComplexShape.embeddingUpNat D).hom.f (q : ℤ) ≫
      (B.extendXIso ComplexShape.embeddingUpNat (i := q) rfl).hom := by
    dsimp only [zD]
    erw [Category.assoc, HomologicalComplex.extendCyclesIso_hom_iCycles,
      HomologicalComplex.cyclesMap_i_assoc]
  let k := ((J.sc (q : ℤ)).map F).isoCyclesOfIsLimit
    (KernelFork.mapIsLimit _ (J.sc (q : ℤ)).cyclesIsKernel F) |>.inv
  let M := (B.sc q).map (SheafOfModules.forget Y.ringCatSheaf)
  let E' := PresheafOfModules.toPresheaf Y.ringCatSheaf.obj ⋙ E
  let kM := M.isoCyclesOfIsLimit
    (KernelFork.mapIsLimit _ (B.sc q).cyclesIsKernel
      (SheafOfModules.forget Y.ringCatSheaf)) |>.inv
  let zM := (M.mapCyclesIso E').hom ≫ E'.map kM
  have hzM : zM ≫ E.map (F.map (B.iCycles q)) = C.iCycles q := by
    change ((M.mapCyclesIso E').hom ≫ E'.map kM) ≫
      E'.map ((SheafOfModules.forget Y.ringCatSheaf).map (B.iCycles q)) = _
    rw [Category.assoc, ← E'.map_comp]
    erw [M.isoCyclesOfIsLimit_inv_ι]
    exact M.mapCyclesIso_hom_iCycles E'
  have hcomponent :
      (C.extendXIso ComplexShape.embeddingUpNat (i := q) rfl).inv ≫
        (L.mapExtendIso ComplexShape.embeddingUpNat Γ).inv.f (q : ℤ) ≫
        E.map (F.map ((L.mapExtendIso ComplexShape.embeddingUpNat D).hom.f (q : ℤ))) ≫
        E.map (F.map (B.extendXIso ComplexShape.embeddingUpNat (i := q) rfl).hom) =
      𝟙 (C.X q) := mapExtend_comp_component D F E L q
  have hcycles : z ≫ E.map k ≫ E.map (F.map zD) = zM := by
    apply (cancel_mono (E.map (F.map (B.iCycles q)))).1
    have hh : k ≫ F.map zD ≫ F.map (B.iCycles q) =
        A.iCycles (q : ℤ) ≫
          F.map ((L.mapExtendIso ComplexShape.embeddingUpNat D).hom.f (q : ℤ)) ≫
          F.map (B.extendXIso ComplexShape.embeddingUpNat (i := q) rfl).hom := by
      exact map_comp_through F k (J.iCycles (q : ℤ)) (B.iCycles q) zD
        ((L.mapExtendIso ComplexShape.embeddingUpNat D).hom.f (q : ℤ))
        (B.extendXIso ComplexShape.embeddingUpNat (i := q) rfl).hom
        (A.iCycles (q : ℤ)) hdz
        (((J.sc (q : ℤ)).map F).isoCyclesOfIsLimit_inv_ι _)
    have hhE := congrArg E.map hh
    simp only [Functor.map_comp] at hhE
    calc
      _ = z ≫ E.map (A.iCycles (q : ℤ)) ≫
          E.map (F.map ((L.mapExtendIso ComplexShape.embeddingUpNat D).hom.f (q : ℤ))) ≫
          E.map (F.map (B.extendXIso ComplexShape.embeddingUpNat (i := q) rfl).hom) := by
        simpa only [Category.assoc] using congrArg (fun m ↦ z ≫ m) hhE
      _ = C.iCycles q := by
        erw [← Category.assoc z (E.map (A.iCycles (q : ℤ))), hz]
        simp only [Category.assoc, hcomponent, Category.comp_id]
      _ = _ := hzM.symm
  let η := (sheafificationAdjunction (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).unit.app
    (A.homology (q : ℤ))
  let c := (sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).map
    (RingedSpace.localSectionComplexSheafificationIso Y.toRingedSpace (q : ℤ) J).hom
  have hh : E.map (A.homologyπ (q : ℤ)) ≫ E.map η ≫ E.map c =
      E.map k ≫ E.map (F.map (J.homologyπ (q : ℤ))) := by
    have h := congrArg E.map (ordinaryLocalClass_cycles J (q : ℤ))
    change E.map (A.homologyπ (q : ℤ) ≫ η ≫ c) =
      E.map (k ≫ F.map (J.homologyπ (q : ℤ))) at h
    simpa only [Functor.map_comp] using h
  have hleft : C.homologyπ q ≫
      ((M.mapHomologyIso E').hom ≫ E'.map (sectionCohomologyTheta B q)) =
      zM ≫ E.map (F.map (B.homologyπ q)) := by
    have h := section_comparison_cycles B q V
    change C.homologyπ q ≫ (M.mapHomologyIso E').hom ≫
      E'.map (sectionCohomologyTheta B q) = zM ≫ E.map (F.map (B.homologyπ q)) at h
    exact h
  have hd : E.map (F.map (J.homologyπ (q : ℤ))) ≫ E.map (F.map d.hom) =
      E.map (F.map zD) ≫ E.map (F.map (B.homologyπ q)) := by
    simpa only [Functor.map_comp] using congrArg (fun f ↦ E.map (F.map f)) hdπ
  exact localClass_of_cycles (C.homologyπ q) _ a.hom (E.map (A.homologyπ (q : ℤ)))
    z (E.map η) (E.map c) (E.map k) (E.map (F.map (J.homologyπ (q : ℤ))))
    (E.map (F.map d.hom)) (E.map (F.map zD)) (E.map (F.map (B.homologyπ q)))
    zM hleft hπ hh hd hcycles

end AlgebraicGeometry
