/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Scalar.TowerScalarSingleCounit
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Chern.TowerChernPullbackData
import all WeilConjectures.Algebra.Homology.DivisibleReduction.DivisibleExtensionDerivedReductionSupplement
import all WeilConjectures.Algebra.Homology.PullbackTensorCanonical.PullbackTensorCanonicalShiftUnit
import all WeilConjectures.CategoryTheory.AlgebraDiagramPullback.AlgebraDiagramDerivedComparisons
import all WeilConjectures.Algebra.Homology.RingedCoefficientProjection.RingedCoefficientPullbackShifts
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift
import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction

/-! # Derived lifting of ordinary scalar association on whole systems

Source: blueprint classes proof (2), scalar comparison on K-flat representatives.
(blueprint: lem-sp-tower-scalar-pullback-counit-lift).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
private theorem scalar_counit_shift {T : Scheme.{u}} (c : Chern l E T) :
    NatTrans.CommShift c.scalar.model.ε ℤ := by
  let q := coefficientSystemMap l E T
  let m := c.scalar.model
  let r := SheafOfModules.scalarRes q
  let ah := (SheafOfModules.sheafScalarOrdinaryAdjunction q m).mapHomologicalComplex (.up ℤ)
  let ad := SheafOfModules.sheafScalarDerivedAdjunction q m
  let : ad.CommShift ℤ := ad.commShift_of_rightAdjoint ℤ
  let : ah.CommShift ℤ := Adjunction.CommShift.mk' ah (A := ℤ) inferInstance
  let β := r.mapDerivedCategoryFactors.inv
  let τ := ((mateEquiv ah ad).symm (TwoSquare.mk _ _ _ _ β))
  have hτshift : NatTrans.CommShift τ ℤ := by
    dsimp only [τ, mateEquiv, Equiv.symm, Equiv.coe_fn_mk, TwoSquare.mk]
    infer_instance
  have hflat (P : CochainComplex (Systems T (Rrings l T)) ℤ)
      (hp : CochainComplex.IsKFlatIndependentCoefficients P) :
      τ.app P = m.ε.app P := by
    apply (ad.homEquiv _ _).injective
    have hm := unit_mateEquiv_symm ah ad (TwoSquare.mk _ _ _ _ β) P
    change DerivedCategory.Q.map (ah.unit.app _) ≫ β.app _ =
      ad.unit.app _ ≫ r.mapDerivedCategory.map (τ.app _) at hm
    dsimp only [Functor.id_obj] at hm
    have hn := SheafOfModules.scalar_derived_unit q m P hp
    apply (cancel_mono (r.mapDerivedCategoryFactors.hom.app
      ((m.E.mapHomologicalComplex (.up ℤ)).obj P))).mp
    simp only [Adjunction.homEquiv_unit]
    rw [← hm]
    simp only [β, Category.assoc, Iso.inv_hom_id_app]
    exact hn.symm
  have heq : τ = m.ε := by
    ext P₀
    obtain ⟨P, f, hp, _, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients P₀
    let : IsIso (DerivedCategory.Q.map f) :=
      Localization.inverts DerivedCategory.Q (HomologicalComplex.quasiIso _ _) f hq
    apply (cancel_epi (m.T.map (DerivedCategory.Q.map f))).mp
    change (DerivedCategory.Q ⋙ m.T).map f ≫ τ.app P₀ =
      (DerivedCategory.Q ⋙ m.T).map f ≫ m.ε.app P₀
    rw [τ.naturality, m.ε.naturality, hflat P hp]
  exact heq ▸ hτshift

private def single_counit
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (E₀ : A ⥤ B) [E₀.Additive] (S : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Q ⋙ S ⟶ E₀.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) :
    DerivedCategory.singleFunctor A 0 ⋙ S ⟶ E₀ ⋙ DerivedCategory.singleFunctor B 0 :=
  Functor.whiskerRight (DerivedCategory.singleFunctorIsoCompQ A 0).hom S ≫
    Functor.whiskerLeft (HomologicalComplex.single A (.up ℤ) 0) ε ≫
    Functor.whiskerRight (HomologicalComplex.singleMapHomologicalComplex E₀ (.up ℤ) 0).hom
      DerivedCategory.Q ≫
    Functor.whiskerLeft E₀ (DerivedCategory.singleFunctorIsoCompQ B 0).inv

private theorem counit_square_single
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (EY : A ⥤ B) (EX : C ⥤ D) (P : A ⥤ C) (Q : B ⥤ D)
    [EY.Additive] [EX.Additive] [P.Additive] [Q.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (SY : DerivedCategory A ⥤ DerivedCategory B)
    (SX : DerivedCategory C ⥤ DerivedCategory D)
    (εY : DerivedCategory.Q ⋙ SY ⟶ EY.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (εX : DerivedCategory.Q ⋙ SX ⟶ EX.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (α : EY ⋙ Q ≅ P ⋙ EX)
    (κ : SY ⋙ Q.mapDerivedCategory ⟶ P.mapDerivedCategory ⋙ SX)
    (hc : ∀ K : CochainComplex A ℤ,
      κ.app (DerivedCategory.Q.obj K) ≫ SX.map (P.mapDerivedCategoryFactors.hom.app K) ≫
          εX.app ((P.mapHomologicalComplex (.up ℤ)).obj K) =
        Q.mapDerivedCategory.map (εY.app K) ≫
          Q.mapDerivedCategoryFactors.hom.app ((EY.mapHomologicalComplex (.up ℤ)).obj K) ≫
          DerivedCategory.Q.map
            ((Functor.mapHomologicalComplexCompIso α (.up ℤ) ≪≫
              (Functor.mapHomologicalComplexCompIso (Iso.refl _) (.up ℤ)).symm).hom.app K)) :
    ∀ M : A,
      κ.app ((DerivedCategory.singleFunctor A 0).obj M) ≫
          SX.map ((P.mapDerivedCategorySingleFunctor 0).hom.app M) ≫
          (single_counit EX SX εX).app (P.obj M) =
        Q.mapDerivedCategory.map ((single_counit EY SY εY).app M) ≫
          (Q.mapDerivedCategorySingleFunctor 0).hom.app (EY.obj M) ≫
          (DerivedCategory.singleFunctor D 0).map (α.hom.app M) := by
  intro M
  let K := (HomologicalComplex.single A (.up ℤ) 0).obj M
  let p := (HomologicalComplex.singleMapHomologicalComplex P (.up ℤ) 0).hom.app M
  let eY := (HomologicalComplex.singleMapHomologicalComplex EY (.up ℤ) 0).hom.app M
  let eX := (HomologicalComplex.singleMapHomologicalComplex EX (.up ℤ) 0).hom.app (P.obj M)
  let q := (HomologicalComplex.singleMapHomologicalComplex Q (.up ℤ) 0).hom.app (EY.obj M)
  let a := Functor.mapHomologicalComplexCompIso α (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl _) (.up ℤ)).symm
  have hsingle : a.hom.app K ≫ (EX.mapHomologicalComplex (.up ℤ)).map p ≫ eX =
      (Q.mapHomologicalComplex (.up ℤ)).map eY ≫ q ≫
        (HomologicalComplex.single D (.up ℤ) 0).map (α.hom.app M) := by
    ext i : 1
    by_cases hi : i = 0
    · subst i
      simp only [Functor.comp_obj, Functor.mapHomologicalComplex_obj_X,
        Functor.mapHomologicalComplexCompIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
        Category.assoc, HomologicalComplex.comp_f, NatIso.mapHomologicalComplex_hom_app_f,
        NatIso.mapHomologicalComplex_inv_app_f, Iso.refl_inv, NatTrans.id_app,
        Functor.mapHomologicalComplex_map_f,
        HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
        HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq, eqToIso_refl,
        Iso.refl_hom, CategoryTheory.Functor.map_id, Category.id_comp,
        HomologicalComplex.single_map_f_self, K, a, p, eX, eY, q]
      erw [EX.map_id, Q.map_id]
      repeat' first | erw [Category.id_comp] | erw [Category.comp_id]
    · simp [p, eX, eY, q, hi,
        HomologicalComplex.singleMapHomologicalComplex_hom_app_ne]
  simp only [single_counit, Functor.mapDerivedCategorySingleFunctor,
    DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom, Iso.refl_inv,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, NatTrans.id_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.map_comp,
    Category.assoc]
  repeat' first
    | erw [P.mapDerivedCategory.map_id]
    | erw [SX.map_id]
    | erw [SY.map_id]
    | erw [Q.mapDerivedCategory.map_id]
    | erw [Category.id_comp]
    | erw [Category.comp_id]
  change κ.app (DerivedCategory.Q.obj K) ≫ SX.map (P.mapDerivedCategoryFactors.hom.app K) ≫
      SX.map (DerivedCategory.Q.map p) ≫
      εX.app ((HomologicalComplex.single C (.up ℤ) 0).obj (P.obj M)) ≫
      DerivedCategory.Q.map eX =
    Q.mapDerivedCategory.map (εY.app K) ≫ Q.mapDerivedCategory.map (DerivedCategory.Q.map eY) ≫
      Q.mapDerivedCategoryFactors.hom.app
        ((HomologicalComplex.single B (.up ℤ) 0).obj (EY.obj M)) ≫
      DerivedCategory.Q.map q ≫
      DerivedCategory.Q.map ((HomologicalComplex.single D (.up ℤ) 0).map (α.hom.app M))
  erw [reassoc_of% (εX.naturality p)]
  erw [reassoc_of% (hc K)]
  erw [reassoc_of% (Q.mapDerivedCategoryFactors.hom.naturality eY)]
  repeat' first
    | erw [← DerivedCategory.Q.map_comp_assoc]
    | erw [← DerivedCategory.Q.map_comp]
  simp only [Category.assoc]
  erw [hsingle]

/-- A scalar-association isomorphism lifts through the universal scalar counits.
Only preservation of the flat K-flat resolving class is needed. Neither coefficient
nor root endpoint normalizations are asserted here.

Source: blueprint latest, classes proof (2), realization step 5; Stacks 06YY,
07A4 and 0G7E (blueprint: lem-sp-tower-scalar-pullback-counit-lift).

Proof: resolve each entire R-system complex by a flat-term K-flat complex P.
The source scalar counit at P and the target scalar counit at pull(P) are
invertible by the hypotheses. Conjugate the termwise ordinary comparison lambda
by these counits and the exact pullback/localization factors. Naturality on the
resolving category and full faithfulness of its localization descend the maps
to kappa on the unbounded derived category. The same formula for the inverse
shows that this comparison is invertible, though only its forward map is needed.
The canonical signed shift comparisons commute with termwise lambda and with
the scalar counits, so their equality on resolving representatives gives
CommShift. The counit square commutes on every complex, not only on resolving
ones: choose a resolving augmentation to that complex, use counit naturality
on both sides, and cancel its inverted image under the two derived composites.
Apply this square to a degree-zero single and compose with the standard single
comparisons. Naturality of the exact pullback factors and the ordinary single
comparison gives precisely the displayed equation. This argument is on whole
systems and does not use faithfulness of derived level evaluation. -/
theorem tower_scalarPullback_counitLift
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    {b : SpTowerShriek.Base l E} (g : SpTowerShriek.Geometry l E b f)
    (cY : Chern l E Y) (cX : Chern l E X)
    (d : IntegralCoefficientPullback l E f cY cX)
    (α : cY.scalar.model.E ⋙ g.pull ≅ d.pull ⋙ cX.scalar.model.E)
    (hflat : ∀ (P : CochainComplex (Systems Y (Rrings l Y)) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients
        (R := WeilConjectures.SemilinearSections.systemRing
          (Scheme.ProEt.topology Y) (fun n ↦ (Rrings l Y).obj (Opposite.op n))
            (fun n ↦ (Rrings l Y).map (homOfLE (Nat.le_succ n)).op)) P →
      (∀ i : ℤ, SheafOfModules.IsFlatOnSite
          (J := WeilConjectures.coefficientSequenceTopology (Scheme.ProEt.topology Y))
          (R := WeilConjectures.SemilinearSections.systemRing
            (Scheme.ProEt.topology Y) (fun n ↦ (Rrings l Y).obj (Opposite.op n))
              (fun n ↦ (Rrings l Y).map (homOfLE (Nat.le_succ n)).op)) (P.X i)) →
      CochainComplex.IsKFlatIndependentCoefficients
        (R := WeilConjectures.SemilinearSections.systemRing
          (Scheme.ProEt.topology X) (fun n ↦ (Rrings l X).obj (Opposite.op n))
            (fun n ↦ (Rrings l X).map (homOfLE (Nat.le_succ n)).op))
        ((d.pull.mapHomologicalComplex (.up ℤ)).obj P)) :
    ∃ κ : cY.scalar.T ⋙ SpTowerShriek.pull l E b g ⟶
        d.pull.mapDerivedCategory ⋙ cX.scalar.T,
      NatTrans.CommShift κ ℤ ∧
      ∀ M : Systems Y (Rrings l Y),
        κ.app ((DerivedCategory.singleFunctor (Systems Y (Rrings l Y)) 0).obj M) ≫
            cX.scalar.T.map ((d.pull.mapDerivedCategorySingleFunctor 0).hom.app M) ≫
            (scalarSingleCounit cX).app (d.pull.obj M) =
          (SpTowerShriek.pull l E b g).map ((scalarSingleCounit cY).app M) ≫
            (g.pull.mapDerivedCategorySingleFunctor 0).hom.app (cY.scalar.model.E.obj M) ≫
            (DerivedCategory.singleFunctor (Systems X (Arings l E X)) 0).map
              (α.hom.app M)  := by
  let := g.pullAdditive
  let := g.pullLimits
  let := g.pullColimits
  let RY := WeilConjectures.SemilinearSections.systemRing
    (Scheme.ProEt.topology Y) (fun n ↦ (Rrings l Y).obj (Opposite.op n))
      (fun n ↦ (Rrings l Y).map (homOfLE (Nat.le_succ n)).op)
  let AX := WeilConjectures.SemilinearSections.systemRing
    (Scheme.ProEt.topology X) (fun n ↦ (Arings l E X).obj (Opposite.op n))
      (fun n ↦ (Arings l E X).map (homOfLE (Nat.le_succ n)).op)
  let PR := SheafOfModules.PullbackTensorCanonical.resolvingProperty (R := RY)
  let EY := cY.scalar.model.E.mapHomologicalComplex (.up ℤ)
  let EX := cX.scalar.model.E.mapHomologicalComplex (.up ℤ)
  let PY := d.pull.mapHomologicalComplex (.up ℤ)
  let PX := g.pull.mapHomologicalComplex (.up ℤ)
  let DY := g.pull.mapDerivedCategory
  let DX := d.pull.mapDerivedCategory
  let F := cY.scalar.T ⋙ DY
  let G := DX ⋙ cX.scalar.T
  let H := (PY ⋙ EX) ⋙ DerivedCategory.Q
  let a : EY ⋙ PX ≅ PY ⋙ EX :=
    Functor.mapHomologicalComplexCompIso α (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl _) (.up ℤ)).symm
  let v : DerivedCategory.Q ⋙ F ⟶ H :=
    (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight cY.scalar.model.ε DY ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft EY g.pull.mapDerivedCategoryFactors.hom ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight a.hom DerivedCategory.Q
  let t : DerivedCategory.Q ⋙ G ⟶ H :=
    (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight d.pull.mapDerivedCategoryFactors.hom cX.scalar.T ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft PY cX.scalar.model.ε ≫
      (Functor.associator _ _ _).inv
  have hv (P : PR.FullSubcategory) : IsIso (v.app P.obj) := by
    have := cY.scalar.model.computes P.obj P.property.1
    dsimp only [v, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.associator_hom_app]
    infer_instance
  have ht (P : PR.FullSubcategory) : IsIso (t.app P.obj) := by
    have := cX.scalar.model.computes (PY.obj P.obj)
      (hflat P.obj P.property.1 P.property.2)
    dsimp only [t, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.associator_hom_app]
    infer_instance
  let vi : PR.ι ⋙ (DerivedCategory.Q ⋙ F) ≅ PR.ι ⋙ H :=
    NatIso.ofComponents (fun P ↦ @asIso _ _ _ _ (v.app P.obj) (hv P))
      (fun f ↦ v.naturality f.hom)
  let ti : PR.ι ⋙ (DerivedCategory.Q ⋙ G) ≅ PR.ι ⋙ H :=
    NatIso.ofComponents (fun P ↦ @asIso _ _ _ _ (t.app P.obj) (ht P))
      (fun f ↦ t.naturality f.hom)
  let ee : (PR.ι ⋙ DerivedCategory.Q) ⋙ F ≅ (PR.ι ⋙ DerivedCategory.Q) ⋙ G :=
    Functor.associator _ _ _ ≪≫ vi ≪≫ ti.symm ≪≫ (Functor.associator _ _ _).symm
  obtain ⟨ff⟩ := SheafOfModules.PullbackTensorCanonical.resolving_fullyFaithful
    (R := RY) (S := AX)
  obtain ⟨P₀, _, hp₀, _⟩ :=
    SheafOfModules.PullbackTensorCanonical.exists_resolving (R := RY)
      (0 : CochainComplex (Systems Y (Rrings l Y)) ℤ)
  obtain ⟨z, hz⟩ := CategoryTheory.AlgebraDiagramPullback.unary_descent
    (PR.ι ⋙ DerivedCategory.Q) ⟨P₀, hp₀⟩ ff ee
  have hzflat (P : PR.FullSubcategory) :
      z.hom.app (DerivedCategory.Q.obj P.obj) ≫ t.app P.obj = v.app P.obj := by
    have h := congrArg Iso.hom (hz P)
    simp only [ee, NatIso.trans_app, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.comp_id] at h
    erw [Category.id_comp] at h
    change z.hom.app (DerivedCategory.Q.obj P.obj) =
      v.app P.obj ≫ @inv _ _ _ _ (t.app P.obj) (ht P) at h
    rw [h]
    have := ht P
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have heq : Functor.whiskerLeft DerivedCategory.Q z.hom ≫ t = v := by
    ext A
    obtain ⟨P, f, hp, hq⟩ :=
      SheafOfModules.PullbackTensorCanonical.exists_resolving (R := RY) A
    let : IsIso (DerivedCategory.Q.map f) :=
      Localization.inverts DerivedCategory.Q (HomologicalComplex.quasiIso _ _) f hq
    let w := Functor.whiskerLeft DerivedCategory.Q z.hom ≫ t
    apply (cancel_epi (F.mapIso (asIso (DerivedCategory.Q.map f))).hom).mp
    change (DerivedCategory.Q ⋙ F).map f ≫ w.app A =
      (DerivedCategory.Q ⋙ F).map f ≫ v.app A
    rw [w.naturality, v.naturality]
    change (z.hom.app (DerivedCategory.Q.obj P) ≫ t.app P) ≫ H.map f = _
    rw [hzflat ⟨P, hp⟩]
  have hsY := scalar_counit_shift l E cY
  have hsX := scalar_counit_shift l E cX
  let := hsY
  let := hsX
  have ha : NatTrans.CommShift a.hom ℤ := by
    have := SheafOfModules.RingedCoefficientProjection.complexComp_commShift α
    have := SheafOfModules.RingedCoefficientProjection.complexComp_commShift
      (Iso.refl (d.pull ⋙ cX.scalar.model.E))
    dsimp only [a, Iso.trans_hom, Iso.symm_hom]
    infer_instance
  let := ha
  have htshift : NatTrans.CommShift t ℤ := by dsimp only [t]; infer_instance
  have hvshift : NatTrans.CommShift v ℤ := by dsimp only [v]; infer_instance
  let := htshift
  have hwshift : NatTrans.CommShift (Functor.whiskerLeft DerivedCategory.Q z.hom ≫ t) ℤ := by
    rw [heq]
    exact hvshift
  let := hwshift
  have hshift : NatTrans.CommShift z.hom ℤ := by
    apply SheafOfModules.RingedCoefficientProjection.shift_of_dense_computation
      DerivedCategory.Q F G H t z.hom
    intro M
    let A := DerivedCategory.Q.objPreimage M
    obtain ⟨P, f, hp, hq⟩ :=
      SheafOfModules.PullbackTensorCanonical.exists_resolving (R := RY) A
    let : IsIso (DerivedCategory.Q.map f) :=
      Localization.inverts DerivedCategory.Q (HomologicalComplex.quasiIso _ _) f hq
    exact ⟨P, asIso (DerivedCategory.Q.map f) ≪≫
      DerivedCategory.Q.objObjPreimageIso M, ht ⟨P, hp⟩⟩
  refine ⟨z.hom, hshift, ?_⟩
  apply counit_square_single cY.scalar.model.E cX.scalar.model.E d.pull g.pull
    cY.scalar.T cX.scalar.T cY.scalar.model.ε cX.scalar.model.ε α z.hom
  intro K
  have h := NatTrans.congr_app heq K
  simp only [t, v, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app,
    Functor.associator_hom_app, Category.comp_id] at h
  repeat' erw [Category.id_comp] at h
  exact h

end AlgebraicGeometry.ProEtale.SpTowerClasses
