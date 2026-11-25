/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.RationalP1ScalarChernMaps
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceComparisonLimitIsos
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.Presentation.DiagonalCompletedChernLift
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceTwistedSplittingComponents
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryReflectsIso

/-! # Splitting off a normalized completed Chern adjunct
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

private theorem map_split
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F : C ⥤ D) [F.Additive] {U V K : C} (a : U ⟶ K) (b : V ⟶ K)
    [IsIso (biprod.desc a b)] {U' V' K' : D}
    (u : F.obj U ≅ U') (v : F.obj V ≅ V') (k : F.obj K ≅ K') :
    IsIso (biprod.desc (u.inv ≫ F.map a ≫ k.hom) (v.inv ≫ F.map b ≫ k.hom)) := by
  let : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBiproducts F
  have he : biprod.desc (u.inv ≫ F.map a ≫ k.hom) (v.inv ≫ F.map b ≫ k.hom) =
      (biprod.mapIso u.symm v.symm).hom ≫ (F.mapBiprod U V).inv ≫
        F.map (biprod.desc a b) ≫ k.hom := by
    rw [← Category.assoc (F.mapBiprod U V).inv (F.map (biprod.desc a b)) k.hom,
      biprod.mapBiprod_inv_map_desc]
    apply biprod.hom_ext' <;>
      simp only [biprod.inl_desc, biprod.inr_desc, biprod.inl_desc_assoc,
        biprod.inr_desc_assoc, biprod.mapIso_hom,
        Iso.symm_hom, biprod.inl_map_assoc, biprod.inr_map_assoc]
  rw [he]
  infer_instance

/-- The completed line remains scalar-orthogonal after shifting by two. -/
private theorem completed_line_shift_complete (l : ℕ) [Fact l.Prime] (S : Scheme.{u})
    [IsNoetherian S] [DiagonalTraceLocalizations l S] (hS : IsUnit (l : Γ(S, ⊤))) :
    ∀ V : DerivedCategory (DiagonalMod l S), IsIso (l • 𝟙 V) →
      Subsingleton (V ⟶ (diagonalCompletedUnderlying l S).obj
        ((DiagonalTrace.completedLine l S) ⟦(2 : ℤ)⟧)) := by
  let : ∀ x : S, Invertible (l : S.residueField x) := fun x ↦
    (show IsUnit (l : S.residueField x) from by
      let ψ := (S.residue x).hom.comp (S.presheaf.germ ⊤ x trivial).hom
      simpa only [map_natCast] using hS.map ψ).invertible
  have hfree := (Scheme.pur_twist_sheaf_locally_free.{u, u} S l
    (ULift.{u} (Padic l))).2.1.2.1
  have hline := DiagonalTrace.diagonalCompletedLine_complete l S _ hfree
  let G := diagonalCompletedUnderlying l S
  let adj : shiftFunctor (DerivedCategory (DiagonalMod l S)) (-2 : ℤ) ⊣
      shiftFunctor (DerivedCategory (DiagonalMod l S)) (2 : ℤ) :=
    (shiftEquiv' (DerivedCategory (DiagonalMod l S)) (-2 : ℤ) (2 : ℤ)
      (by decide)).toAdjunction
  have hshift := DiagonalTrace.complete_rightAdjoint adj l
    (G.obj (DiagonalTrace.completedLine l S)) hline
  intro V hV
  let e := Iso.homCongr (Iso.refl V)
    ((G.commShiftIso (2 : ℤ)).app (DiagonalTrace.completedLine l S))
  constructor
  intro a b
  apply e.injective
  exact @Subsingleton.elim _ (hshift V hV) (e a) (e b)

-- The derived biproduct structure on completed coefficients is found by unfolding.
/-- A normalized completed Chern adjunct is the second component of a splitting. -/
theorem completed_chern_splitting
    (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian S]
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    {f : X ⟶ S} (t : DiagonalTrace.Result l (ULift.{u} (Padic l)) f)
    (hS : IsUnit (l : Γ(S, ⊤)))
    (b : DiagonalTrace.completedUnit l S ⟶
      t.Rc.R.obj ((DiagonalTrace.completedLine l X) ⟦(2 : ℤ)⟧))
    (hb : CompletedChernNormalized l t.toPresentation b) :
    ∃ v : (DiagonalTrace.completedLine l S) ⟦(2 : ℤ)⟧ ⟶
        t.Rc.R.obj ((DiagonalTrace.completedLine l X) ⟦(2 : ℤ)⟧),
      IsIso (biprod.desc v b) := by
  let E := ULift.{u} (Padic l)
  let p := t.toPresentation
  let m := p.model
  let T := p.twistS.T l E ⋙
    shiftFunctor (SpTowerClasses.D S (SpTowerClasses.Arings l E S)) (2 : ℤ)
  let a := (shiftFunctor (SpTowerClasses.D S (SpTowerClasses.Arings l E S))
    (2 : ℤ)).mapIso (p.twistS.positiveUnit l E).symm
  let z := (shiftFunctor (SpTowerClasses.D S (SpTowerClasses.Arings l E S))
      (2 : ℤ)).mapIso
        (((p.twistS.T l E).commShiftIso (-2 : ℤ)).app
          (SpTowerClasses.inverseLine l E p.chernS)) ≪≫
    (shiftFunctorCompIsoId (SpTowerClasses.D S (SpTowerClasses.Arings l E S))
      (-2 : ℤ) 2 (by decide)).app
        ((p.twistS.T l E).obj (SpTowerClasses.inverseLine l E p.chernS)) ≪≫
    p.twistS.contract l E
  obtain ⟨_, hu, hc⟩ := DiagonalTrace.diagonalTrace_twistedSplitting_components l p hS
  have hbq : IsIso (biprod.desc (SpTowerClasses.unitArrow l E m.coefficientPullback)
      (m.second l E)) := t.split
  change m.twistedUnit l E = a.hom ≫ T.map biprod.inl ≫ T.map (m.bq l E) ≫
    (m.twistedPush l E).hom at hu
  change m.chernAdjoint l E = z.inv ≫ T.map biprod.inr ≫ T.map (m.bq l E) ≫
    (m.twistedPush l E).hom at hc
  rw [← Functor.map_comp_assoc, DiagonalTrace.Model.bq, biprod.inl_desc] at hu
  rw [← Functor.map_comp_assoc, DiagonalTrace.Model.bq, biprod.inr_desc] at hc
  have hs : IsIso (biprod.desc (m.twistedUnit l E) (m.chernAdjoint l E)) := by
    have := map_split T (SpTowerClasses.unitArrow l E m.coefficientPullback)
      (m.second l E) a.symm z (m.twistedPush l E)
    simpa only [hu, hc, Iso.symm_inv] using this
  let F := p.restrictionS.F.mapDerivedCategory ⋙ p.LS.R
  let G := diagonalCompletedUnderlying l S
  have : p.LS.R.IsTriangulated := p.LS.triangulated
  let : ∀ x : S, Invertible (l : S.residueField x) := fun x ↦
    (show IsUnit (l : S.residueField x) from by
      let ψ := (S.residue x).hom.comp (S.presheaf.germ ⊤ x trivial).hom
      simpa only [map_natCast] using hS.map ψ).invertible
  have : IsIso (p.coefficientsS.lineMap l E p.LS) :=
    DiagonalTrace.lineComparison_isIso l E p.coefficientsS p.LS
  have := p.unit_limit
  have := p.line_limit
  let v₀ := DiagonalTrace.shiftedComparison G F (p.coefficientsS.lineMap l E p.LS) 2
  let u₀ := p.coefficientsS.unitMap l E p.LS
  let k₀ := p.sourceMap l E ≫ p.LS.R.map (p.varying.inv.app _)
  have : IsIso v₀ := by dsimp [v₀, DiagonalTrace.shiftedComparison]; infer_instance
  have : IsIso k₀ := by
    dsimp [k₀, DiagonalTrace.Presentation.sourceMap, DiagonalTrace.shiftedComparison]
    infer_instance
  let v := v₀ ≫ F.map (m.twistedUnit l E) ≫ inv k₀
  have hb' : G.map b = u₀ ≫ F.map (m.chernAdjoint l E) ≫ inv k₀ := by
    have hb₀ : G.map b ≫ p.sourceMap l E = u₀ ≫ p.LS.R.map (p.systemChern l) := hb
    apply (cancel_mono k₀).mp
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    change G.map b ≫ (p.sourceMap l E ≫ p.LS.R.map (p.varying.inv.app _)) =
      u₀ ≫ p.LS.R.map (p.restrictionS.F.mapDerivedCategory.map (m.chernAdjoint l E))
    rw [← Category.assoc, hb₀, Category.assoc, ← p.LS.R.map_comp]
    congr 1
    apply congrArg p.LS.R.map
    unfold DiagonalTrace.Presentation.systemChern
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun z ↦ p.restrictionS.F.mapDerivedCategory.map
        (m.chernAdjoint l E) ≫ z) (p.varying.hom_inv_id_app _)).trans
        (Category.comp_id _))
  have hvb : IsIso (biprod.desc v (G.map b)) := by
    rw [hb']
    exact map_split F (m.twistedUnit l E) (m.chernAdjoint l E)
      (asIso v₀).symm (asIso u₀).symm (asIso k₀).symm
  -- Lift only on the full subcategory of derived-complete objects.
  let P : ObjectProperty (DerivedCategory (DiagonalCompleted l S)) := fun M ↦
    ∀ V : DerivedCategory (DiagonalMod l S), IsIso (l • 𝟙 V) → Subsingleton (V ⟶ G.obj M)
  obtain ⟨ff⟩ := DiagonalTrace.diagonalCompleteScalarRestrictionCore l S
  have hV : P ((DiagonalTrace.completedLine l S) ⟦(2 : ℤ)⟧) :=
    completed_line_shift_complete l S hS
  have hX : IsUnit (l : Γ(X, ⊤)) := by
    simpa only [map_natCast] using hS.map f.appTop.hom
  let GX := diagonalCompletedUnderlying l X
  have hline := completed_line_shift_complete l X hX
  have hK : P (p.Rc.R.obj ((DiagonalTrace.completedLine l X) ⟦(2 : ℤ)⟧)) := by
    let adj := (ProEtale.upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f).mapDerivedCategoryRightDerivedAdjunction
    have hpush := DiagonalTrace.complete_rightAdjoint adj l _ hline
    let e := DiagonalTrace.rightDerivedComparison _ p.Rf
    intro V hV
    let i := (p.completed.iso.app ((DiagonalTrace.completedLine l X) ⟦(2 : ℤ)⟧)) ≪≫
      e.app (GX.obj ((DiagonalTrace.completedLine l X) ⟦(2 : ℤ)⟧))
    have := hpush V hV
    exact (Iso.homCongr (Iso.refl V) i).injective.subsingleton
  let A : P.FullSubcategory := ⟨_, hV⟩
  let B : P.FullSubcategory := ⟨_, hK⟩
  obtain ⟨v', hv'⟩ := ff.map_surjective (X := A) (Y := B) v
  change G.map v'.hom = v at hv'
  refine ⟨v'.hom, ?_⟩
  have hfaith : (diagonalCompletedRestriction l S).Faithful := ⟨by
    intro M N f g h
    ext U x
    exact congrArg (fun k ↦ (k.hom.app U).hom x) h⟩
  have hreflect : G.ReflectsIsomorphisms := inferInstance
  let : PreservesBinaryBiproducts G :=
    preservesBinaryBiproducts_of_preservesBiproducts G
  have he : G.map (biprod.desc v'.hom b) =
      (G.mapBiprod _ _).hom ≫ biprod.desc v (G.map b) := by
    rw [← hv', biprod.mapBiprod_hom_desc]
  have : IsIso (G.map (biprod.desc v'.hom b)) := by rw [he]; infer_instance
  exact isIso_of_reflects_iso _ G

attribute [local irreducible] derivedScalars Functor.mapDerivedCategory RestrictionSquare.mate
attribute [local irreducible] CompletedRealization.singleUnit CompletedRealization.shiftedLine

private theorem realize_splitting (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}}
    (f : X ⟶ S) [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    (eX : CompletedRealization l X) (eS : CompletedRealization l S)
    (R : DiagonalRightDerived (diagonalTracePush l f))
    (R' : DiagonalRightDerived
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f))
    (s : CompletedPushSquare l f eX eS R R')
    (b : DiagonalTrace.completedUnit l S ⟶
      R.R.obj ((DiagonalTrace.completedLine l X) ⟦(2 : ℤ)⟧))
    (h : ∃ v : (DiagonalTrace.completedLine l S) ⟦(2 : ℤ)⟧ ⟶
      R.R.obj ((DiagonalTrace.completedLine l X) ⟦(2 : ℤ)⟧), IsIso (biprod.desc v b)) :
    ∃ v : ((DerivedCategory.singleFunctor
        (Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) S) 0).obj (zlLine l S))
          ⟦(2 : ℤ)⟧ ⟶
      R'.R.obj (((DerivedCategory.singleFunctor
        (Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) X) 0).obj (zlLine l X))
          ⟦(2 : ℤ)⟧),
      IsIso (biprod.desc v (realizeScalarChern l f eX eS R R' s b)) := by
  obtain ⟨v, hv⟩ := h
  have : IsIso (eS.singleUnit l S) := by
    unfold CompletedRealization.singleUnit
    infer_instance
  have : IsIso (eS.shiftedLine l S) := by
    unfold CompletedRealization.shiftedLine
    infer_instance
  have : IsIso (eX.shiftedLine l X) := by
    unfold CompletedRealization.shiftedLine
    infer_instance
  let k := s.derived.iso.hom.app _ ≫ R'.R.map (eX.shiftedLine l X)
  have : IsIso k := by dsimp only [k]; infer_instance
  refine ⟨inv (eS.shiftedLine l S) ≫ eS.F.mapDerivedCategory.map v ≫ k, ?_⟩
  unfold realizeScalarChern
  simpa only [asIso_hom, asIso_inv, k, Category.assoc] using
    map_split eS.F.mapDerivedCategory v b (asIso (eS.shiftedLine l S))
      (asIso (eS.singleUnit l S)) (asIso k)

private theorem extend_splitting
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] {X S : Scheme.{u}} (f : X ⟶ S)
    {M : Modules Λ X} {M' : Modules Λ' X} {m : M.X ⟶ M'.X}
    {N : Modules Λ S} {N' : Modules Λ' S} {n : N.X ⟶ N'.X}
    (cU : Endpoint a (Mod.regular (condensedRingObj Λ S))
      (Mod.regular (condensedRingObj Λ' S)) (coefficientMap a S))
    (cL : Endpoint a M M' m) (cS : Endpoint a N N' n)
    (R : DiagonalRightDerived (CondensedRing.lowerStar Λ f))
    (R' : DiagonalRightDerived (CondensedRing.lowerStar Λ' f))
    (s : RestrictionSquare a f R R')
    (hs : IsIso ((s.mate a).app
      (((DerivedCategory.singleFunctor (Modules Λ X) 0).obj M) ⟦(2 : ℤ)⟧)))
    (b : unit Λ S ⟶ R.R.obj
      (((DerivedCategory.singleFunctor (Modules Λ X) 0).obj M) ⟦(2 : ℤ)⟧))
    (h : ∃ v : ((DerivedCategory.singleFunctor (Modules Λ S) 0).obj N) ⟦(2 : ℤ)⟧ ⟶
        R.R.obj (((DerivedCategory.singleFunctor (Modules Λ X) 0).obj M) ⟦(2 : ℤ)⟧),
      IsIso (biprod.desc v b)) :
    ∃ v : ((DerivedCategory.singleFunctor (Modules Λ' S) 0).obj N') ⟦(2 : ℤ)⟧ ⟶
        R'.R.obj (((DerivedCategory.singleFunctor (Modules Λ' X) 0).obj M') ⟦(2 : ℤ)⟧),
      IsIso (biprod.desc v (extendScalarChern a f cU cL R R' s b)) := by
  obtain ⟨v, hv⟩ := h
  have : (derivedScalars a S).Additive := by
    unfold derivedScalars
    exact (Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap a S)).left_adjoint_additive
  have : IsIso (cL.shift a) := by unfold Endpoint.shift; infer_instance
  have : IsIso (cS.shift a) := by unfold Endpoint.shift; infer_instance
  let k := (s.mate a).app _ ≫ R'.R.map (cL.shift a)
  have : IsIso k := by dsimp only [k]; infer_instance
  refine ⟨inv (cS.shift a) ≫ (derivedScalars a S).map v ≫ k, ?_⟩
  unfold extendScalarChern
  simpa only [asIso_hom, asIso_inv, k, Category.assoc] using
    map_split (derivedScalars a S) v b (asIso (cS.shift a)) cU.iso (asIso k)

private theorem postcompose_splitting
    {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
    {V U K K' : C} (b : U ⟶ K) (h : ∃ v : V ⟶ K, IsIso (biprod.desc v b))
    (e : K ≅ K') : ∃ v : V ⟶ K', IsIso (biprod.desc v (b ≫ e.hom)) := by
  obtain ⟨v, hv⟩ := h
  refine ⟨v ≫ e.hom, ?_⟩
  have he : biprod.desc (v ≫ e.hom) (b ≫ e.hom) = biprod.desc v b ≫ e.hom := by
    apply biprod.hom_ext'
    · rw [biprod.inl_desc, biprod.inl_desc_assoc]
    · rw [biprod.inr_desc, biprod.inr_desc_assoc]
  rw [he]
  infer_instance

end AlgebraicGeometry.ProEtale.RationalP1
