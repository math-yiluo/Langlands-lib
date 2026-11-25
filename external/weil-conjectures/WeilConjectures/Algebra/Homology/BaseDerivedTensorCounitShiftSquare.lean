/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence

/-! # The B-linear cohomological counit square under integer shift

Source: Stacks Project, Tags 05SU, 06Y6 and 08IB; the explicit square is an
explicit compatibility calculation for the ordinary shift model.
(blueprint: lem-pc-base-derived-tensor-counit-shift-square).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
open scoped TensorProduct ChangeOfRings
namespace ModuleCat

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} B)]

private theorem shiftHomology_nat
    (D T : CochainComplex (ModuleCat.{u} A) ℤ ⥤ DerivedCategory (ModuleCat.{u} B))
    [D.CommShift ℤ] [T.CommShift ℤ] (η : D ⟶ T) [NatTrans.CommShift η ℤ]
    (K L : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) (e : L ≅ K⟦-n⟧) (j : ℤ) :
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B)
    let δD := (H j).mapIso (D.mapIso e ≪≫ (D.commShiftIso (-n)).app K) ≪≫
      ((H 0).shiftIso (-n) j (j - n) (by omega)).app (D.obj K)
    let δT := (H j).mapIso (T.mapIso e ≪≫ (T.commShiftIso (-n)).app K) ≪≫
      ((H 0).shiftIso (-n) j (j - n) (by omega)).app (T.obj K)
    δD.hom ≫ (H (j - n)).map (η.app K) = (H j).map (η.app L) ≫ δT.hom := by
  have h := congrArg (fun f ↦ (DerivedCategory.homologyFunctor (ModuleCat.{u} B) 0).shiftMap
     f j (j - n) (show -n + j = j - n by omega))
      (ShiftedHom.map_naturality e.hom η)
  simp only [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp, Functor.shiftMap,
    ShiftedHom.map, Functor.map_comp, Category.assoc,
    Functor.shiftIso_hom_naturality] at h
  simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Functor.map_comp,
    Category.assoc, DerivedCategory.shift_homologyFunctor] using h


omit [HasDerivedCategory (ModuleCat.{u} B)] in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restriction_shiftMap_homology
    {E : Type u} [CommRing E] (g : B →+* E)
    (Q Q' : CochainComplex (ModuleCat.{u} E) ℤ) (n j k : ℤ) (h : n + j = k)
    (w : Q' ⟶ Q⟦n⟧) :
    let U : ModuleCat.{u} E ⥤ ModuleCat.{u} B := restrictScalars.{u} g
    let V : CochainComplex (ModuleCat.{u} E) ℤ ⥤
      CochainComplex (ModuleCat.{u} B) ℤ := U.mapHomologicalComplex (.up ℤ)
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℤ) 0).shiftMap
      (ShiftedHom.map w V) j k h ≫ ((Q.sc k).mapHomologyIso U).hom =
      ((Q'.sc j).mapHomologyIso U).hom ≫
        U.map ((HomologicalComplex.homologyFunctor (ModuleCat.{u} E) (.up ℤ) 0).shiftMap
           w j k h) := by
  intro U V
  let HB := HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℤ) j
  let HE := HomologicalComplex.homologyFunctor (ModuleCat.{u} E) (.up ℤ) j
  let shB := (CochainComplex.ShiftSequence.shiftIso (ModuleCat.{u} B) n j k h).hom.app
     (V.obj Q)
  let shE := (CochainComplex.ShiftSequence.shiftIso (ModuleCat.{u} E) n j k h).hom.app
     Q
  have hμ (Q : CochainComplex (ModuleCat.{u} E) ℤ) (j : ℤ) :
      (U.mapHomologicalComplexHomologyIso (.up ℤ) j).hom.app Q =
        ((Q.sc j).mapHomologyIso U).hom := by
    simp only [Functor.comp_obj, HomologicalComplex.homologyFunctor_obj,
      Functor.mapHomologicalComplexHomologyIso,
      Functor.mapHomologicalComplexCompShortComplexFunctorIso, Functor.isoWhiskerRight_refl,
      ShortComplex.homologyFunctorIso, Iso.refl_trans, Iso.trans_hom,
      Functor.isoWhiskerLeft_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
      NatTrans.comp_app, ShortComplex.homologyFunctor_obj, Functor.whiskerLeft_app,
      HomologicalComplex.homologyFunctorIso_hom_app, Functor.associator_inv_app,
      Functor.mapShortComplex_obj, Functor.associator_hom_app, NatIso.ofComponents_hom_app,
      Functor.whiskerRight_app, HomologicalComplex.homologyFunctorIso_inv_app,
      Category.id_comp]
    erw [Category.id_comp, U.map_id, Category.comp_id]
  have hshift := U.mapHomologicalComplexHomologyIso_hom_app_shiftIso n j k h Q
  change HB.map ((V.commShiftIso n).inv.app Q) ≫
    (U.mapHomologicalComplexHomologyIso (.up ℤ) j).hom.app (Q⟦n⟧) ≫ U.map shE =
      shB ≫ (U.mapHomologicalComplexHomologyIso (.up ℤ) k).hom.app Q at hshift
  have hshift' : (U.mapHomologicalComplexHomologyIso (.up ℤ) j).hom.app (Q⟦n⟧) ≫
      U.map shE = HB.map ((V.commShiftIso n).hom.app Q) ≫ shB ≫
        (U.mapHomologicalComplexHomologyIso (.up ℤ) k).hom.app Q := by
    rw [← hshift]
    simp only [← Category.assoc, ← HB.map_comp, Iso.hom_inv_id_app, HB.map_id,
      Category.id_comp]
  have hnat := (U.mapHomologicalComplexHomologyIso (.up ℤ) j).hom.naturality w
  dsimp only [Functor.comp_map, Functor.comp_obj] at hnat
  rw [← hμ, ← hμ]
  change (HB.map (V.map w ≫ (V.commShiftIso n).hom.app Q) ≫ shB) ≫
      (U.mapHomologicalComplexHomologyIso (.up ℤ) k).hom.app Q =
    (U.mapHomologicalComplexHomologyIso (.up ℤ) j).hom.app Q' ≫ U.map (HE.map w ≫ shE)
  rw [HB.map_comp, U.map_comp, ← Category.assoc _ _ (U.map shE), ← hnat]
  simp only [Category.assoc]
  rw [hshift']
set_option backward.isDefEq.respectTransparency true in
/-- The cohomological counit, before any tensor-algebra action is supplied, commutes
with the prescribed shift isomorphisms.
Source: Stacks Project, Tag 05SU (derived shift comparisons), Tag 06Y6 (derived
extension), and Tag 08IB (ordinary comparison). This precise diagram calculation
is the explicit part of step 3 of the ordinary shift model.

Proof: Restrict e to R and pass through the homotopy quotient and Qh. Naturality
of counit for this map gives the first comparison square. Its CommShift equation
gives the square for the shift of K. Apply derived B-homology in degree j and
compose with the homology shift to degree j-n. The homology factorization
isomorphisms for Qh and the homotopy quotient intertwine these shifts, by their
induced ShiftSequence structures. The ordinary tensor isomorphisms intertwine e
and shift: on b tensor x both sides send it to (1 tensor b) tensor e(x), and the
shift changes the differential by the same sign on both sides. The specified
generator formulas determine the ordinary isomorphisms, so this holds for the
supplied isomorphisms, not just chosen representatives. Finally restriction from
E to B is exact. Its homology comparison is natural and commutes with shift;
compose this square with the preceding ones. Their interior edges cancel to give
the displayed equality. No E-action, transported model, localized comparison,
flatness or invertibility of counit is used. For n=0 the shift edges are the unit
comparisons; zero complexes give the zero square; nonflat extensions cause no
problem because only restriction is required to preserve homology.
(blueprint: lem-pc-base-derived-tensor-counit-shift-square). -/
theorem baseDerivedTensor_counit_shift_square
    (derived : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} B))
    [derived.CommShift ℤ]
    (counit : DerivedCategory.Qh ⋙ derived ⟶
      (extendScalars.{u, u, u} (algebraMap R B)).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh)
    [NatTrans.CommShift counit ℤ]
    (K L : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) (e : L ≅ K⟦-n⟧) (j : ℤ)
    (ordinaryIsoK :
      ((extendScalars.{u, u, u} (algebraMap R B)).mapHomologicalComplex (.up ℤ)).obj
        (((restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex (.up ℤ)).obj K) ≅
      ((restrictScalars.{u} Algebra.TensorProduct.includeRight.toRingHom).mapHomologicalComplex
        (.up ℤ)).obj
          (((extendScalars.{u, u, u} (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
            (.up ℤ)).obj K))
    (ordinaryIsoK_tmul : ∀ (k : ℤ) (b : B) (x : K.X k),
      ordinaryIsoK.hom.f k (b ⊗ₜ[R,algebraMap R B] x) =
        Algebra.TensorProduct.includeRight b ⊗ₜ[A,algebraMap A (A ⊗[R] B)] x)
    (ordinaryIsoL :
      ((extendScalars.{u, u, u} (algebraMap R B)).mapHomologicalComplex (.up ℤ)).obj
        (((restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex (.up ℤ)).obj L) ≅
      ((restrictScalars.{u} Algebra.TensorProduct.includeRight.toRingHom).mapHomologicalComplex
        (.up ℤ)).obj
          (((extendScalars.{u, u, u} (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
            (.up ℤ)).obj L))
    (ordinaryIsoL_tmul : ∀ (k : ℤ) (b : B) (x : L.X k),
      ordinaryIsoL.hom.f k (b ⊗ₜ[R,algebraMap R B] x) =
        Algebra.TensorProduct.includeRight b ⊗ₜ[A,algebraMap A (A ⊗[R] B)] x) :
    let S := (restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex (.up ℤ)
    let G := (extendScalars.{u, u, u} (algebraMap R B)).mapHomologicalComplex (.up ℤ)
    let F := (extendScalars.{u, u, u} (algebraMap A (A ⊗[R] B))).mapHomologicalComplex (.up ℤ)
    let U := restrictScalars.{u}
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom
    let πR := HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)
    let πB := HomotopyCategory.quotient (ModuleCat.{u} B) (.up ℤ)
    let D := S ⋙ πR ⋙ DerivedCategory.Qh ⋙ derived
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B)
    let δ := (H j).mapIso (D.mapIso e ≪≫ (D.commShiftIso (-n)).app K) ≪≫
      ((H 0).shiftIso (-n) j (j - n) (by omega)).app (D.obj K)
    let ε := (HomologicalComplex.homologyFunctor (ModuleCat.{u} (A ⊗[R] B))
      (.up ℤ) j).mapIso (F.mapIso e ≪≫ (F.commShiftIso (-n)).app K) ≪≫
      (CochainComplex.ShiftSequence.shiftIso (ModuleCat.{u} (A ⊗[R] B)) (-n) j (j - n)
        (by omega)).app (F.obj K)
    let cK := (H (j - n)).map (counit.app (πR.obj (S.obj K))) ≫
      (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u} B) (j - n)).hom.app
        (πB.obj (G.obj (S.obj K))) ≫
      (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B) (.up ℤ) (j - n)).hom.app
        (G.obj (S.obj K)) ≫ HomologicalComplex.homologyMap ordinaryIsoK.hom (j - n) ≫
      (((F.obj K).sc (j - n)).mapHomologyIso U).hom
    let cL := (H j).map (counit.app (πR.obj (S.obj L))) ≫
      (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u} B) j).hom.app
        (πB.obj (G.obj (S.obj L))) ≫
      (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B) (.up ℤ) j).hom.app
        (G.obj (S.obj L)) ≫ HomologicalComplex.homologyMap ordinaryIsoL.hom j ≫
      (((F.obj L).sc j).mapHomologyIso U).hom
    δ.hom ≫ cK = cL ≫ U.map ε.hom := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  intro S G F U πR πB D H δ ε cK cL
  let GH := (extendScalars.{u, u, u} (algebraMap R B)).mapHomotopyCategory (.up ℤ)
  let T := S ⋙ G ⋙ πB ⋙ DerivedCategory.Qh
  let η : D ⟶ T := Functor.whiskerLeft S
    (Functor.whiskerLeft πR counit ≫
      (Functor.associator πR GH DerivedCategory.Qh).inv ≫
      Functor.whiskerRight
        ((extendScalars.{u, u, u} (algebraMap R B)).mapHomotopyCategoryFactors (.up ℤ)).hom
        DerivedCategory.Qh ≫ (Functor.associator G πB DerivedCategory.Qh).hom)
  have : NatTrans.CommShift η ℤ := by dsimp [η, GH]; infer_instance
  have hη := shiftHomology_nat A B D T η K L n e j
  let δT := (H j).mapIso (T.mapIso e ≪≫ (T.commShiftIso (-n)).app K) ≪≫
    ((H 0).shiftIso (-n) j (j - n) (by omega)).app (T.obj K)
  let ρ (X : CochainComplex (ModuleCat.{u} A) ℤ) (k : ℤ) :=
    (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u} B) k).app
      (πB.obj (G.obj (S.obj X))) ≪≫
    (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B) (.up ℤ) k).app
      (G.obj (S.obj X))
  have hT : δT.hom ≫ (ρ K (j - n)).hom = (ρ L j).hom ≫
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℤ) 0).shiftMap
        (ShiftedHom.map e.hom (S ⋙ G)) j (j - n) (by omega) := by
    have h := DerivedCategory.shiftMap_homologyFunctor_map_Qh
      (ShiftedHom.map (ShiftedHom.map e.hom (S ⋙ G)) πB) j (j - n) (by omega)
    rw [HomotopyCategory.homologyFunctor_shiftMap] at h
    have hc : ShiftedHom.map (ShiftedHom.map (ShiftedHom.map e.hom (S ⋙ G)) πB)
        DerivedCategory.Qh = ShiftedHom.map e.hom T := by
      simp only [ShiftedHom.map, T, Functor.commShiftIso_comp_hom_app, Functor.comp_map,
        CategoryTheory.Functor.map_comp, Category.assoc]
      rfl
    rw [hc] at h
    change (H 0).shiftMap (ShiftedHom.map e.hom T) j (j - n) (by omega) =
      (ρ L j).hom ≫
        (HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℤ) 0).shiftMap
          (ShiftedHom.map e.hom (S ⋙ G)) j (j - n) (by omega) ≫ (ρ K (j - n)).inv at h
    have h' := congrArg (fun f ↦ f ≫ (ρ K (j - n)).hom) h
    change δT.hom ≫ (ρ K (j - n)).hom =
      ((ρ L j).hom ≫
        (HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℤ) 0).shiftMap
          (ShiftedHom.map e.hom (S ⋙ G)) j (j - n) (by omega) ≫
          (ρ K (j - n)).inv) ≫ (ρ K (j - n)).hom at h'
    simp only [Category.assoc] at h'
    erw [(ρ K (j - n)).inv_hom_id, Category.comp_id] at h'
    exact h'
  have hηapp (X : CochainComplex (ModuleCat.{u} A) ℤ) :
      η.app X = counit.app (πR.obj (S.obj X)) := by
    simp only [η, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_inv_app, Functor.associator_hom_app]
    change counit.app (πR.obj (S.obj X)) ≫ 𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _) ≫
      𝟙 _ = counit.app (πR.obj (S.obj X))
    simp only [CategoryTheory.Functor.map_id, Category.id_comp]
    erw [Category.id_comp, Category.comp_id]
  let V := U.mapHomologicalComplex (.up ℤ)
  have ho : ShiftedHom.map e.hom (S ⋙ G) ≫ (ordinaryIsoK.hom)⟦-n⟧' =
      ordinaryIsoL.hom ≫ ShiftedHom.map (ShiftedHom.map e.hom F) V := by
    apply HomologicalComplex.Hom.ext
    funext k
    apply ExtendScalars.hom_ext
    intro x
    change ordinaryIsoK.hom.f (k + -n)
      ((extendScalars (algebraMap R B)).map ((restrictScalars (algebraMap R A)).map
        (e.hom.f k)) ((1 : B) ⊗ₜ[R, _] x)) =
      (U.map ((extendScalars (algebraMap A (A ⊗[R] B))).map (e.hom.f k)))
        (ordinaryIsoL.hom.f k ((1 : B) ⊗ₜ[R, _] x))
    erw [ExtendScalars.map_tmul, ordinaryIsoK_tmul, ordinaryIsoL_tmul]
    change Algebra.TensorProduct.includeRight (1 : B) ⊗ₜ[A, _] (e.hom.f k x) =
      (extendScalars (algebraMap A (A ⊗[R] B))).map (e.hom.f k)
        (Algebra.TensorProduct.includeRight (1 : B) ⊗ₜ[A, _] x)
    erw [ExtendScalars.map_tmul]
  have hbase : δ.hom ≫ (H (j - n)).map (counit.app (πR.obj (S.obj K))) ≫
      (ρ K (j - n)).hom =
      (H j).map (counit.app (πR.obj (S.obj L))) ≫ (ρ L j).hom ≫
        (HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℤ) 0).shiftMap
          (ShiftedHom.map e.hom (S ⋙ G)) j (j - n) (by omega) := by
    have h := congrArg (fun f ↦ f ≫ (ρ K (j - n)).hom) hη
    change (δ.hom ≫ (H (j - n)).map (η.app K)) ≫ (ρ K (j - n)).hom =
      ((H j).map (η.app L) ≫ δT.hom) ≫ (ρ K (j - n)).hom at h
    rw [hηapp K, hηapp L] at h
    simp only [Category.assoc] at h
    rw [hT] at h
    exact h
  have hO := congrArg (fun f ↦
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℤ) 0).shiftMap
      f j (j - n) (show -n + j = j - n by omega)) ho
  rw [Functor.shiftMap_comp, Functor.shiftMap_comp'] at hO
  have hV := restriction_shiftMap_homology B
    (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom
    (F.obj K) (F.obj L) (-n) j (j - n) (by omega) (ShiftedHom.map e.hom F)
  have hordinary :
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℤ) 0).shiftMap
        (ShiftedHom.map e.hom (S ⋙ G)) j (j - n) (by omega) ≫
        HomologicalComplex.homologyMap ordinaryIsoK.hom (j - n) ≫
        (((F.obj K).sc (j - n)).mapHomologyIso U).hom =
      HomologicalComplex.homologyMap ordinaryIsoL.hom j ≫
        (((F.obj L).sc j).mapHomologyIso U).hom ≫ U.map ε.hom := by
    have h := congrArg (fun f ↦ f ≫ (((F.obj K).sc (j - n)).mapHomologyIso U).hom) hO
    change ((HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℤ) 0).shiftMap
        (ShiftedHom.map e.hom (S ⋙ G)) j (j - n) (by omega) ≫
        HomologicalComplex.homologyMap ordinaryIsoK.hom (j - n)) ≫
        (((F.obj K).sc (j - n)).mapHomologyIso U).hom =
      (HomologicalComplex.homologyMap ordinaryIsoL.hom j ≫
        (HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℤ) 0).shiftMap
          (ShiftedHom.map (ShiftedHom.map e.hom F) V) j (j - n) (by omega)) ≫
        (((F.obj K).sc (j - n)).mapHomologyIso U).hom at h
    change (HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℤ) 0).shiftMap
        (ShiftedHom.map (ShiftedHom.map e.hom F) V) j (j - n) (by omega) ≫
        (((F.obj K).sc (j - n)).mapHomologyIso U).hom =
      (((F.obj L).sc j).mapHomologyIso U).hom ≫ U.map ε.hom at hV
    simp only [Category.assoc] at h
    rw [hV] at h
    exact h
  change δ.hom ≫ (H (j - n)).map (counit.app (πR.obj (S.obj K))) ≫
      (ρ K (j - n)).hom ≫ HomologicalComplex.homologyMap ordinaryIsoK.hom (j - n) ≫
        (((F.obj K).sc (j - n)).mapHomologyIso U).hom =
    ((H j).map (counit.app (πR.obj (S.obj L))) ≫ (ρ L j).hom ≫
      HomologicalComplex.homologyMap ordinaryIsoL.hom j ≫
        (((F.obj L).sc j).mapHomologyIso U).hom) ≫ U.map ε.hom
  rw [reassoc_of% hbase]
  simp only [Category.assoc]
  erw [hordinary]

end ModuleCat
