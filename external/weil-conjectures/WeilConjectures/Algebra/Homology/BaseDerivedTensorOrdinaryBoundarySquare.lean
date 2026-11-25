/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence

/-! # The ordinary derived counit boundary square

Source: Stacks Project, Tag 06Y6, Lemma 15.61.1.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
open scoped TensorProduct ChangeOfRings
namespace ModuleCat

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restriction_shiftMap_homology
    (B : Type u) [CommRing B]
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

private theorem shifted_counit_naturality
    (A B : Type u) [CommRing A] [CommRing B]
    [HasDerivedCategory (ModuleCat.{u} B)]
    (D E : CochainComplex (ModuleCat.{u} A) ℤ ⥤ DerivedCategory (ModuleCat.{u} B))
    [D.CommShift ℤ] [E.CommShift ℤ] (η : D ⟶ E) [NatTrans.CommShift η ℤ]
    (K L : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) (f : L ⟶ K⟦n⟧) (j : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} B) 0).shiftMap
        (ShiftedHom.map f D) j (j + n) (by omega) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} B) (j + n)).map (η.app K) =
    (DerivedCategory.homologyFunctor (ModuleCat.{u} B) j).map (η.app L) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} B) 0).shiftMap
        (ShiftedHom.map f E) j (j + n) (by omega) := by
  have h := congrArg (fun a ↦ (DerivedCategory.homologyFunctor
    (ModuleCat.{u} B) 0).shiftMap a j (j + n) (show n + j = j + n by omega))
      (ShiftedHom.map_naturality f η)
  simp only [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp, Functor.shiftMap,
    ShiftedHom.map, Functor.map_comp, Category.assoc,
    Functor.shiftIso_hom_naturality] at h
  simpa only [Functor.shiftMap, ShiftedHom.map, Functor.map_comp, Category.assoc,
    Functor.shiftIso_hom_naturality, DerivedCategory.shift_homologyFunctor] using h

private theorem counit_shifted_map_square
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} B)]
    (derived : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} B))
    [derived.CommShift ℤ]
    (counit : DerivedCategory.Qh ⋙ derived ⟶
      (extendScalars.{u, u, u} (algebraMap R B)).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh)
    [NatTrans.CommShift counit ℤ]
    (K L : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) (f : L ⟶ K⟦n⟧) (j : ℤ)
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
    let δ := (H 0).shiftMap (ShiftedHom.map f D) j (j + n) (by omega)
    let ε := (HomologicalComplex.homologyFunctor (ModuleCat.{u} (A ⊗[R] B))
      (.up ℤ) 0).shiftMap (ShiftedHom.map f F) j (j + n) (by omega)
    let cK := (H (j + n)).map (counit.app (πR.obj (S.obj K))) ≫
      (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u} B) (j + n)).hom.app
        (πB.obj (G.obj (S.obj K))) ≫
      (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B) (.up ℤ) (j + n)).hom.app
        (G.obj (S.obj K)) ≫ HomologicalComplex.homologyMap ordinaryIsoK.hom (j + n) ≫
      (((F.obj K).sc (j + n)).mapHomologyIso U).hom
    let cL := (H j).map (counit.app (πR.obj (S.obj L))) ≫
      (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u} B) j).hom.app
        (πB.obj (G.obj (S.obj L))) ≫
      (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B) (.up ℤ) j).hom.app
        (G.obj (S.obj L)) ≫ HomologicalComplex.homologyMap ordinaryIsoL.hom j ≫
      (((F.obj L).sc j).mapHomologyIso U).hom
    δ ≫ cK = cL ≫ U.map ε := by
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
  have hη := shifted_counit_naturality A B D T η K L n f j
  let δT := (H 0).shiftMap (ShiftedHom.map f T) j (j + n) (by omega)
  let ρ (X : CochainComplex (ModuleCat.{u} A) ℤ) (k : ℤ) :=
    (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u} B) k).app
      (πB.obj (G.obj (S.obj X))) ≪≫
    (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B) (.up ℤ) k).app
      (G.obj (S.obj X))
  have hT : δT ≫ (ρ K (j + n)).hom = (ρ L j).hom ≫
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℤ) 0).shiftMap
        (ShiftedHom.map f (S ⋙ G)) j (j + n) (by omega) := by
    have h := DerivedCategory.shiftMap_homologyFunctor_map_Qh
      (ShiftedHom.map (ShiftedHom.map f (S ⋙ G)) πB) j (j + n) (by omega)
    rw [HomotopyCategory.homologyFunctor_shiftMap] at h
    have hc : ShiftedHom.map (ShiftedHom.map (ShiftedHom.map f (S ⋙ G)) πB)
        DerivedCategory.Qh = ShiftedHom.map f T := by
      simp only [ShiftedHom.map, T, Functor.commShiftIso_comp_hom_app, Functor.comp_map,
        CategoryTheory.Functor.map_comp, Category.assoc]
      rfl
    rw [hc] at h
    change (H 0).shiftMap (ShiftedHom.map f T) j (j + n) (by omega) =
      (ρ L j).hom ≫
        (HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℤ) 0).shiftMap
          (ShiftedHom.map f (S ⋙ G)) j (j + n) (by omega) ≫ (ρ K (j + n)).inv at h
    have h' := congrArg (fun f ↦ f ≫ (ρ K (j + n)).hom) h
    change δT ≫ (ρ K (j + n)).hom =
      ((ρ L j).hom ≫
        (HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℤ) 0).shiftMap
          (ShiftedHom.map f (S ⋙ G)) j (j + n) (by omega) ≫
          (ρ K (j + n)).inv) ≫ (ρ K (j + n)).hom at h'
    simp only [Category.assoc] at h'
    erw [(ρ K (j + n)).inv_hom_id, Category.comp_id] at h'
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
  have ho : ShiftedHom.map f (S ⋙ G) ≫ (ordinaryIsoK.hom)⟦n⟧' =
      ordinaryIsoL.hom ≫ ShiftedHom.map (ShiftedHom.map f F) V := by
    apply HomologicalComplex.Hom.ext
    funext k
    apply ExtendScalars.hom_ext
    intro x
    change ordinaryIsoK.hom.f (k + n)
      ((extendScalars (algebraMap R B)).map ((restrictScalars (algebraMap R A)).map
        (f.f k)) ((1 : B) ⊗ₜ[R, _] x)) =
      (U.map ((extendScalars (algebraMap A (A ⊗[R] B))).map (f.f k)))
        (ordinaryIsoL.hom.f k ((1 : B) ⊗ₜ[R, _] x))
    erw [ExtendScalars.map_tmul, ordinaryIsoK_tmul, ordinaryIsoL_tmul]
    change Algebra.TensorProduct.includeRight (1 : B) ⊗ₜ[A, _] (f.f k x) =
      (extendScalars (algebraMap A (A ⊗[R] B))).map (f.f k)
        (Algebra.TensorProduct.includeRight (1 : B) ⊗ₜ[A, _] x)
    erw [ExtendScalars.map_tmul]
  have hbase : δ ≫ (H (j + n)).map (counit.app (πR.obj (S.obj K))) ≫
      (ρ K (j + n)).hom =
      (H j).map (counit.app (πR.obj (S.obj L))) ≫ (ρ L j).hom ≫
        (HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℤ) 0).shiftMap
          (ShiftedHom.map f (S ⋙ G)) j (j + n) (by omega) := by
    have h := congrArg (fun f ↦ f ≫ (ρ K (j + n)).hom) hη
    change (δ ≫ (H (j + n)).map (η.app K)) ≫ (ρ K (j + n)).hom =
      ((H j).map (η.app L) ≫ δT) ≫ (ρ K (j + n)).hom at h
    rw [hηapp K, hηapp L] at h
    simp only [Category.assoc] at h
    rw [hT] at h
    exact h
  have hO := congrArg (fun f ↦
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℤ) 0).shiftMap
      f j (j + n) (show n + j = j + n by omega)) ho
  rw [Functor.shiftMap_comp, Functor.shiftMap_comp'] at hO
  have hV := restriction_shiftMap_homology B
    (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom
    (F.obj K) (F.obj L) (n) j (j + n) (by omega) (ShiftedHom.map f F)
  have hordinary :
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℤ) 0).shiftMap
        (ShiftedHom.map f (S ⋙ G)) j (j + n) (by omega) ≫
        HomologicalComplex.homologyMap ordinaryIsoK.hom (j + n) ≫
        (((F.obj K).sc (j + n)).mapHomologyIso U).hom =
      HomologicalComplex.homologyMap ordinaryIsoL.hom j ≫
        (((F.obj L).sc j).mapHomologyIso U).hom ≫ U.map ε := by
    have h := congrArg (fun f ↦ f ≫ (((F.obj K).sc (j + n)).mapHomologyIso U).hom) hO
    change ((HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℤ) 0).shiftMap
        (ShiftedHom.map f (S ⋙ G)) j (j + n) (by omega) ≫
        HomologicalComplex.homologyMap ordinaryIsoK.hom (j + n)) ≫
        (((F.obj K).sc (j + n)).mapHomologyIso U).hom =
      (HomologicalComplex.homologyMap ordinaryIsoL.hom j ≫
        (HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℤ) 0).shiftMap
          (ShiftedHom.map (ShiftedHom.map f F) V) j (j + n) (by omega)) ≫
        (((F.obj K).sc (j + n)).mapHomologyIso U).hom at h
    change (HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℤ) 0).shiftMap
        (ShiftedHom.map (ShiftedHom.map f F) V) j (j + n) (by omega) ≫
        (((F.obj K).sc (j + n)).mapHomologyIso U).hom =
      (((F.obj L).sc j).mapHomologyIso U).hom ≫ U.map ε at hV
    simp only [Category.assoc] at h
    rw [hV] at h
    exact h
  change δ ≫ (H (j + n)).map (counit.app (πR.obj (S.obj K))) ≫
      (ρ K (j + n)).hom ≫ HomologicalComplex.homologyMap ordinaryIsoK.hom (j + n) ≫
        (((F.obj K).sc (j + n)).mapHomologyIso U).hom =
    ((H j).map (counit.app (πR.obj (S.obj L))) ≫ (ρ L j).hom ≫
      HomologicalComplex.homologyMap ordinaryIsoL.hom j ≫
        (((F.obj L).sc j).mapHomologyIso U).hom) ≫ U.map ε
  rw [reassoc_of% hbase]
  simp only [Category.assoc]
  erw [hordinary]

/-- The canonical derived connecting map commutes with the ordinary counit.
Source: Stacks Project, Tag 06Y6, Lemma 15.61.1 (universal counit), and Tag 05SU
(shift compatibility); step 2 of the ordinary triangle-row argument.

Proof: the universal transformation δ from m₃.derived to m₁.derived is fixed
by its counit identity. Whisker that identity by restriction A to R and the
homotopy quotient. Naturality of the resulting counit at T.mor₃ and its
CommShift equation identify the shifted homology square. The homology
factorization isomorphisms for Qh and the homotopy quotient respect shifts.
The ordinary associativity maps also respect T.mor₃ and shift, since both
composites send b tensor x to (1 tensor b) tensor T.mor₃(x), and shifting gives
the same differential sign on each side. Exact restriction E to B has a
natural homology comparison compatible with shifts. Compose these squares,
substitute both comparison_eq identities and the displayed formula for s₂,
and cancel the restriction homology isomorphism. Faithfulness of restriction
E to B yields the asserted E-linear square. This argument uses only the
third arrow of T, not distinguishedness or exactness of any ordinary triangle.
Zero rings, zero complexes and nonflat scalar extensions cause no exception.
(blueprint: lem-pc-base-derived-tensor-ordinary-boundary-square). -/
theorem baseDerivedTensor_ordinary_boundary_square
    (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
    [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} B)]
    (T : Pretriangulated.Triangle (CochainComplex (ModuleCat.{u} A) ℤ))
    (m₁ : BaseDerivedTensorCohomologyModel R A B T.obj₁ C)
    (m₃ : BaseDerivedTensorCohomologyModel R A B T.obj₃ C)
    [m₁.derived.CommShift ℤ] [NatTrans.CommShift m₁.counit ℤ]
    (i : ℤ) (s₂ : m₃.cohomology i ⟶ m₁.cohomology (i + 1)) :
    letI := m₁.universal
    let δ := Functor.leftDerivedNatTrans m₃.derived m₁.derived m₃.counit m₁.counit
      (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)) (𝟙 _)
    let D := (restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex (.up ℤ) ⋙
      HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ) ⋙ DerivedCategory.Qh ⋙ m₁.derived
    let X := DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj
      (((restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex (.up ℤ)).obj T.obj₃))
    ((restrictScalars.{u} Algebra.TensorProduct.includeRight.toRingHom).map s₂ ≫
        (m₁.cohomologyIso (i + 1)).hom =
      (m₃.cohomologyIso i).hom ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map (δ.app X) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} B) 0).shiftMap
          (ShiftedHom.map T.mor₃ D) i (i + 1) (by omega)) →
    s₂ ≫ m₁.comparison (i + 1) = m₃.comparison i ≫
      CochainComplex.homologyδOfTriangle
        (((extendScalars.{u, u, u} (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
          (.up ℤ)).mapTriangle.obj T) i (i + 1) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  let := m₁.universal
  intro δ D X hb
  let S := (restrictScalars.{u} (algebraMap R A)).mapHomologicalComplex (.up ℤ)
  let G := (extendScalars.{u, u, u} (algebraMap R B)).mapHomologicalComplex (.up ℤ)
  let F := (extendScalars.{u, u, u} (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
    (.up ℤ)
  let U := restrictScalars.{u}
    (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom
  let πR := HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)
  let πB := HomotopyCategory.quotient (ModuleCat.{u} B) (.up ℤ)
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B)
  let c₁ := (H (i + 1)).map (m₁.counit.app (πR.obj (S.obj T.obj₁))) ≫
    (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u} B) (i + 1)).hom.app
      (πB.obj (G.obj (S.obj T.obj₁))) ≫
    (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B) (.up ℤ) (i + 1)).hom.app
      (G.obj (S.obj T.obj₁)) ≫ HomologicalComplex.homologyMap m₁.ordinaryIso.hom (i + 1) ≫
    (((F.obj T.obj₁).sc (i + 1)).mapHomologyIso U).hom
  let c₃ := (H i).map (m₁.counit.app (πR.obj (S.obj T.obj₃))) ≫
    (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u} B) i).hom.app
      (πB.obj (G.obj (S.obj T.obj₃))) ≫
    (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} B) (.up ℤ) i).hom.app
      (G.obj (S.obj T.obj₃)) ≫ HomologicalComplex.homologyMap m₃.ordinaryIso.hom i ≫
    (((F.obj T.obj₃).sc i).mapHomologyIso U).hom
  have hc₁ : U.map (m₁.comparison (i + 1)) = (m₁.cohomologyIso (i + 1)).hom ≫ c₁ := by
    apply (cancel_mono (((F.obj T.obj₁).sc (i + 1)).mapHomologyIso U).inv).1
    simpa only [c₁, Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      m₁.comparison_eq (i + 1)
  have hc₃ : U.map (m₃.comparison i) = (m₃.cohomologyIso i).hom ≫
      (H i).map (δ.app X) ≫ c₃ := by
    have hd := Functor.leftDerivedNatTrans_app m₃.derived m₁.derived
      m₃.counit m₁.counit (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ))
      (𝟙 _) (πR.obj (S.obj T.obj₃))
    change δ.app X ≫ m₁.counit.app (πR.obj (S.obj T.obj₃)) =
      m₃.counit.app (πR.obj (S.obj T.obj₃)) ≫ 𝟙 _ at hd
    simp only [Category.comp_id] at hd
    apply (cancel_mono (((F.obj T.obj₃).sc i).mapHomologyIso U).inv).1
    rw [m₃.comparison_eq]
    dsimp only [c₃]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [← (H i).map_comp_assoc, hd]
  have hshift := counit_shifted_map_square R A B m₁.derived m₁.counit
    T.obj₁ T.obj₃ 1 T.mor₃ i m₁.ordinaryIso m₁.ordinaryIso_tmul
    m₃.ordinaryIso m₃.ordinaryIso_tmul
  have hsq : (H 0).shiftMap (ShiftedHom.map T.mor₃ D) i (i + 1) (by omega) ≫ c₁ =
      c₃ ≫ U.map (CochainComplex.homologyδOfTriangle (F.mapTriangle.obj T) i (i + 1)) := by
    exact hshift
  apply U.map_injective
  rw [Functor.map_comp, Functor.map_comp, hc₁, hc₃]
  rw [← Category.assoc, hb]
  simp only [Category.assoc]
  rw [hsq]

end ModuleCat
