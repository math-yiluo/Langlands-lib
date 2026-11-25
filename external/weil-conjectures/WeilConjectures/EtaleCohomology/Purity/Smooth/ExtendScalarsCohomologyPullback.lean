/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerChernClass

/-!
# The comparison `Extᵠ(Λ ⊗ ℤ, -) ≅ Hᵠ` and pullback

The comparison `Extᵠ(Λ ⊗ ℤ_X, N) ⟶ Hᵠ(X, N)` of
`WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBoundaryComparison` commutes with the
pullback along a morphism of schemes `g : X ⟶ Y`
(`AlgebraicGeometry.Etale.extToSheafHOf_upperStar`): both sides are δ-functors in `N` which
agree in degree zero, where this is the compatibility of the unit `ℤ ⟶ Λ ⊗ ℤ` with pullback
(`unitIntToExtendScalars_comp_upperStarExtendScalarsConstantSheafIntIso_inv`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (g : X ⟶ Y)

lemma ofNatIsoRight_unit_app'' {C D : Type*} [Category* C] [Category* D] {F : C ⥤ D}
    {G H : D ⥤ C} (adj : F ⊣ G) (e : G ≅ H) (x : C) :
    (adj.ofNatIsoRight e).unit.app x = adj.unit.app x ≫ e.hom.app _ := by
  rw [← Adjunction.homEquiv_id, Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_id]

lemma unit_app_upperStarExtendScalarsIso_aux
    (x : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (extendScalarsAdjunction Λ Y).unit.app x ≫
      (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
        ((upperStarLowerStarAdjunction _ g).unit.app ((extendScalars Λ Y).obj x) ≫
          (g)_*[ModuleCat.{u + 1} Λ].map ((upperStarExtendScalarsIso Λ g).hom.app x)) =
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app x ≫
      (g)_*[AddCommGrpCat.{u + 1}].map
        ((extendScalarsAdjunction Λ X).unit.app ((g)^*[AddCommGrpCat.{u + 1}].obj x)) := by
  have := Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((extendScalarsAdjunction Λ Y).comp (upperStarLowerStarAdjunction _ g))
    (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).comp
      (extendScalarsAdjunction Λ X)).ofNatIsoRight
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl))) x
  rw [Adjunction.homEquiv_unit, ofNatIsoRight_unit_app''] at this
  simpa [upperStarExtendScalarsIso, Adjunction.comp_unit_app] using this

/-- **Pullback of the unit of extension of scalars.** For an abelian sheaf `x` on `Y`, the
pullback of the unit `x ⟶ Λ ⊗ x` is the unit `g^* x ⟶ Λ ⊗ g^* x`, under
`g^* (forget (Λ ⊗ x)) ≅ forget (g^* (Λ ⊗ x)) ≅ forget (Λ ⊗ g^* x)`. -/
lemma upperStar_map_unit_comp_upperStarExtendScalarsIso
    (x : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (g)^*[AddCommGrpCat.{u + 1}].map ((extendScalarsAdjunction Λ Y).unit.app x) ≫
        upperStarForget₂Comparison Λ g ((extendScalars Λ Y).obj x) ≫
          (forget₂Sheaf Λ X).map ((upperStarExtendScalarsIso Λ g).hom.app x) =
      (extendScalarsAdjunction Λ X).unit.app ((g)^*[AddCommGrpCat.{u + 1}].obj x) := by
  apply ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, Functor.map_comp]
  have h1 := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.naturality
    ((extendScalarsAdjunction Λ Y).unit.app x)
  have h2 := unit_comp_lowerStar_map_upperStarForget₂Comparison Λ g ((extendScalars Λ Y).obj x)
  simp only [Functor.id_map, Functor.comp_map] at h1
  erw [← reassoc_of% h1, reassoc_of% h2]
  refine Eq.trans ?_ (unit_app_upperStarExtendScalarsIso_aux Λ g x)
  rw [Functor.map_comp]
  rfl

/-- The unit class `ℤ ⟶ Λ ⊗ ℤ` is compatible with pullback. -/
lemma unitIntToExtendScalars_comp_upperStarExtendScalarsConstantSheafIntIso_inv :
    unitIntToExtendScalars Λ X ≫
        (forget₂Sheaf Λ X).map (upperStarExtendScalarsConstantSheafIntIso Λ g).inv =
      ((upperStarConstantSheafIso AddCommGrpCat.{u + 1} g).symm.app
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom ≫
        (g)^*[AddCommGrpCat.{u + 1}].map (unitIntToExtendScalars Λ Y) ≫
          upperStarForget₂Comparison Λ g _ := by
  rw [← cancel_mono ((forget₂Sheaf Λ X).map (upperStarExtendScalarsConstantSheafIntIso Λ g).hom),
    Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.comp_id]
  have hc := upperStar_map_unit_comp_upperStarExtendScalarsIso Λ g Y.constantSheafInt
  have hn := (upperStarConstantSheafIso AddCommGrpCat.{u + 1} g).hom.naturality
    (AddEquiv.toAddCommGrpIso (X := AddCommGrpCat.of (ULift.{u + 1} ℤ))
      (Y := AddCommGrpCat.of (ULift.{u + 1} (ZMod 0)))
      (AddEquiv.ulift.trans (AddEquiv.ulift (α := ZMod 0)).symm)).hom
  have hu := (extendScalarsAdjunction Λ X).unit.naturality
    ((upperStarConstantSheafIso AddCommGrpCat.{u + 1} g).hom.app
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod 0))))
  simp only [unitIntToExtendScalars, upperStarExtendScalarsConstantSheafIntIso, Iso.trans_hom,
    Functor.mapIso_hom, Iso.app_hom, Functor.map_comp, Category.assoc, Iso.symm_hom] at hc hn hu ⊢
  erw [reassoc_of% hc]
  simp only [Functor.id_map, Functor.comp_map] at hu hn
  let uc := (upperStarConstantSheafIso AddCommGrpCat.{u + 1} g).hom.app
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod 0)))
  let ηX := (extendScalarsAdjunction Λ X).unit.app X.constantSheafInt
  let ηg := (extendScalarsAdjunction Λ X).unit.app ((g)^*[AddCommGrpCat.{u + 1}].obj
    Y.constantSheafInt)
  let eX := X.constantSheafULiftIntIso.hom
  let eY := Y.constantSheafULiftIntIso.hom
  let i := (upperStarConstantSheafIso AddCommGrpCat.{u + 1} g).app
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  have hu' : uc ≫ ηX = ηg ≫ (forget₂Sheaf Λ X).map ((extendScalars Λ X).map uc) := hu
  have hn' : (g)^*[AddCommGrpCat.{u + 1}].map eY ≫ uc = i.hom ≫ eX := hn
  calc eX ≫ ηX = i.inv ≫ (i.hom ≫ eX) ≫ ηX := by simp
    _ = i.inv ≫ ((g)^*[AddCommGrpCat.{u + 1}].map eY ≫ uc) ≫ ηX := by rw [hn']
    _ = i.inv ≫ (g)^*[AddCommGrpCat.{u + 1}].map eY ≫ (uc ≫ ηX) := by
      simp only [Category.assoc]
    _ = i.inv ≫ (g)^*[AddCommGrpCat.{u + 1}].map eY ≫ ηg ≫
        (forget₂Sheaf Λ X).map ((extendScalars Λ X).map uc) := by rw [hu']

/-- The comparison `g^* (forget₂ B) ⟶ forget₂ (g^* B)` is natural in `B`. -/
@[reassoc]
lemma upperStarForget₂Comparison_naturality {B B' : Sheaf Y.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)} (φ : B ⟶ B') :
    (g)^*[AddCommGrpCat.{u + 1}].map ((forget₂Sheaf Λ Y).map φ) ≫
        upperStarForget₂Comparison Λ g B' =
      upperStarForget₂Comparison Λ g B ≫
        (forget₂Sheaf Λ X).map ((g)^*[ModuleCat.{u + 1} Λ].map φ) := by
  apply ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, Functor.map_comp]
  have h1 := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.naturality
    ((forget₂Sheaf Λ Y).map φ)
  simp only [Functor.id_map, Functor.comp_map] at h1
  have hB := unit_comp_lowerStar_map_upperStarForget₂Comparison Λ g B
  have hB' := unit_comp_lowerStar_map_upperStarForget₂Comparison Λ g B'
  have h2 := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.naturality φ
  simp only [Functor.id_map, Functor.comp_map] at h2
  rw [← Category.assoc, ← h1, Category.assoc, hB', ← Category.assoc, hB]
  exact (congrArg (forget₂Sheaf Λ Y).map h2).trans (Functor.map_comp _ _ _)

attribute [local instance] Abelian.Ext.subsingleton_of_injective in
/-- **The comparison `Extᵠ(Λ ⊗ ℤ, -) ≅ Hᵠ` commutes with pullback.** -/
theorem extToSheafHOf_upperStar (q : ℕ) (B : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (y : Abelian.Ext.{u + 1} ((extendScalars Λ Y).obj Y.constantSheafInt) B q) :
    extToSheafHOf Λ (unitIntToExtendScalars Λ X) ((g)^*[ModuleCat.{u + 1} Λ].obj B) q
        ((Abelian.Ext.mk₀ (upperStarExtendScalarsConstantSheafIntIso Λ g).inv).comp
          (y.mapExactFunctor (g)^*[ModuleCat.{u + 1} Λ]) (zero_add q)) =
      Sheaf.H.map (upperStarForget₂Comparison Λ g B) q
        (cohomologyMap g ((forget₂Sheaf Λ Y).obj B) q
          (extToSheafHOf Λ (unitIntToExtendScalars Λ Y) B q y)) := by
  induction q generalizing B with
  | zero =>
    obtain ⟨f, rfl⟩ := (Abelian.Ext.mk₀_bijective _ _).2 y
    rw [Abelian.Ext.mapExactFunctor_mk₀, Abelian.Ext.mk₀_comp_mk₀, extToSheafHOf_apply,
      extToSheafHOf_apply, Abelian.Ext.mapExactFunctor_mk₀, Abelian.Ext.mapExactFunctor_mk₀,
      Abelian.Ext.mk₀_comp_mk₀, Abelian.Ext.mk₀_comp_mk₀, cohomologyMap_apply,
      Abelian.Ext.mapExactFunctor_mk₀, Abelian.Ext.mk₀_comp_mk₀, Sheaf.H.map_apply,
      Abelian.Ext.mk₀_comp_mk₀]
    congr 1
    rw [Functor.map_comp, ← Category.assoc,
      unitIntToExtendScalars_comp_upperStarExtendScalarsConstantSheafIntIso_inv,
      Functor.map_comp]
    simp only [Category.assoc, upperStarForget₂Comparison_naturality]
  | succ n ih =>
    let I : InjectivePresentation B := Classical.arbitrary _
    have := I.injective
    let T := ShortComplex.mk I.f (cokernel.π I.f) (cokernel.condition I.f)
    have hT : T.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    obtain ⟨z, rfl⟩ := Abelian.Ext.covariant_sequence_exact₁ _ hT y
      (Abelian.Ext.eq_zero_of_injective _) rfl
    have hTg := hT.map_of_exact (g)^*[ModuleCat.{u + 1} Λ]
    have hTf := hT.map_of_exact (forget₂Sheaf Λ Y)
    have hTfg := hTf.map_of_exact (g)^*[AddCommGrpCat.{u + 1}]
    have hTgf := hTg.map_of_exact (forget₂Sheaf Λ X)
    let m : (T.map (forget₂Sheaf Λ Y)).map (g)^*[AddCommGrpCat.{u + 1}] ⟶
        (T.map (g)^*[ModuleCat.{u + 1} Λ]).map (forget₂Sheaf Λ X) :=
      { τ₁ := upperStarForget₂Comparison Λ g T.X₁
        τ₂ := upperStarForget₂Comparison Λ g T.X₂
        τ₃ := upperStarForget₂Comparison Λ g T.X₃
        comm₁₂ := (upperStarForget₂Comparison_naturality Λ g T.f).symm
        comm₂₃ := (upperStarForget₂Comparison_naturality Λ g T.g).symm }
    have hm := hTfg.extClass_naturality hTgf m
    have hL : (Abelian.Ext.mk₀ (upperStarExtendScalarsConstantSheafIntIso Λ g).inv).comp
        ((z.comp hT.extClass rfl).mapExactFunctor (g)^*[ModuleCat.{u + 1} Λ]) (zero_add _) =
        ((Abelian.Ext.mk₀ (upperStarExtendScalarsConstantSheafIntIso Λ g).inv).comp
          (z.mapExactFunctor (g)^*[ModuleCat.{u + 1} Λ]) (zero_add _)).comp hTg.extClass rfl := by
      rw [Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_extClass]
      exact (Abelian.Ext.comp_assoc _ _ _ (zero_add n) rfl (by omega)).symm
    rw [hL]
    have e1 := extToSheafHOf_comp_extClass Λ (unitIntToExtendScalars Λ X) hTg n
      ((Abelian.Ext.mk₀ (upperStarExtendScalarsConstantSheafIntIso Λ g).inv).comp
        (z.mapExactFunctor (g)^*[ModuleCat.{u + 1} Λ]) (zero_add _))
    have e2 := extToSheafHOf_comp_extClass Λ (unitIntToExtendScalars Λ Y) hT n z
    have e3 := cohomologyMap_δSucc g hTf n (extToSheafHOf Λ (unitIntToExtendScalars Λ Y) T.X₃ n z)
    rw [Sheaf.H.δSucc_apply, Sheaf.H.δSucc_apply] at e3
    refine e1.trans ?_
    have ih' := ih T.X₃ z
    erw [ih']
    change _ = Sheaf.H.map (upperStarForget₂Comparison Λ g T.X₁) (n + 1)
      (cohomologyMap g ((forget₂Sheaf Λ Y).obj T.X₁) (n + 1)
        (extToSheafHOf Λ (unitIntToExtendScalars Λ Y) T.X₁ (n + 1) (z.comp hT.extClass rfl)))
    rw [e2]
    erw [e3]
    rw [Sheaf.H.map_apply, Sheaf.H.map_apply,
      Abelian.Ext.comp_assoc _ _ _ (add_zero n) (zero_add 1) (by omega)]
    erw [← hm]
    exact (Abelian.Ext.comp_assoc _ _ _ rfl (add_zero _) (by omega)).symm


section DerivedPullback

variable (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The derived pullback of an `Ext`-class between sheaves is the `Ext`-class of the pulled back
sheaves (pulling back is exact). -/
lemma leftDerivedUpperStar_map_extHom {M N : Sheaf Y.smallEtaleTopology A} {n : ℕ}
    (x : Abelian.Ext.{u + 1} M N n) :
    (L((f)^*[A])).map x.hom ≫ ((L((f)^*[A])).commShiftIso (n : ℤ)).hom.app _ ≫
        ((singleFunctorCompLeftDerivedUpperStarIso A f).hom.app N)⟦(n : ℤ)⟧' =
      (singleFunctorCompLeftDerivedUpperStarIso A f).hom.app M ≫
        (x.mapExactFunctor (f)^*[A]).hom := by
  let ε := leftDerivedUpperStarIsoMapDerivedCategory A f
  have h := Abelian.Ext.mapExactFunctor_hom (f)^*[A] x
  have hcs : ((L((f)^*[A])).commShiftIso (n : ℤ)).hom.app
      ((DerivedCategory.singleFunctor _ 0).obj N) =
      ε.hom.app _ ≫ (((f)^*[A]).mapDerivedCategory.commShiftIso (n : ℤ)).hom.app _ ≫
        (ε.inv.app _)⟦(n : ℤ)⟧' :=
    Functor.CommShift.ofIso_commShiftIso_hom_app _ _ _ _
  rw [hcs, h]
  simp only [singleFunctorCompLeftDerivedUpperStarIso,
    Functor.singleFunctorCompLeftDerivedFunctorIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.map_comp, Category.assoc]
  have hε := ε.hom.naturality x.hom
  rw [reassoc_of% hε]
  erw [← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]
  simp only [ShiftedHom.map, Category.assoc]
  rw [Iso.hom_inv_id_app_assoc]
  rfl

end DerivedPullback


/-- The coefficient extension `μₙ ⟶ μₙ ⊗ Λ` on cohomology commutes with pullback. -/
lemma sheafH_map_unit_cohomologyMap (n q : ℕ) (x : Sheaf.H (Y.rootsOfUnitySheaf n) q) :
    Sheaf.H.map ((forget₂Sheaf Λ X).map ((upperStarExtendScalarsIso Λ g).hom.app _ ≫
        (extendScalars Λ X).map (upperStarRootsOfUnitySheafToRootsOfUnitySheaf n g))) q
      (Sheaf.H.map (upperStarForget₂Comparison Λ g _) q (cohomologyMap g _ q
        (Sheaf.H.map ((extendScalarsAdjunction Λ Y).unit.app _) q x))) =
      Sheaf.H.map ((extendScalarsAdjunction Λ X).unit.app (X.rootsOfUnitySheaf n)) q
        (rootsOfUnityCohomologyMap g n q x) := by
  have h1 := cohomologyMap_map (f := g) (n := q)
    ((extendScalarsAdjunction Λ Y).unit.app (Y.rootsOfUnitySheaf n)) x
  have hc := upperStar_map_unit_comp_upperStarExtendScalarsIso Λ g (Y.rootsOfUnitySheaf n)
  have hu := (extendScalarsAdjunction Λ X).unit.naturality
    (upperStarRootsOfUnitySheafToRootsOfUnitySheaf n g)
  simp only [Functor.id_map, Functor.comp_map] at hu
  have key : (g)^*[AddCommGrpCat.{u + 1}].map
      ((extendScalarsAdjunction Λ Y).unit.app (Y.rootsOfUnitySheaf n)) ≫
      upperStarForget₂Comparison Λ g _ ≫ (forget₂Sheaf Λ X).map
        ((upperStarExtendScalarsIso Λ g).hom.app _ ≫
          (extendScalars Λ X).map (upperStarRootsOfUnitySheafToRootsOfUnitySheaf n g)) =
      upperStarRootsOfUnitySheafToRootsOfUnitySheaf n g ≫
        (extendScalarsAdjunction Λ X).unit.app (X.rootsOfUnitySheaf n) := by
    rw [Functor.map_comp, reassoc_of% hc]
    exact hu.symm
  refine (congrArg (fun z ↦ Sheaf.H.map ((forget₂Sheaf Λ X).map
    ((upperStarExtendScalarsIso Λ g).hom.app _ ≫
      (extendScalars Λ X).map (upperStarRootsOfUnitySheafToRootsOfUnitySheaf n g))) q
        (Sheaf.H.map (upperStarForget₂Comparison Λ g _) q z)) h1).trans ?_
  calc _ = Sheaf.H.map ((g)^*[AddCommGrpCat.{u + 1}].map
          ((extendScalarsAdjunction Λ Y).unit.app (Y.rootsOfUnitySheaf n)) ≫
          upperStarForget₂Comparison Λ g _ ≫ (forget₂Sheaf Λ X).map
            ((upperStarExtendScalarsIso Λ g).hom.app _ ≫
              (extendScalars Λ X).map (upperStarRootsOfUnitySheafToRootsOfUnitySheaf n g))) q
          (cohomologyMap g (Y.rootsOfUnitySheaf n) q x) := by
        rw [Sheaf.H.map_comp_apply, Sheaf.H.map_comp_apply]
        rfl
    _ = Sheaf.H.map (upperStarRootsOfUnitySheafToRootsOfUnitySheaf n g ≫
          (extendScalarsAdjunction Λ X).unit.app (X.rootsOfUnitySheaf n)) q
          (cohomologyMap g (Y.rootsOfUnitySheaf n) q x) :=
        congrArg (fun φ ↦ Sheaf.H.map φ q (cohomologyMap g (Y.rootsOfUnitySheaf n) q x)) key
    _ = _ := Sheaf.H.map_comp_apply _ _ _

variable [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]

/-- The coefficient extension `Hᵠ(-, μₙ) ⟶ Extᵠ(Λ ⊗ ℤ, μₙ ⊗ Λ)` commutes with pullback. -/
lemma kummerCoefficientMap_upperStar (q : ℕ)
    (x : Sheaf.H (Y.rootsOfUnitySheaf (ringChar Λ)) q) :
    ((Abelian.Ext.mk₀ (upperStarExtendScalarsConstantSheafIntIso Λ g).inv).comp
        ((kummerCoefficientMap Λ Y q x).mapExactFunctor (g)^*[ModuleCat.{u + 1} Λ])
          (zero_add q)).comp
        (Abelian.Ext.mk₀ ((upperStarExtendScalarsIso Λ g).hom.app _ ≫ (extendScalars Λ X).map
          (upperStarRootsOfUnitySheafToRootsOfUnitySheaf (ringChar Λ) g))) (add_zero q) =
      kummerCoefficientMap Λ X q (rootsOfUnityCohomologyMap g (ringChar Λ) q x) := by
  apply (extExtendScalarsIntAddEquiv Λ X q _).injective
  refine Eq.trans ?_ (extExtendScalarsIntAddEquiv_kummerCoefficientMap Λ X q _).symm
  refine Eq.trans ?_ (sheafH_map_unit_cohomologyMap Λ g (ringChar Λ) q x)
  have h := extExtendScalarsIntAddEquiv_kummerCoefficientMap Λ Y q x
  change extToSheafHOf Λ _ _ q _ = _
  rw [extToSheafHOf_comp_mk₀, extToSheafHOf_upperStar]
  exact congrArg (fun z ↦ Sheaf.H.map _ q (Sheaf.H.map _ q (cohomologyMap g _ q z))) h

omit [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y] in
lemma ext_comp_mk₀_hom {M M' N N' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} {n : ℕ}
    (a : M' ⟶ M) (x : Abelian.Ext.{u + 1} M N n) (b : N ⟶ N') :
    (((Abelian.Ext.mk₀ a).comp x (zero_add n)).comp (Abelian.Ext.mk₀ b) (add_zero n)).hom =
      (DerivedCategory.singleFunctor _ 0).map a ≫ x.hom ≫
        ((DerivedCategory.singleFunctor _ 0).map b)⟦(n : ℤ)⟧' := by
  simp [Abelian.Ext.comp_hom, ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp]

variable [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y] [NeZero (ringChar Λ)]

/-- The first Chern class `c₁(L)`, unfolded. -/
lemma chernClass_eq (L : X.Pic) :
    chernClass Λ X L = (constantComplexIsoSingleFunctorExtendScalarsInt X Λ).hom ≫
      Abelian.Ext.homAddEquiv (kummerCoefficientMap Λ X 2
        (Pic.chernClassRootsOfUnity (ringChar Λ) (isUnit_ringChar_of_hasInvertibleExponent X) L)) ≫
      (tateTwistObjectOneIso X Λ).inv⟦(2 : ℤ)⟧' :=
  rfl

omit [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y] in
/-- The derived pullback of `Λ_Y(1) ≅ (μₙ ⊗ Λ)[0]`, inverted. -/
lemma leftDerivedUpperStar_map_tateTwistObjectOneIso_inv :
    (L((g)^*[ModuleCat.{u + 1} Λ])).map (tateTwistObjectOneIso Y Λ).inv ≫
      (leftDerivedUpperStarTateTwistObjectIso Λ g 1).hom =
      ((singleFunctorCompLeftDerivedUpperStarIso _ g).hom.app _ ≫
          (DerivedCategory.singleFunctor _ 0).map
            ((upperStarExtendScalarsIso Λ g).hom.app (Y.rootsOfUnitySheaf (ringChar Λ)) ≫
              (extendScalars Λ X).map
                (upperStarRootsOfUnitySheafToRootsOfUnitySheaf (ringChar Λ) g))) ≫
        (tateTwistObjectOneIso X Λ).inv := by
  have hB := leftDerivedUpperStar_map_tateTwistObjectOneIso Λ g
  rw [Iso.eq_comp_inv, ← cancel_epi ((L((g)^*[ModuleCat.{u + 1} Λ])).map
    (tateTwistObjectOneIso Y Λ).hom)]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  exact hB.symm

omit [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
  [NeZero (ringChar Λ)] in
/-- The derived pullback of `Λ_Y ≅ (Λ ⊗ ℤ)[0]`. -/
lemma leftDerivedUpperStar_map_constantComplexIsoSingleFunctorExtendScalarsInt_hom :
    (L((g)^*[ModuleCat.{u + 1} Λ])).map
      (constantComplexIsoSingleFunctorExtendScalarsInt Y Λ).hom =
      (leftDerivedUpperStarConstantComplexIso Λ g).hom ≫
        (constantComplexIsoSingleFunctorExtendScalarsInt X Λ).hom ≫
          (DerivedCategory.singleFunctor _ 0).map
            (upperStarExtendScalarsConstantSheafIntIso Λ g).inv ≫
          (singleFunctorCompLeftDerivedUpperStarIso _ g).inv.app _ := by
  have hA := leftDerivedUpperStar_map_constantComplexIsoSingleFunctorExtendScalarsInt Λ g
  have hE : (upperStarExtendScalarsIso Λ g).hom.app Y.constantSheafInt ≫
      (extendScalars Λ X).map ((upperStarConstantSheafIso AddCommGrpCat.{u + 1} g).hom.app _) =
      (upperStarExtendScalarsConstantSheafIntIso Λ g).hom := rfl
  rw [hE] at hA
  rw [← reassoc_of% hA, ← Functor.map_comp_assoc, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app]
  exact (Category.comp_id _).symm

/-- The first Chern class is compatible with pullback: `Lg^* c₁(L) = c₁(g^* L)`. -/
theorem leftDerivedUpperStar_map_chernClass (L : Y.Pic) :
    (L((g)^*[ModuleCat.{u + 1} Λ])).map (chernClass Λ Y L) ≫
        ((L((g)^*[ModuleCat.{u + 1} Λ])).commShiftIso (2 : ℤ)).hom.app (tateTwistObject Λ Y 1) ≫
          (leftDerivedUpperStarTateTwistObjectIso Λ g 1).hom⟦(2 : ℤ)⟧' =
      (leftDerivedUpperStarConstantComplexIso Λ g).hom ≫ chernClass Λ X (Pic.map g L) := by
  have hB' := leftDerivedUpperStar_map_tateTwistObjectOneIso_inv Λ g
  have hA' := leftDerivedUpperStar_map_constantComplexIsoSingleFunctorExtendScalarsInt_hom Λ g
  have hcs := ((L((g)^*[ModuleCat.{u + 1} Λ])).commShiftIso (2 : ℤ)).hom.naturality
    (tateTwistObjectOneIso Y Λ).inv
  simp only [Functor.comp_map] at hcs
  set y := kummerCoefficientMap Λ Y 2 (Pic.chernClassRootsOfUnity (ringChar Λ)
    (isUnit_ringChar_of_hasInvertibleExponent Y) L) with hy
  have h3 := leftDerivedUpperStar_map_extHom (ModuleCat.{u + 1} Λ) g y
  rw [chernClass_eq Λ L, chernClass_eq Λ (Pic.map g L)]
  simp only [Functor.map_comp, Category.assoc, Abelian.Ext.homAddEquiv_apply]
  erw [reassoc_of% hcs]
  rw [← Functor.map_comp, hB', Functor.map_comp, Functor.map_comp]
  have h3' : (L((g)^*[ModuleCat.{u + 1} Λ])).map y.hom ≫
      ((L((g)^*[ModuleCat.{u + 1} Λ])).commShiftIso (2 : ℤ)).hom.app _ ≫
        ((singleFunctorCompLeftDerivedUpperStarIso _ g).hom.app _)⟦(2 : ℤ)⟧' =
      (singleFunctorCompLeftDerivedUpperStarIso _ g).hom.app _ ≫
        (y.mapExactFunctor (g)^*[ModuleCat.{u + 1} Λ]).hom := h3
  simp only [Category.assoc]
  rw [reassoc_of% h3']
  rw [hA']
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  have hK := kummerCoefficientMap_upperStar Λ g 2
    (Pic.chernClassRootsOfUnity (ringChar Λ) (isUnit_ringChar_of_hasInvertibleExponent Y) L)
  rw [Pic.chernClassRootsOfUnity_map g _ _ (isUnit_ringChar_of_hasInvertibleExponent X)] at hK
  rw [← hK, ext_comp_mk₀_hom]
  simp only [Category.assoc]
  rfl

omit [CompactSpace X] [QuasiSeparatedSpace X] [HasInvertibleExponent Λ X] in
/-- Blueprint `proposition-purity-vector-bundles`: Kummer additivity.

For a line bundle `L` on a quasi-compact quasi-separated scheme `Y` (for instance a separated
finite-type `k`-scheme) on which the exponent of `Λ` is invertible, let
`c₁(L) : Λ_Y ⟶ Λ_Y(1)[2]` (`AlgebraicGeometry.Etale.chernClass`) be the image of the class of
`L` in `H¹(Y, 𝔾ₘ) = Pic(Y)` under the connecting morphism of the Kummer sequence, with
coefficients extended to `Λ(1) = μₙ ⊗ Λ`. Then `c₁(L ⊗ L') = c₁(L) + c₁(L')`, and `c₁` is
compatible with pullback along every morphism `g : X ⟶ Y` of such schemes:
`Lg^* c₁(L) = c₁(g^* L)` under `Lg^* Λ_Y ≅ Λ_X` and `Lg^* Λ_Y(1) ≅ Λ_X(1)`. Compatibility with
base change is the case of the projection `g : Y ×_S S' ⟶ Y`. -/
theorem kummer_additivity :
    (∀ L L' : Y.Pic, chernClass Λ Y (L * L') = chernClass Λ Y L + chernClass Λ Y L') ∧
      ∀ {X : Scheme.{u}} (g : X ⟶ Y) [CompactSpace X] [QuasiSeparatedSpace X]
        [HasInvertibleExponent Λ X] (L : Y.Pic),
        (L((g)^*[ModuleCat.{u + 1} Λ])).map (chernClass Λ Y L) ≫
            ((L((g)^*[ModuleCat.{u + 1} Λ])).commShiftIso (2 : ℤ)).hom.app
              (tateTwistObject Λ Y 1) ≫
            (leftDerivedUpperStarTateTwistObjectIso Λ g 1).hom⟦(2 : ℤ)⟧' =
          (leftDerivedUpperStarConstantComplexIso Λ g).hom ≫ chernClass Λ X (Pic.map g L) :=
  ⟨chernClass_mul Λ Y, fun g _ _ _ L ↦ leftDerivedUpperStar_map_chernClass Λ g L⟩

end AlgebraicGeometry.Etale
