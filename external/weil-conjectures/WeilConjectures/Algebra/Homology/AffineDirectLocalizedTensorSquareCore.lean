/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.AffineBaseChangeTildeCoordinates

import WeilConjectures.Algebra.Homology.DerivedTensorFirstLocalizationModels
import WeilConjectures.Algebra.Homology.AffineStalkScalarExtensionCoordinates
import WeilConjectures.Algebra.Homology.BaseDerivedTensorModelQuasiIsoComparison
import WeilConjectures.Algebra.Homology.AffineStalkBaseSecondLocalizationComparison

/-! Core derived localization and stalk comparison glue.
(blueprint: new-affine-direct-localized-tensor-square-core). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w wM
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
attribute [local instance] Algebra.TensorProduct.rightAlgebra
noncomputable section
namespace AlgebraicGeometry

/-- Keep the tensor-algebra coefficient map abstract; its restrictions are the API. -/
@[irreducible] private def tensorCoefficientMap
    (R Aq B D : Type u) [CommRing R] [CommRing Aq] [CommRing B] [CommRing D]
    [Algebra R Aq] [Algebra R B] [Algebra R D]
    (a : Aq →ₐ[R] D) (b : B →ₐ[R] D) : Aq ⊗[R] B →+* D :=
  (Algebra.TensorProduct.lift (R := R) (S := R) a b
    (fun _ _ ↦ Commute.all _ _)).toRingHom

private theorem tensorCoefficientMap_left
    (R Aq B D : Type u) [CommRing R] [CommRing Aq] [CommRing B] [CommRing D]
    [Algebra R Aq] [Algebra R B] [Algebra R D]
    (a : Aq →ₐ[R] D) (b : B →ₐ[R] D) :
    (tensorCoefficientMap R Aq B D a b).comp (algebraMap Aq (Aq ⊗[R] B)) =
      a.toRingHom := by
  unfold tensorCoefficientMap
  ext x
  change (Algebra.TensorProduct.lift (R := R) (S := R) a b
    (fun _ _ ↦ Commute.all _ _)) (x ⊗ₜ[R] (1 : B)) = a x
  rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]

private theorem tensorCoefficientMap_right
    (R Aq B D : Type u) [CommRing R] [CommRing Aq] [CommRing B] [CommRing D]
    [Algebra R Aq] [Algebra R B] [Algebra R D]
    (a : Aq →ₐ[R] D) (b : B →ₐ[R] D) :
    (tensorCoefficientMap R Aq B D a b).comp Algebra.TensorProduct.includeRight.toRingHom =
      b.toRingHom := by
  unfold tensorCoefficientMap
  ext x
  change (Algebra.TensorProduct.lift (R := R) (S := R) a b
    (fun _ _ ↦ Commute.all _ _)) ((1 : Aq) ⊗ₜ[R] x) = b x
  rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]

/-- Scalar composition in each degree, with naturality for the differentials. -/
@[irreducible] private noncomputable def coefficientExtensionIso
    (A Aq D : Type u) [CommRing A] [CommRing Aq] [CommRing D]
    (rho : A →+* Aq) (f0 : A →+* D) (f1 : Aq →+* D) (h : f1.comp rho = f0)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    ((ModuleCat.extendScalars f0).mapHomologicalComplex (.up ℤ)).obj M ≅
      ((ModuleCat.extendScalars f1).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.extendScalars rho).mapHomologicalComplex (.up ℤ)).obj M) := by
  subst f0
  exact HomologicalComplex.Hom.isoOfComponents
    (fun j ↦ (ModuleCat.extendScalarsComp rho f1).app (M.X j))
    (fun j k _ ↦ ((ModuleCat.extendScalarsComp rho f1).hom.naturality (M.d j k)).symm)

set_option backward.isDefEq.respectTransparency false in
private theorem coefficientExtensionIso_tmul
    (A Aq D : Type u) [CommRing A] [CommRing Aq] [CommRing D]
    (rho : A →+* Aq) (f0 : A →+* D) (f1 : Aq →+* D) (h : f1.comp rho = f0)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (j : ℤ) (d : D) (x : P.X j) :
    (coefficientExtensionIso A Aq D rho f0 f1 h P).hom.f j (d ⊗ₜ[A,f0] x) =
      d ⊗ₜ[Aq,f1] ((1 : Aq) ⊗ₜ[A,rho] x) := by
  subst f0
  unfold coefficientExtensionIso
  change (ModuleCat.extendScalarsComp rho f1).hom.app (P.X j)
    (d ⊗ₜ[A,f1.comp rho] x) = _
  have hx : d ⊗ₜ[A,f1.comp rho] x = d • ((1 : D) ⊗ₜ[A,f1.comp rho] x) := by
    rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]
  rw [hx, map_smul, ModuleCat.extendScalarsComp_hom_app_one_tmul]
  erw [ModuleCat.ExtendScalars.smul_tmul, mul_one]


/-- Equal scalar maps, kept abstract to avoid repeated whole-complex equality casts. -/
@[irreducible] private noncomputable def scalarComplexIso
    (A D : Type u) [CommRing A] [CommRing D] (f g : A →+* D) (h : f = g)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj M ≅
      ((ModuleCat.extendScalars g).mapHomologicalComplex (.up ℤ)).obj M :=
  eqToIso (congrArg
    (fun φ : A →+* D ↦ ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M) h)

private theorem scalarComplexIso_hom
    (A D : Type u) [CommRing A] [CommRing D] (f g : A →+* D) (h : f = g)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    (scalarComplexIso A D f g h M).hom = eqToHom (congrArg
      (fun φ : A →+* D ↦ ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M)
      h) := by
  unfold scalarComplexIso
  rfl

private theorem scalarComplexIso_inv_tmul
    (A D : Type u) [CommRing A] [CommRing D] (f g : A →+* D) (h : f = g)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (j : ℤ) (x : M.X j) :
    (scalarComplexIso A D f g h M).inv.f j ((1 : D) ⊗ₜ[A, g] x) =
      (1 : D) ⊗ₜ[A, f] x := by
  subst g
  unfold scalarComplexIso
  rfl

/-- Compose comparison squares using only functoriality, without unfolding their models. -/
private theorem composeComparisonSquares
    {X Y : Type*} [Category X] [Category Y] (F : X ⥤ Y)
    {C₀ C₁ C₂ : X} {U₀ U₁ U₂ : Y}
    (a : U₀ ⟶ F.obj C₀) (b : U₁ ⟶ F.obj C₁) (l : U₂ ⟶ F.obj C₂)
    (e₁ : U₀ ≅ U₁) (e₂ : U₁ ≅ U₂) (β : C₀ ≅ C₁) (τ : C₀ ≅ C₂)
    (h₁ : a ≫ F.map β.hom = e₁.hom ≫ b)
    (h₂ : b ≫ F.map (β.inv ≫ τ.hom) = e₂.hom ≫ l) :
    a ≫ F.map τ.hom = (e₁ ≪≫ e₂).hom ≫ l := by
  have hcomp : β.hom ≫ (β.inv ≫ τ.hom) = τ.hom := Iso.hom_inv_id_assoc _ _
  rw [Iso.trans_hom, Category.assoc, ← h₂, ← Category.assoc, ← h₁,
    Category.assoc, ← F.map_comp, hcomp]

/-- Transport the ordinary input and compose the two homology squares abstractly. -/
private theorem transportedComparisonSquares
    {X Y : Type*} [Category X] [Category Y] (H : X ⥤ Y)
    {C₀ C₁ C₂ C₃ : X} {U₀ U₁ U₂ : Y}
    (a : U₀ ⟶ H.obj C₀) (n : U₀ ⟶ H.obj C₁)
    (k : U₁ ⟶ H.obj C₂) (m : U₂ ⟶ H.obj C₃)
    (δ : C₁ ≅ C₀) (b : C₁ ≅ C₂) (t : C₂ ≅ C₃)
    (e₁ : U₀ ≅ U₁) (e₂ : U₁ ≅ U₂)
    (ha : a = n ≫ H.map δ.hom)
    (hb : n ≫ H.map b.hom = e₁.hom ≫ k)
    (ht : k ≫ H.map t.hom = e₂.hom ≫ m) :
    a ≫ H.map (δ.inv ≫ b.hom ≫ t.hom) = (e₁ ≪≫ e₂).hom ≫ m := by
  have hc : δ.hom ≫ (δ.inv ≫ b.hom ≫ t.hom) = b.hom ≫ t.hom := by
    simp only [Iso.hom_inv_id_assoc]
  rw [ha, Category.assoc, ← H.map_comp, hc, H.map_comp,
    ← Category.assoc, hb, Category.assoc, ht, Iso.trans_hom, Category.assoc]

/-- Keep the universal model constructor abstract during comparison elaboration. -/
@[irreducible] private noncomputable def affineTensorModel
    (R A B D : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) D]
    [HasDerivedCategory.{wM} (ModuleCat.{u} R)]
    [HasDerivedCategory.{wM} (ModuleCat.{u} B)]
    (Q : CochainComplex (ModuleCat.{u} A) ℤ) :
    ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D :=
  ModuleCat.baseDerivedTensorCohomologyModel R A B Q D

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

-- Affine stalk algebra instances and their homology transports require this budget.
/--
For an explicitly supplied affine tilde complex `P`, the common localization model
produces the comparison isomorphism and its universal characterization. This is the
substantial derived localization and stalk glue step in the proof of the parent theorem.
Source: Stacks Project, Tag 0DJ8, together with Tags 06Y6 and 01I9.
(blueprint: new-affine-direct-localized-tensor-square-core).
-/
theorem affineDirectLocalizedTensorSquare_core
    (R A R' A' : Type u) [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [Algebra R A] [Algebra R R'] [Algebra (A ⊗[R] R') A']
    [HasDerivedCategory.{wM} (ModuleCat.{u} R)]
    [HasDerivedCategory.{wM} (ModuleCat.{u} R')]
    (φg' : A →+* A') (φf' : R' →+* A')
    (hφg' : (algebraMap (A ⊗[R] R') A').comp
      (algebraMap A (A ⊗[R] R')) = φg')
    (hφf' : (algebraMap (A ⊗[R] R') A').comp
      Algebra.TensorProduct.includeRight.toRingHom = φf')
    (sq : IsPullback (Spec.map (CommRingCat.ofHom φg')) (Spec.map (CommRingCat.ofHom φf'))
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (i : ℤ)
    (p : PrimeSpectrum A') :
    let P := ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
      (@id (ModuleCat.{u} A ⥤
        SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M)
      let f := Spec.map (CommRingCat.ofHom (algebraMap R A))
      let f' := Spec.map (CommRingCat.ofHom φf')
      let g := Spec.map (CommRingCat.ofHom (algebraMap R R'))
      let g' := Spec.map (CommRingCat.ofHom φg')
      letI := SingleComplexBaseChange.leftAlgebra f g' p
      letI := SingleComplexBaseChange.rightAlgebra f f' g g' sq p
      letI := (SingleComplexBaseChange.tensorMap f f' g g' sq p).toAlgebra
      letI := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.R f g' p))
      letI := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.B f' p))
      let D : Type u := (Spec.structureSheaf A').presheaf.stalk p
      let κ := (StructureSheaf.toStalk A' p).hom
      letI : Algebra (A ⊗[R] R') D :=
        (κ.comp (algebraMap (A ⊗[R] R') A')).toAlgebra
      (n : ModuleCat.BaseDerivedTensorCohomologyModel R A R' M D) →
      let C := ((ModuleCat.extendScalars (κ.comp φg')).mapHomologicalComplex (.up ℤ)).obj M
      let U := affineBaseChangeTildeModule R A R' D M n i
      let hφ : (algebraMap (A ⊗[R] R') D).comp
          (algebraMap A (A ⊗[R] R')) = κ.comp φg' :=
        by
          change (κ.comp (algebraMap (A ⊗[R] R') A')).comp _ = _
          rw [RingHom.comp_assoc, hφg']
      let a := affineBaseChangeTildeModuleMap R A R' D M n (κ.comp φg') hφ i
        (C.homology i) (Iso.refl _)
      let ρ := (SingleComplexBaseChange.tensorMap f f' g g' sq p).comp
        (algebraMap (SingleComplexBaseChange.A g' p)
          (SingleComplexBaseChange.A g' p ⊗[SingleComplexBaseChange.R f g' p]
            SingleComplexBaseChange.B f' p))
      let l :=
        (SingleComplexBaseChange.cohomologyModel f f' g g' sq p P).localizedComparison i
      ∃ e : U ≅ (Arrow.mk l).left,
        ∀ τ : C ≅
            SingleComplexBaseChange.tensorComplex f f' g g' sq p P,
          (∀ (j : ℤ) (x : M.X j),
            τ.hom.f j ((1 : D) ⊗ₜ[A, κ.comp φg'] x) =
              (1 : (Spec (.of A')).presheaf.stalk p) ⊗ₜ[SingleComplexBaseChange.A g' p, ρ]
                (TopCat.Presheaf.germ (P.X j).val.presheaf ⊤ (g' p) trivial
                  (tilde.toOpen (R := .of A) (M.X j) ⊤ x))) →
          a ≫ HomologicalComplex.homologyMap τ.hom i = e.hom ≫ l := by
  intro P f f' g g' D κ n C U hφ a ρ l
  let Aq : Type u := (Spec.structureSheaf A).presheaf.stalk (g' p)
  let κA := (StructureSheaf.toStalk A (g' p)).hom
  let α := (g'.stalkMap p).hom
  have hα : α.comp κA = κ.comp φg' := by
    exact congrArg CommRingCat.Hom.hom
      (AlgebraicGeometry.stalkMap_toStalk (CommRingCat.ofHom φg') p)
  let : Algebra A Aq := κA.toAlgebra
  let : IsLocalization (g' p).asIdeal.primeCompl Aq :=
    StructureSheaf.IsLocalization.to_stalk (R := A) (g' p)
  let : Algebra R Aq := (κA.comp (algebraMap R A)).toAlgebra
  let : Algebra R D := ((κ.comp φg').comp (algebraMap R A)).toAlgebra
  have hbase : (κ.comp φf').comp (algebraMap R R') =
      (κ.comp φg').comp (algebraMap R A) := by
    rw [← hφg', ← hφf']
    simp only [RingHom.comp_assoc]
    congr 2
    exact (IsScalarTower.algebraMap_eq R R' (A ⊗[R] R')).symm.trans
      (IsScalarTower.algebraMap_eq R A (A ⊗[R] R'))
  let αR : Aq →ₐ[R] D :=
    { toRingHom := α
      commutes' := fun r => by
        change α (κA (algebraMap R A r)) = κ (φg' (algebraMap R A r))
        exact DFunLike.congr_fun hα (algebraMap R A r) }
  let βR : R' →ₐ[R] D :=
    { toRingHom := κ.comp φf'
      commutes' := fun r => DFunLike.congr_fun hbase r }
  let ψ := tensorCoefficientMap R Aq R' D αR βR
  have hψA : ψ.comp (algebraMap Aq (Aq ⊗[R] R')) = α :=
    tensorCoefficientMap_left R Aq R' D αR βR
  have hψB : ψ.comp Algebra.TensorProduct.includeRight.toRingHom = κ.comp φf' :=
    tensorCoefficientMap_right R Aq R' D αR βR
  let : Algebra (Aq ⊗[R] R') D := ψ.toAlgebra
  let Q := SingleComplexBaseChange.stalkComplex g' p P
  let m : ModuleCat.BaseDerivedTensorCohomologyModel R Aq R' Q D :=
    affineTensorModel R Aq R' D Q
  let : Algebra A D := (κ.comp φg').toAlgebra
  let : Algebra R' D := (κ.comp φf').toAlgebra
  let : Algebra Aq D := α.toAlgebra
  let : Algebra (A ⊗[R] R') D :=
    (κ.comp (algebraMap (A ⊗[R] R') A')).toAlgebra
  let : IsScalarTower R A Aq := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A (A ⊗[R] R') D :=
    IsScalarTower.of_algebraMap_eq' (by
      change κ.comp φg' = (κ.comp (algebraMap (A ⊗[R] R') A')).comp
        (algebraMap A (A ⊗[R] R'))
      rw [RingHom.comp_assoc, hφg'])
  let : IsScalarTower R' (A ⊗[R] R') D :=
    IsScalarTower.of_algebraMap_eq' (by
      change κ.comp φf' = (κ.comp (algebraMap (A ⊗[R] R') A')).comp
        Algebra.TensorProduct.includeRight.toRingHom
      rw [RingHom.comp_assoc, hφf'])
  let : IsScalarTower Aq (Aq ⊗[R] R') D :=
    IsScalarTower.of_algebraMap_eq' hψA.symm
  let : IsScalarTower R' (Aq ⊗[R] R') D :=
    IsScalarTower.of_algebraMap_eq' hψB.symm
  let : IsScalarTower A Aq D := IsScalarTower.of_algebraMap_eq' hα.symm
  obtain ⟨χ, hχ, _⟩ := exists_affineStalkScalarExtensionCoordinates.{u, w} A M (g' p) i
  let k : ModuleCat.BaseDerivedTensorCohomologyModel R Aq R'
      ((RingTensorCohomology.extend A Aq).obj M) D :=
    affineTensorModel R Aq R' D ((RingTensorCohomology.extend A Aq).obj M)
  obtain ⟨eLoc, hLoc, _⟩ := RingTensorCohomology.derivedTensor_first_localization_models.{u, wM}
    R A R' Aq D (g' p).asIdeal.primeCompl i
  let φ₀ := (algebraMap (A ⊗[R] R') D).comp (algebraMap A (A ⊗[R] R'))
  let φ₁ := (algebraMap (Aq ⊗[R] R') D).comp (algebraMap Aq (Aq ⊗[R] R'))
  have hcoeff : φ₁.comp κA = φ₀ := by
    change (ψ.comp (algebraMap Aq (Aq ⊗[R] R'))).comp κA = _
    rw [hψA, hα]
    change κ.comp φg' = (κ.comp (algebraMap (A ⊗[R] R') A')).comp
      (algebraMap A (A ⊗[R] R'))
    rw [RingHom.comp_assoc, hφg']
  let b := coefficientExtensionIso A Aq D κA φ₀ φ₁ hcoeff M
  have hb := hLoc M n k b
    (coefficientExtensionIso_tmul A Aq D κA φ₀ φ₁ hcoeff M)
  have hχiso : QuasiIso χ.hom := by infer_instance
  obtain ⟨eχ, heχ⟩ := ModuleCat.exists_baseDerivedTensorModel_quasiIso_comparison.{u, wM}
    R Aq R' D χ.hom hχiso k m i
  let F := (ModuleCat.extendScalars φ₁).mapHomologicalComplex (.up ℤ)
  let t := F.mapIso χ
  let e₁ := eLoc M n k ≪≫
    (ModuleCat.extendScalars (algebraMap (Aq ⊗[R] R') D)).mapIso eχ
  have hφ₀ : φ₀ = κ.comp φg' := by
    change (κ.comp (algebraMap (A ⊗[R] R') A')).comp _ = _
    rw [RingHom.comp_assoc, hφg']
  let δ := scalarComplexIso A D φ₀ (κ.comp φg') hφ₀ M
  let β := δ.symm ≪≫ b ≪≫ t
  set_option backward.isDefEq.respectTransparency false in
    have hβ (j : ℤ) (x : M.X j) :
        β.hom.f j ((1 : D) ⊗ₜ[A, κ.comp φg'] x) =
          (1 : D) ⊗ₜ[Aq, φ₁]
            (TopCat.Presheaf.germ (P.X j).val.presheaf ⊤ (g' p) trivial
              (tilde.toOpen (R := .of A) (M.X j) ⊤ x)) := by
      have hδ : δ.inv.f j ((1 : D) ⊗ₜ[A, κ.comp φg'] x) =
          (1 : D) ⊗ₜ[A, φ₀] x := by
        exact scalarComplexIso_inv_tmul A D φ₀ (κ.comp φg') hφ₀ M j x
      change t.hom.f j (b.hom.f j (δ.inv.f j _)) = _
      rw [hδ]
      have hb_tmul := coefficientExtensionIso_tmul A Aq D κA φ₀ φ₁ hcoeff M j (1 : D) x
      change b.hom.f j _ = _ at hb_tmul
      have hmap := congrArg (fun z ↦ t.hom.f j z) hb_tmul
      refine hmap.trans ?_
      change (1 : D) ⊗ₜ[Aq, φ₁] (χ.hom.f j ((1 : Aq) ⊗ₜ[A, κA] x)) = _
      exact congrArg (fun z : Q.X j ↦ (1 : D) ⊗ₜ[Aq, φ₁] z) (hχ j x)
  have hδhom := scalarComplexIso_hom A D φ₀ (κ.comp φg') hφ₀ M
  have ha : a = n.localizedComparison i ≫ HomologicalComplex.homologyMap δ.hom i := by
    rw [hδhom]
    change n.localizedComparison i ≫ _ ≫ 𝟙 _ = _
    rw [Category.comp_id]
    rfl
  have hfirst :
      a ≫ HomologicalComplex.homologyMap β.hom i =
        e₁.hom ≫ m.localizedComparison i := by
    exact transportedComparisonSquares
      (HomologicalComplex.homologyFunctor (ModuleCat D) (.up ℤ) i)
      a (n.localizedComparison i) (k.localizedComparison i) (m.localizedComparison i)
      δ b t (eLoc M n k)
      ((ModuleCat.extendScalars (algebraMap (Aq ⊗[R] R') D)).mapIso eχ) ha hb heχ
  obtain ⟨e₂, he₂⟩ := exists_affineStalkBaseSecondLocalizationComparison
    R A R' A' φg' φf' hφg' hφf' sq M i p ψ hψA hψB m β hβ
  refine ⟨e₁ ≪≫ e₂, ?_⟩
  intro τ hτ
  have hsecond := he₂ τ hτ
  exact composeComparisonSquares
    (HomologicalComplex.homologyFunctor (ModuleCat D) (.up ℤ) i)
    a (m.localizedComparison i) l e₁ e₂ β τ hfirst hsecond


end AlgebraicGeometry
