/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import WeilConjectures.AlgebraicGeometry.ConstantKoszulQuotientAugmentation
public import WeilConjectures.AlgebraicGeometry.KoszulComplex
import WeilConjectures.CategoryTheory.AdditiveConeFamilyComparison
import WeilConjectures.CategoryTheory.ExteriorKoszulScalarRealization

/-! # Finite realization of constant Koszul augmentation cones
Source: Stacks Project, Tags 099M, 093M and 0A0E.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace CategoryTheory.ConstantCompletion
variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
variable (A : Type u) [CommRing A] (I : Ideal A)

open scoped ChangeOfRings

/-- Sectionwise scalar extension sends the regular module to the regular module. -/
private def scalarUnitPresheafIso {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S) :
    SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ (SheafOfModules.unit (siteModuleRings R)) ≅
      (SheafOfModules.unit (siteModuleRings S)).val := by
  let e (V : Cᵒᵖ) :
      (SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ
        (SheafOfModules.unit (siteModuleRings R))).obj V ≅
      (SheafOfModules.unit (siteModuleRings S)).val.obj V := by
    let := (φ.hom.app V).hom.toAlgebra
    exact (TensorProduct.AlgebraTensorModule.rid (R.obj.obj V)
      (S.obj.obj V) (S.obj.obj V)).toModuleIso
  let ep : SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ
      (SheafOfModules.unit (siteModuleRings R)) ≅
      (SheafOfModules.unit (siteModuleRings S)).val :=
    PresheafOfModules.isoMk e (by
      intro X Y f
      apply ModuleCat.ExtendScalars.hom_ext
      intro x
      change (e Y).hom (SheafOfModules.changeOfRingsMap φ _ f
        ((1 : S.obj.obj X) ⊗ₜ[R.obj.obj X, (φ.hom.app X).hom] x)) =
          S.obj.map f ((e X).hom
            ((1 : S.obj.obj X) ⊗ₜ[R.obj.obj X, (φ.hom.app X).hom] x))
      erw [Classical.choose_spec (SheafOfModules.exists_changeOfRingsMap φ _ f)
        1 x, map_one]
      change (φ.hom.app Y) (R.obj.map f x) * 1 =
        S.obj.map f ((φ.hom.app X) x * 1)
      simp only [mul_one]
      exact ConcreteCategory.congr_hom (φ.hom.naturality f) x)
  exact ep

/-- Sheafify the sectionwise regular-module comparison. -/
private def scalarUnitIso {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S) :
    (change φ).obj (SheafOfModules.unit (siteModuleRings R)) ≅
      SheafOfModules.unit (siteModuleRings S) :=
  (PresheafOfModules.sheafification (𝟙 (siteModuleRings S).obj)).mapIso
    (scalarUnitPresheafIso J φ) ≪≫
    asIso ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (siteModuleRings S).obj)).counit.app
        (SheafOfModules.unit (siteModuleRings S)))

/-- The concrete scalar-unit comparison sends the inserted tensor of ones to one. -/
private theorem scalarUnitIso_one {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S)
    (V : Cᵒᵖ) :
    (scalarUnitIso J φ).hom.val.app V
      (tensorSection φ (SheafOfModules.unit (siteModuleRings R)) V 1
        (1 : R.obj.obj V)) = (1 : S.obj.obj V) := by
  let N := SheafOfModules.unit (siteModuleRings S)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (siteModuleRings S).obj)
  let ep := scalarUnitPresheafIso J φ
  have hn := congrArg (fun k ↦ k.app V
    ((1 : S.obj.obj V) ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] (1 : R.obj.obj V)))
    (adj.unit.naturality ep.hom)
  have ht := congrArg (fun k ↦ k.app V (ep.hom.app V
    ((1 : S.obj.obj V) ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] (1 : R.obj.obj V))))
    (adj.right_triangle_components N)
  change (adj.counit.app N).val.app V
    ((((PresheafOfModules.sheafification (𝟙 (siteModuleRings S).obj)).map ep.hom).val.app V)
      ((adj.unit.app (SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ
        (SheafOfModules.unit (siteModuleRings R)))).app V _)) = (1 : S.obj.obj V)
  rw [← show (adj.unit.app N.val).app V (ep.hom.app V _) =
      ((PresheafOfModules.sheafification (𝟙 (siteModuleRings S).obj)).map
        ep.hom).val.app V ((adj.unit.app (SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ
        (SheafOfModules.unit (siteModuleRings R)))).app V _) from hn]
  have he : ep.hom.app V
      ((1 : S.obj.obj V) ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom]
        (1 : R.obj.obj V)) = (1 : S.obj.obj V) := by
    change φ.hom.app V 1 * 1 = 1
    simp
  exact ht.trans he

/-- At the literal zero index, the single-complex coordinate is the identity. -/
private theorem singleZeroInt_eq_refl {D : Type*} [Category D] [HasZeroObject D]
    [HasZeroMorphisms D] (M : D) :
    HomologicalComplex.singleObjXSelf (.up ℤ) 0 M = Iso.refl M := by
  rfl

/-- The corresponding chain-complex coordinate is also the identity. -/
private theorem singleZeroNat_eq_refl {D : Type*} [Category D] [HasZeroObject D]
    [HasZeroMorphisms D] (M : D) :
    HomologicalComplex.singleObjXSelf (.down ℕ) 0 M = Iso.refl M := by
  rfl

/-- A transposed tower morphism has the expected component in each degree. -/
private theorem transposeComponent {D : Type*} [Category D] [HasZeroMorphisms D]
    {X Y : CochainComplex (ℕᵒᵖ ⥤ D) ℤ} (v : X ⟶ Y) (n : ℕᵒᵖ) (i : ℤ) :
    (((HomologicalComplex.functorEquivalence D (.up ℤ) ℕᵒᵖ).functor.map v).app n).f i =
      (v.f i).app n := rfl

/-- Perform the double-transpose conversion before specializing the tower objects. -/
private theorem coneFamilyFromTower
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (E : C ⥤ D) [E.Additive]
    (K L : ℕ → CochainComplex C ℤ) (f : ∀ n, K n ⟶ L n)
    (t : ∀ n m : ℕ, n ≤ m → (K m ⟶ K n))
    (q : ∀ n m : ℕ, n ≤ m → (L m ⟶ L n))
    (hc : ∀ n m h, t n m h ≫ f n = f m ≫ q n m h)
    {T Q : CochainComplex (ℕᵒᵖ ⥤ D) ℤ} (v : T ⟶ Q)
    (eK : ∀ n, (E.mapHomologicalComplex (.up ℤ)).obj (K n) ≅ T.asFunctor.obj (op n))
    (eQ : ∀ n, (E.mapHomologicalComplex (.up ℤ)).obj (L n) ≅ Q.asFunctor.obj (op n))
    (haug : ∀ n, (E.mapHomologicalComplex (.up ℤ)).map (f n) ≫ (eQ n).hom =
      (eK n).hom ≫
        ((HomologicalComplex.functorEquivalence D (.up ℤ) ℕᵒᵖ).functor.map v).app (op n))
    (ht : ∀ n m h, (E.mapHomologicalComplex (.up ℤ)).map (t n m h) ≫ (eK n).hom =
      (eK m).hom ≫ T.asFunctor.map (homOfLE h).op)
    (hfepi : ∀ n, Epi ((E.mapHomologicalComplex (.up ℤ)).map (f n))) :
    ∃ e : ∀ n, (E.mapHomologicalComplex (.up ℤ)).obj
        (HomologicalComplex.homotopyCofiber (f n)) ≅
      (CochainComplex.mappingCone v).asFunctor.obj (op n),
      ∀ n m h, (E.mapHomologicalComplex (.up ℤ)).map
          (HomologicalComplex.homotopyCofiber.mapArrowHom (f m) (f n)
            (fun j : ℤ ↦ ⟨j - 1, sub_add_cancel j 1⟩)
            (Arrow.homMk (t n m h) (q n m h) (hc n m h))) ≫ (e n).hom =
        (e m).hom ≫ (CochainComplex.mappingCone v).asFunctor.map (homOfLE h).op := by
  exact additiveConeFamilyComparison E K L f t q hc
    ((HomologicalComplex.functorEquivalence D (.up ℤ) ℕᵒᵖ).functor.map v)
    eK eQ haug ht hfepi

/-- The reconstructed tower has the original total complex in each level. -/
private def tensorReconstructionIso
    {R : Sheaf J CommRingCat.{u}} (r : ℕ)
    (a : Fin r → (R.obj ⋙ forget CommRingCat).sections)
    (N : Cx R) (n : ℕᵒᵖ) :
    ((ringedKoszulTensorTower R r a).obj N).obj n ≅
      ((ringedKoszulTensorTowerFunctor R r a).obj N).asFunctor.obj n :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (by
    intro i j hij
    obtain rfl : j = i + 1 := hij.symm
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    change (CochainComplex.of.d (V := ℕᵒᵖ ⥤ Mod R) _ _ i (i + 1)).app n = _
    rw [CochainComplex.of_d]
    rfl)

/-- An invertible degree-zero source coordinate detects the augmentation square. -/
private theorem augmentationComparisonOfZero
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (E : C ⥤ D) [E.Additive]
    {K L : CochainComplex C ℤ} {T Q : CochainComplex D ℤ}
    (f : K ⟶ L) (ε : T ⟶ Q)
    (eK : (E.mapHomologicalComplex (.up ℤ)).obj K ≅ T)
    (eQ : (E.mapHomologicalComplex (.up ℤ)).obj L ≅ Q)
    {V Z : C} {M : D} (vK : V ≅ K.X 0) (vL : L.X 0 ≅ Z) (π : V ⟶ Z)
    (c : M ≅ E.obj V) (w : E.obj Z ⟶ Q.X 0) (ρ : M ⟶ T.X 0) (p : M ⟶ Q.X 0)
    (hf : vK.hom ≫ f.f 0 ≫ vL.hom = π)
    (heQ : eQ.hom.f 0 = E.map vL.hom ≫ w)
    (hu : c.hom ≫ E.map vK.hom ≫ eK.hom.f 0 = ρ)
    (hp : c.hom ≫ E.map π ≫ w = p) (hε : ρ ≫ ε.f 0 = p)
    (hex : ∀ g h : (E.mapHomologicalComplex (.up ℤ)).obj K ⟶ Q,
      g.f 0 = h.f 0 → g = h) :
    (E.mapHomologicalComplex (.up ℤ)).map f ≫ eQ.hom = eK.hom ≫ ε := by
  apply hex
  apply (cancel_epi (c.hom ≫ E.map vK.hom)).1
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    heQ, Category.assoc]
  rw [← E.map_comp_assoc, ← E.map_comp_assoc, Category.assoc, hf]
  have hun := congrArg (fun z ↦ z ≫ ε.f 0) hu
  simp only [Category.assoc] at hun
  rw [hun, hε, hp]

attribute [local irreducible] homComplexFunctor ringedKoszulDualTower
  completed ringedKoszulDualUnit

-- Finite tensor coordinates involve several nested sheaf and complex functors.
/-- Exact realization identifies the finite algebraic augmentation cones, including
all strict transition maps. No arbitrary complex, pro-zero or derived limit occurs.
Source: Stacks Project, Tag 099M, with Tags 093M and 0A0E.
(auxiliary; not a blueprint node).

Proof: the supplied exact functor, regular module and quotient isomorphisms fix the
coefficient realization. Exterior scalar realization identifies the realized
exterior complex with the actual dual Koszul tower, naturally for the diagonals.
Tensor the source with the coefficient complex and insert the left unitor. Identify
the reduction of the coefficient complex with its finite quotient in degree zero.
The unit equation for v, projected to level n and degree zero, says that this finite
map is the realized quotient augmentation: precomposition by the degree-zero Koszul
unit is invertible. All other target degrees are zero. The source comparisons are
natural; epimorphy of each realized augmentation forces target naturality. Apply
additiveConeFamilyComparison to obtain the strict cone isomorphisms. Empty lists,
zero rings and the unit ideal require no change to these universal properties. -/
theorem constantKoszulCoefficientConeComparison
    (b : Bool)
    (E : ModuleCat.{u} A ⥤ Mod (coefficients J A I b)) [E.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (c : SheafOfModules.unit (siteModuleRings (coefficients J A I b)) ≅
      E.obj (ModuleCat.of A A))
    (q : ∀ n : ℕ, E.obj (ModuleCat.of A (A ⧸ I ^ (n + 1))) ≅
      (res (finiteMap J A I b n)).obj
        (SheafOfModules.unit (siteModuleRings (finite J A I n))))
    (hs : ∀ x : A, c.hom ≫ E.map (ModuleCat.ofHom (LinearMap.mul A A x)) =
      (ringedKoszulScalar (coefficients J A I b) (algebraSection (baseMap J A I b) x)).asHom ≫
        c.hom)
    (hq : ∀ n : ℕ, c.hom ≫ E.map (ModuleCat.ofHom (I ^ (n + 1)).mkQ) ≫ (q n).hom =
      (SheafOfModules.unitHomEquiv
        ((res (finiteMap J A I b n)).obj
          (SheafOfModules.unit (siteModuleRings (finite J A I n))))).symm
        ⟨fun V ↦ (1 : (finite J A I n).obj.obj V),
          fun f ↦ map_one ((finite J A I n).obj.map f).hom⟩)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = I)
    (εA : ∀ n : ℕ, ExteriorAlgebra.koszulComplex A r (fun i ↦ a i ^ (n + 1)) ⟶
      (ChainComplex.single₀ (ModuleCat.{u} A)).obj
        (ModuleCat.of A (A ⧸ (Ideal.span (Set.range a)) ^ (n + 1))))
    (tA : ∀ n m : ℕ, n ≤ m →
      (ExteriorAlgebra.koszulComplex A r (fun i ↦ a i ^ (m + 1)) ⟶
        ExteriorAlgebra.koszulComplex A r (fun i ↦ a i ^ (n + 1))))
    (qA : ∀ n m : ℕ, n ≤ m →
      ((ChainComplex.single₀ (ModuleCat.{u} A)).obj
          (ModuleCat.of A (A ⧸ (Ideal.span (Set.range a)) ^ (m + 1))) ⟶
        (ChainComplex.single₀ (ModuleCat.{u} A)).obj
          (ModuleCat.of A (A ⧸ (Ideal.span (Set.range a)) ^ (n + 1)))))
    (hεA : ∀ n, (εA n).f 0 = ModuleCat.ofHom
      (((Ideal.span (Set.range a)) ^ (n + 1)).mkQ.comp
        (exteriorPower.zeroEquiv A (Fin r →₀ A)).toLinearMap))
    (htA : ∀ n m h k, (tA n m h).f k = ModuleCat.ofHom
      (exteriorPower.map k
        (Finsupp.linearCombination A (fun i ↦ Finsupp.single i (a i ^ (m - n))))))
    (hqA : ∀ n m h,
      ModuleCat.ofHom ((Ideal.span (Set.range a)) ^ (m + 1)).mkQ ≫ (qA n m h).f 0 =
        ModuleCat.ofHom ((Ideal.span (Set.range a)) ^ (n + 1)).mkQ)
    (hc : ∀ n m h,
      HomologicalComplex.extendMap (tA n m h) ComplexShape.embeddingDownNat ≫
        HomologicalComplex.extendMap (εA n) ComplexShape.embeddingDownNat =
      HomologicalComplex.extendMap (εA m) ComplexShape.embeddingDownNat ≫
        HomologicalComplex.extendMap (qA n m h) ComplexShape.embeddingDownNat) :
    let O := coefficients J A I b
    let U := ringedSiteRingComplex O
    ∀ (v : (ringedKoszulTensorTowerFunctor O r
        (fun i ↦ algebraSection (baseMap J A I b) (a i))).obj U ⟶
      ((reductionTower J A I b).mapHomologicalComplex (.up ℤ)).obj U)
      (_hv : ringedKoszulLimitUnit O r
        (fun i ↦ algebraSection (baseMap J A I b) (a i)) U ≫
          (ordinaryLimit O).map v = ordinaryUnit J A I b U),
    ∃ e : ∀ n : ℕ,
        (E.mapHomologicalComplex (.up ℤ)).obj
          (HomologicalComplex.homotopyCofiber
            (HomologicalComplex.extendMap (εA n) ComplexShape.embeddingDownNat)) ≅
          (CochainComplex.mappingCone v).asFunctor.obj (op n),
      ∀ (n m : ℕ) (h : n ≤ m),
        (E.mapHomologicalComplex (.up ℤ)).map
          (HomologicalComplex.homotopyCofiber.mapArrowHom
            (HomologicalComplex.extendMap (εA m) ComplexShape.embeddingDownNat)
            (HomologicalComplex.extendMap (εA n) ComplexShape.embeddingDownNat)
            (fun j : ℤ ↦ ⟨j - 1, sub_add_cancel j 1⟩)
            (Arrow.homMk
              (HomologicalComplex.extendMap (tA n m h) ComplexShape.embeddingDownNat)
              (HomologicalComplex.extendMap (qA n m h) ComplexShape.embeddingDownNat)
              (hc n m h))) ≫ (e n).hom =
        (e m).hom ≫ (CochainComplex.mappingCone v).asFunctor.map
          (homOfLE h).op := by
  have _ := hqA
  subst I
  intro O U v hv
  let : IsGrothendieckAbelian.{u} (Mod O) := SheafOfModules.isGrothendieckAbelian _
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := Classical.choice (SheafOfModules.tensorClosed O).1
  let := Classical.choice (SheafOfModules.tensorClosed O).2.1
  let mon : MonoidalCategory (Cx O) := inferInstance
  let : MonoidalCategoryStruct (Cx O) := mon.toMonoidalCategoryStruct
  let : MonoidalCategory (Cx O) := mon
  let s := fun x : A ↦ algebraSection (baseMap J A (Ideal.span (Set.range a)) b) x
  let H := E.mapHomologicalComplex (.up ℤ)
  let B (n : ℕ) := ModuleCat.of A (A ⧸ (Ideal.span (Set.range a)) ^ (n + 1))
  let K (n : ℕ) := (ExteriorAlgebra.koszulComplex A r (fun i ↦ a i ^ (n + 1))).extend
    ComplexShape.embeddingDownNat
  let L (n : ℕ) := ((ChainComplex.single₀ (ModuleCat A)).obj (B n)).extend
    ComplexShape.embeddingDownNat
  let f (n : ℕ) : K n ⟶ L n :=
    HomologicalComplex.extendMap (εA n) ComplexShape.embeddingDownNat
  let D := ringedKoszulDualTower O r (fun i ↦ s (a i))
  let T := ((ringedKoszulTensorTowerFunctor O r (fun i ↦ s (a i))).obj U).asFunctor
  let Q := (((reductionTower J A (Ideal.span (Set.range a)) b).mapHomologicalComplex
    (.up ℤ)).obj U).asFunctor
  let ε : T ⟶ Q := (HomologicalComplex.functorEquivalence
    (Mod O) (.up ℤ) ℕᵒᵖ).functor.map v
  obtain ⟨eD, htD, huD⟩ := exteriorKoszul_scalar_realization O E c s hs r a tA htA
  let eK (n : ℕ) : H.obj (K n) ≅ T.obj (op n) :=
    eD n ≪≫ (λ_ (D.obj (op n))).symm ≪≫
      tensorReconstructionIso J r (fun i ↦ s (a i)) U (op n)
  let F (n : ℕ) := reduction J A (Ideal.span (Set.range a)) b n
  have hF (n : ℕ) : (F n).Additive := by
    dsimp only [F, reduction, res]
    infer_instance
  let d (n : ℕ) : (F n).obj (SheafOfModules.unit (siteModuleRings O)) ≅
      (res (finiteMap J A (Ideal.span (Set.range a)) b n)).obj
        (SheafOfModules.unit (siteModuleRings
          (finite J A (Ideal.span (Set.range a)) n))) :=
    (res (finiteMap J A (Ideal.span (Set.range a)) b n)).mapIso
      (scalarUnitIso J (finiteMap J A (Ideal.span (Set.range a)) b n))
  let w (n : ℕ) := (q n) ≪≫ (d n).symm
  let eQ (n : ℕ) : H.obj (L n) ≅ Q.obj (op n) :=
    H.mapIso (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat
      (B n) 0 0 rfl) ≪≫
    (HomologicalComplex.singleMapHomologicalComplex E (.up ℤ) 0).app (B n) ≪≫
    (HomologicalComplex.single (Mod O) (.up ℤ) 0).mapIso (w n) ≪≫
    ((HomologicalComplex.singleMapHomologicalComplex (F n) (.up ℤ) 0).app
      (SheafOfModules.unit (siteModuleRings O))).symm
  let vK (n : ℕ) : ModuleCat.of A A ⟶ (K n).X 0 :=
    ModuleCat.ofHom (exteriorPower.zeroEquiv A (Fin r →₀ A)).symm.toLinearMap ≫
      ((ExteriorAlgebra.koszulComplex A r (fun i ↦ a i ^ (n + 1))).extendXIso
        ComplexShape.embeddingDownNat (i := 0) rfl).inv
  have hvK (n : ℕ) : IsIso (vK n) := by
    change IsIso ((exteriorPower.zeroEquiv A (Fin r →₀ A)).toModuleIso.inv ≫ _)
    infer_instance
  have heQ (n : ℕ) : (eQ n).hom.f 0 =
      E.map ((((ChainComplex.single₀ (ModuleCat A)).obj (B n)).extendXIso
        ComplexShape.embeddingDownNat (i := 0) rfl).hom) ≫ (w n).hom := by
    simp only [eQ, H, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
      Iso.app_inv, HomologicalComplex.comp_f, Functor.mapIso_hom,
      Functor.mapHomologicalComplex_map_f, HomologicalComplex.extendSingleIso_hom_f,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
      HomologicalComplex.single_map_f_self, Category.assoc,
      Iso.inv_hom_id_assoc, ← E.map_comp_assoc]
    simp only [singleZeroInt_eq_refl, singleZeroNat_eq_refl, Iso.refl_hom, Iso.refl_inv,
      Category.comp_id, Category.id_comp, Functor.map_id]
    erw [Category.comp_id]
  have hp (n : ℕ) : c.hom ≫ E.map
      (ModuleCat.ofHom ((Ideal.span (Set.range a)) ^ (n + 1)).mkQ) ≫ (w n).hom =
      ((reductionUnit J A (Ideal.span (Set.range a)) b).app
        (SheafOfModules.unit (siteModuleRings O))).app (op n) := by
    apply (cancel_mono (d n).hom).1
    dsimp only [w, Iso.trans_hom, Iso.symm_hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hq n]
    apply (SheafOfModules.unitHomEquiv _).injective
    apply Subtype.ext
    funext V
    rw [Equiv.apply_symm_apply]
    change (1 : (finite J A (Ideal.span (Set.range a)) n).obj.obj V) =
      (scalarUnitIso J (finiteMap J A (Ideal.span (Set.range a)) b n)).hom.val.app V
      (((reductionUnit J A (Ideal.span (Set.range a)) b).app
        (SheafOfModules.unit (siteModuleRings O))).app (op n) |>.val.app V (1 : O.obj.obj V))
    change _ = (scalarUnitIso J (finiteMap J A (Ideal.span (Set.range a)) b n)).hom.val.app V
      ((((reductionUnit_existsUnique J A (Ideal.span (Set.range a)) b).exists.choose.app
        (SheafOfModules.unit (siteModuleRings O))).app (op n)).val.app V
          (1 : O.obj.obj V))
    rw [(reductionUnit_existsUnique J A (Ideal.span (Set.range a)) b).exists.choose_spec]
    exact (scalarUnitIso_one J _ V).symm
  have hu (n : ℕ) : c.hom ≫ E.map (vK n) ≫ (eK n).hom.f 0 =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv ≫
        (ringedKoszulTensorUnitComponent O r (fun i ↦ s (a i)) U (op n)).f 0 := by
    have hunit : ringedKoszulDualUnit O r (fun i ↦ s (a i)) n ≫
        (λ_ (D.obj (op n))).inv =
        ringedKoszulTensorUnitComponent O r (fun i ↦ s (a i)) U (op n) := by
      change _ = (ρ_ U).inv ≫ (U ◁ ringedKoszulDualUnit O r (fun i ↦ s (a i)) n)
      rw [leftUnitor_inv_naturality]
      change (λ_ (𝟙_ (Cx O))).inv ≫ _ = (ρ_ (𝟙_ (Cx O))).inv ≫ _
      rw [unitors_inv_equal]
      rfl
    have hh := congrArg (fun z ↦ z ≫ (λ_ (D.obj (op n))).inv.f 0) (huD n)
    have hf := congrArg (fun z ↦
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv ≫ z.f 0) hunit
    simp only [HomologicalComplex.comp_f] at hf
    change c.hom ≫ E.map (vK n) ≫ (eD n).hom.f 0 ≫
      (λ_ (D.obj (op n))).inv.f 0 ≫ 𝟙 _ = _
    rw [Category.comp_id]
    simpa only [Category.assoc] using hh.trans hf
  have hn (n : ℕ) :
      (ringedKoszulTensorUnitComponent O r (fun i ↦ s (a i)) U (op n)).f 0 ≫
        (v.f 0).app (op n) =
      ((reductionUnit J A (Ideal.span (Set.range a)) b).app (U.X 0)).app (op n) := by
    have hh := congrArg (fun z ↦ z.f 0 ≫
      limit.π ((reductionComplex J A (Ideal.span (Set.range a)) b U).X 0) (op n)) hv
    change (ringedKoszulLimitUnit O r (fun i ↦ s (a i)) U).f 0 ≫
      limMap (v.f 0) ≫ limit.π _ (op n) = _ at hh
    rw [limMap_π, ← Category.assoc] at hh
    change (limit.lift _ _ ≫ limit.π _ (op n)) ≫ _ = _ at hh
    rw [limit.lift_π] at hh
    exact hh.trans
      ((ordinaryUnit_existsUnique J A (Ideal.span (Set.range a)) b U).exists.choose_spec 0 n)
  have haug (n : ℕ) : H.map (f n) ≫ (eQ n).hom = (eK n).hom ≫ ε.app (op n) := by
    have hf0 : vK n ≫ (f n).f 0 ≫
        (((ChainComplex.single₀ (ModuleCat A)).obj (B n)).extendXIso
          ComplexShape.embeddingDownNat (i := 0) rfl).hom =
        ModuleCat.ofHom ((Ideal.span (Set.range a)) ^ (n + 1)).mkQ := by
      dsimp only [vK, f]
      rw [HomologicalComplex.extendMap_f _ _ (i := 0) (i' := 0) rfl, hεA n]
      dsimp only [B]
      simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
      change ModuleCat.ofHom
        (((((Ideal.span (Set.range a)) ^ (n + 1)).mkQ).comp
          (exteriorPower.zeroEquiv A (Fin r →₀ A)).toLinearMap).comp
            (exteriorPower.zeroEquiv A (Fin r →₀ A)).symm.toLinearMap) = _
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      simp
    refine augmentationComparisonOfZero E (f n) (ε.app (op n)) (eK n) (eQ n)
      (asIso (vK n))
      (((ChainComplex.single₀ (ModuleCat A)).obj (B n)).extendXIso
        ComplexShape.embeddingDownNat (i := 0) rfl)
      (ModuleCat.ofHom ((Ideal.span (Set.range a)) ^ (n + 1)).mkQ)
      c (w n).hom _ _ hf0 (heQ n) (hu n) (hp n) ?_ ?_
    · simp only [singleZeroInt_eq_refl, Iso.refl_inv, Category.id_comp,
        ε, transposeComponent]
      change (ringedKoszulTensorUnitComponent O r (fun i ↦ s (a i)) U (op n)).f 0 ≫
        (v.f 0).app (op n) =
          ((reductionUnit J A (Ideal.span (Set.range a)) b).app (U.X 0)).app (op n)
      exact hn n
    · intro g h hzero
      let j := H.mapIso (HomologicalComplex.extendSingleIso
        ComplexShape.embeddingDownNat (B n) 0 0 rfl) ≪≫
        (HomologicalComplex.singleMapHomologicalComplex E (.up ℤ) 0).app (B n)
      apply (cancel_mono ((eQ n).inv ≫ j.hom)).1
      apply HomologicalComplex.to_single_hom_ext
      simp only [HomologicalComplex.comp_f, hzero]
  have ht (n m : ℕ) (h : n ≤ m) : H.map
      (HomologicalComplex.extendMap (tA n m h) ComplexShape.embeddingDownNat) ≫
      (eK n).hom = (eK m).hom ≫ T.map (homOfLE h).op := by
    dsimp only [eK, Iso.trans_hom, Iso.symm_hom]
    rw [← Category.assoc, htD n m h]
    have hl := leftUnitor_inv_naturality (D.map (homOfLE h).op)
    have hr : (U ◁ D.map (homOfLE h).op) ≫
        (tensorReconstructionIso J r (fun i ↦ s (a i)) U (op n)).hom =
        (tensorReconstructionIso J r (fun i ↦ s (a i)) U (op m)).hom ≫
          T.map (homOfLE h).op := by
      apply HomologicalComplex.hom_ext
      intro i
      change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
      rw [Category.comp_id, Category.id_comp]
      rfl
    rw [Category.assoc, ← Category.assoc (D.map _), hl, Category.assoc]
    change (eD m).hom ≫ (λ_ (D.obj (op m))).inv ≫
      (U ◁ D.map (homOfLE h).op) ≫
        (tensorReconstructionIso J r (fun i ↦ s (a i)) U (op n)).hom = _
    rw [hr]
    simp only [Category.assoc]
  have hfepi (n : ℕ) : Epi (H.map (f n)) := by
    have hepi (k : ℕ) : Epi ((εA n).f k) := by
      cases k with
      | zero =>
        rw [hεA n]
        apply (ModuleCat.epi_iff_surjective _).2
        exact (Submodule.mkQ_surjective _).comp
          (exteriorPower.zeroEquiv A (Fin r →₀ A)).surjective
      | succ k =>
        exact (HomologicalComplex.isZero_single_obj_X (.down ℕ) 0 (B n) (k + 1)
          (by omega)).epi _
    have : Epi (f n) := by
      apply HomologicalComplex.epi_of_epi_f
      intro i
      by_cases hi : ∃ k, ComplexShape.embeddingDownNat.f k = i
      · obtain ⟨k, hk⟩ := hi
        dsimp only [f]
        rw [HomologicalComplex.extendMap_f _ _ hk]
        infer_instance
      · exact (HomologicalComplex.isZero_extend_X _ _ i (by simpa using hi)).epi _
    infer_instance
  exact coneFamilyFromTower E K L f
    (fun n m h ↦ HomologicalComplex.extendMap (tA n m h) ComplexShape.embeddingDownNat)
    (fun n m h ↦ HomologicalComplex.extendMap (qA n m h) ComplexShape.embeddingDownNat)
    hc v eK eQ haug ht hfepi

end CategoryTheory.ConstantCompletion
