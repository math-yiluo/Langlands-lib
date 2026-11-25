/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionBasic
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.AlgebraicGeometry.ConstantModuleSectionProperties
import all WeilConjectures.AlgebraicGeometry.SectionwiseAdicAlgebraLimit

/-! Flatness component of constant coefficient completion.
Source: Stacks Project, Tag 093M (auxiliary; not a blueprint node).
(auxiliary; not a blueprint node)
The sectionwise adic algebra limit theorem applied to the finite quotient tower proves
that the completed coefficient algebra is flat over the constant coefficient sheaf. -/
@[expose] public noncomputable section

set_option synthInstance.maxSize 2048

open CategoryTheory CategoryTheory.Limits Opposite
universe u

namespace CategoryTheory.ConstantCompletion

variable {C : Type u} [SmallCategory C]

private abbrev ringAb : CommRingCat.{u} ⥤ AddCommGrpCat.{u} :=
  forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat

private instance ringAbPreserves (J : GrothendieckTopology C) :
    J.PreservesSheafification ringAb.{u} where
  le := by
    intro P Q f hf
    let := hf.isLocallyInjective
    let := hf.isLocallySurjective
    let : Presheaf.IsLocallyInjective J (Functor.whiskerRight f ringAb.{u}) :=
      ⟨fun x y h ↦ Presheaf.equalizerSieve_mem J f x y h⟩
    let : Presheaf.IsLocallySurjective J (Functor.whiskerRight f ringAb.{u}) :=
      ⟨fun x ↦ Presheaf.imageSieve_mem J f x⟩
    exact J.W_of_isLocallyBijective (Functor.whiskerRight f ringAb.{u})

private instance moduleAbPreserves (J : GrothendieckTopology C) (R : Type u) [CommRing R] :
    J.PreservesSheafification (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) where
  le := by
    intro P Q f hf
    let := hf.isLocallyInjective
    let := hf.isLocallySurjective
    let F := forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}
    let : Presheaf.IsLocallyInjective J (Functor.whiskerRight f F) :=
      ⟨fun x y h ↦ Presheaf.equalizerSieve_mem J f x y h⟩
    let : Presheaf.IsLocallySurjective J (Functor.whiskerRight f F) :=
      ⟨fun x ↦ Presheaf.imageSieve_mem J f x⟩
    exact J.W_of_isLocallyBijective (Functor.whiskerRight f F)

private instance ringSectionsAlgebra (J : GrothendieckTopology C) (R : Type u)
    [CommRing R] (U : Cᵒᵖ) : Algebra R ((constant J R).obj.obj U) :=
  ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of R))).app U).hom.toAlgebra

-- Forgetting to additive groups identifies the two constant-sheaf constructions.
private def ringModuleComparison (J : GrothendieckTopology C) (R : Type u)
    [CommRing R] : (constant J R).obj ⋙ ringAb.{u} ≅
      ((constantSheaf J (ModuleCat.{u} R)).obj (ModuleCat.of R R)).obj ⋙
        forget₂ (ModuleCat R) AddCommGrpCat :=
  (sheafifyComposeIso J ringAb.{u} ((Functor.const Cᵒᵖ).obj (CommRingCat.of R))).symm ≪≫
    sheafifyComposeIso J (forget₂ (ModuleCat R) AddCommGrpCat)
      ((Functor.const Cᵒᵖ).obj (ModuleCat.of R R))

private theorem ringModuleComparison_unit (J : GrothendieckTopology C) (R : Type u)
    [CommRing R] (U : Cᵒᵖ) (r : R) :
    (ringModuleComparison J R).hom.app U
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of R))).app U r) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj (ModuleCat.of R R))).app U r := by
  have h : Functor.whiskerRight
      (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of R))) ringAb.{u} ≫
      (ringModuleComparison J R).hom = Functor.whiskerRight
      (toSheafify J ((Functor.const Cᵒᵖ).obj (ModuleCat.of R R)))
        (forget₂ (ModuleCat R) AddCommGrpCat) := by
    dsimp only [ringModuleComparison, Iso.trans_hom, Iso.symm_hom]
    rw [← Category.assoc, sheafComposeIso_inv_fac]
    exact sheafComposeIso_hom_fac J (forget₂ (ModuleCat R) AddCommGrpCat)
      ((Functor.const Cᵒᵖ).obj (ModuleCat.of R R))
  exact ConcreteCategory.congr_hom (congr_app h U) r

-- Scalar compatibility can be checked on local constant lifts of a section.
private def ringModuleLinearEquiv (J : GrothendieckTopology C) (R : Type u)
    [CommRing R] (U : Cᵒᵖ) :
    ((constant J R).obj.obj U) ≃ₗ[R]
      ((constantSheaf J (ModuleCat.{u} R)).obj (ModuleCat.of R R)).obj.obj U := by
  let e := ((evaluation Cᵒᵖ AddCommGrpCat).obj U).mapIso (ringModuleComparison J R)
  refine { e.addCommGroupIsoToAddEquiv with map_smul' := ?_ }
  intro r x
  let M := ((constantSheaf J (ModuleCat.{u} R)).obj (ModuleCat.of R R))
  let η := toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of R))
  have hM : Presieve.IsSheaf J (M.obj ⋙ forget (ModuleCat R)) :=
    (isSheaf_iff_isSheaf_of_type J _).mp
      ((sheafCompose J (forget (ModuleCat R))).obj M).property
  apply (hM.isSeparated _ (Presheaf.imageSieve_mem J η x)).ext
  rintro V f ⟨a : R, ha⟩
  change η.app (op V) a = (constant J R).obj.map f.op x at ha
  have he (y : (constant J R).obj.obj U) :
      (M.obj.map f.op) ((ringModuleComparison J R).hom.app U y) =
        (ringModuleComparison J R).hom.app (op V) ((constant J R).obj.map f.op y) :=
    (ConcreteCategory.congr_hom ((ringModuleComparison J R).hom.naturality f.op) y).symm
  change (M.obj.map f.op) ((ringModuleComparison J R).hom.app U (r • x)) =
    (M.obj.map f.op) (r • (show M.obj.obj U from (ringModuleComparison J R).hom.app U x))
  rw [he, (M.obj.map f.op).hom.map_smul, he]
  have hn : (constant J R).obj.map f.op (η.app U r) = η.app (op V) r :=
    (ConcreteCategory.congr_hom (η.naturality f.op) r).symm
  change (ringModuleComparison J R).hom.app (op V)
      ((constant J R).obj.map f.op
        ((show (constant J R).obj.obj U from η.app U r) * x)) = _
  rw [map_mul, hn, ← ha]
  erw [← (η.app (op V)).hom.map_mul]
  rw [ringModuleComparison_unit, ringModuleComparison_unit]
  change (toSheafify J ((Functor.const Cᵒᵖ).obj (ModuleCat.of R R))).app (op V)
    (r • a) = _
  exact map_smul _ r a

private theorem ringSectionsFlat (J : GrothendieckTopology C) (R : Type u)
    [CommRing R] [IsNoetherianRing R] (U : Cᵒᵖ) :
    Module.Flat R ((constant J R).obj.obj U) := by
  let := (constantModule_section_properties J R).2.2
    (ModuleCat.of R R) (inferInstance : Module.Flat R R) U.unop
  exact Module.Flat.of_linearEquiv (ringModuleLinearEquiv J R U)

private def algebraTower (J : GrothendieckTopology C) (A : Type u) [CommRing A]
    (I : Ideal A) : ℕᵒᵖ ⥤ Under (constant J A) :=
  Under.lift (finiteSystem J A I) (quotientCone J A I).π

-- Keep the actual coefficient map and the actual finite projections.
private def completionCone (J : GrothendieckTopology C) (A : Type u) [CommRing A]
    (I : Ideal A) : Cone (algebraTower J A I) where
  pt := Under.mk (coefficientMap J A I)
  π :=
    { app := fun n ↦ Under.homMk (projection J A I n.unop) (by
        exact limit.lift_π (quotientCone J A I) n)
      naturality := by
        intro m n f
        apply Under.UnderMorphism.ext
        change projection J A I n.unop =
          projection J A I m.unop ≫ (finiteSystem J A I).map f
        exact (limit.w (finiteSystem J A I) f).symm }

private def completionConeIsLimit (J : GrothendieckTopology C) (A : Type u) [CommRing A]
    (I : Ideal A) : IsLimit (completionCone J A I) :=
  isLimitOfReflects (Under.forget _) (limit.isLimit (finiteSystem J A I))

private instance termQuotientModule (J : GrothendieckTopology C) (A : Type u) [CommRing A]
    (I : Ideal A) (n : ℕ) (U : Cᵒᵖ) :
    Module (A ⧸ I ^ (n + 1)) (adicTerm J A (algebraTower J A I) n U) :=
  inferInstanceAs (Module (A ⧸ I ^ (n + 1))
    ((constant J (A ⧸ I ^ (n + 1))).obj.obj U))

private instance termScalarTower (J : GrothendieckTopology C) (A : Type u) [CommRing A]
    (I : Ideal A) (n : ℕ) (U : Cᵒᵖ) :
    IsScalarTower A (A ⧸ I ^ (n + 1)) (adicTerm J A (algebraTower J A I) n U) := by
  apply IsScalarTower.of_algebraMap_smul
  intro a b
  let η : (A ⧸ I ^ (n + 1)) →+* adicTerm J A (algebraTower J A I) n U :=
    ((toSheafify J ((Functor.const Cᵒᵖ).obj
      (CommRingCat.of (A ⧸ I ^ (n + 1))))).app U).hom
  let α : A →+* adicTerm J A (algebraTower J A I) n U :=
    ((quotient J A I n).hom.app U).hom.comp
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app U).hom
  change η (Ideal.Quotient.mk _ a) * b = α a * b
  congr 1
  exact ConcreteCategory.congr_hom (congr_app
    (toSheafify_naturality J ((Functor.const Cᵒᵖ).map
      (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))) U) a

private theorem termFlat (J : GrothendieckTopology C) (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (n : ℕ) (U : Cᵒᵖ) :
    Module.Flat (A ⧸ I ^ (n + 1)) (adicTerm J A (algebraTower J A I) n U) :=
  ringSectionsFlat J (A ⧸ I ^ (n + 1)) U

private theorem termSurjective (J : GrothendieckTopology C) (A : Type u) [CommRing A]
    (I : Ideal A) (n : ℕ) (U : Cᵒᵖ) :
    Function.Surjective
      (adicTransition J A (algebraTower J A I) (n + 1) n (Nat.le_succ n) U) := by
  change Function.Surjective (((finiteSystem J A I).map
    (homOfLE (Nat.le_succ n)).op).hom.app U)
  simp only [finiteSystem, Functor.ofOpSequence_map_homOfLE_succ]
  classical
  let R₀ := CommRingCat.of (A ⧸ I ^ (n + 1))
  let R₁ := CommRingCat.of (A ⧸ I ^ (n + 2))
  let f : R₁ ⟶ R₀ :=
    CommRingCat.ofHom (Ideal.Quotient.factorPow I (Nat.le_succ (n + 1)))
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨Ideal.Quotient.mk _ a, rfl⟩
  let e := constantCommuteCompose J (forget CommRingCat.{u})
  let s := (constantSheaf J (Type u)).map (TypeCat.ofHom (Function.surjInv hf))
  have hs : s ≫ (constantSheaf J (Type u)).map ((forget CommRingCat.{u}).map f) = 𝟙 _ := by
    rw [← Functor.map_comp]
    trans (constantSheaf J (Type u)).map (𝟙 ((forget CommRingCat.{u}).obj R₀))
    · congr 1
      ext x
      exact Function.surjInv_eq hf x
    exact (constantSheaf J (Type u)).map_id _
  let r := e.hom.app R₀ ≫ s ≫ e.inv.app R₁
  have hr : r ≫ (sheafCompose J (forget CommRingCat.{u})).map
      ((constantSheaf J CommRingCat.{u}).map f) = 𝟙 _ := by
    dsimp only [r]
    rw [Category.assoc, Category.assoc]
    change e.hom.app R₀ ≫ s ≫ e.inv.app R₁ ≫
      (constantSheaf J CommRingCat.{u} ⋙ sheafCompose J (forget CommRingCat.{u})).map f = _
    rw [← e.inv.naturality f]
    change e.hom.app R₀ ≫ s ≫
      (constantSheaf J (Type u)).map ((forget CommRingCat.{u}).map f) ≫ e.inv.app R₀ = _
    rw [← Category.assoc s, hs, Category.id_comp, e.hom_inv_id_app]
  intro x
  exact ⟨r.hom.app U x, congrArg (fun h ↦ h.hom.app U x) hr⟩

theorem flat_and_quotients_flatness (J : GrothendieckTopology C) (A : Type u)
    [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    SheafOfModules.IsFlat
      ((res (coefficientMap J A I)).obj (SheafOfModules.unit
        (siteModuleRings (completed J A I)))) := by
  have hflat := (adicSectionwiseFlatTensor.{u, u} J A I (algebraTower J A I)
    (termFlat J A I) (termSurjective J A I)).1
  let e : Under.mk (coefficientMap J A I) ≅ limit (algebraTower J A I) :=
    IsLimit.conePointUniqueUpToIso (completionConeIsLimit J A I) (limit.isLimit _)
  have hsection (U : Cᵒᵖ) : Module.Flat A
      ((adicAlgebraSections J A U).obj (Under.mk (coefficientMap J A I))) := by
    let := hflat U
    let i := (forget₂ (CommAlgCat A) (AlgCat A)).mapIso
      ((adicAlgebraSections J A U).mapIso e)
    exact Module.Flat.of_linearEquiv i.toAlgEquiv.toLinearEquiv
  have hsite := adicSheafFlat J A (Under.mk (coefficientMap J A I)) hsection
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso (constant J A) _) hsite

end CategoryTheory.ConstantCompletion
