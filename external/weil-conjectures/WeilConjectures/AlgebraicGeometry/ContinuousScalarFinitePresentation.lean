/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteConstantModelResolution
import all WeilConjectures.AlgebraicGeometry.FiniteConstantModelResolution
import WeilConjectures.AlgebraicGeometry.RegularExtensionComparison

/-!
# Finite presentations over continuous condensed coefficients

Finite presentations over the continuous coefficient ring are extensions of ordinary
finite scalar presentations. Only sections at the one-point profinite set enter.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj TensorProduct

namespace AlgebraicGeometry.ProEtale

/-- The actual extension of an ordinary scalar module to continuous condensed coefficients.
Source: blueprint integral-heart triangulated proof, paragraph (2), finite scalar models
(auxiliary; not a blueprint node). -/
def continuousScalarFunctor (A : Type u) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    ModuleCat.{u + 1} A ⥤ Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      (Profinite.continuousCoefficientRingObj A) :=
  FiniteConstantModel.scalarModules A ⋙
    (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).mapMod
      (AddCommGrpCat.of (ULift.{u + 1} A)) ⋙
    Mod.extendScalars (FiniteConstantModel.scalarToContinuous A)

namespace ContinuousScalarPresentation

open FiniteConstantModel
variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

omit [TopologicalSpace A] [IsTopologicalRing A] in
private theorem scalarModules_full : (scalarModules A).Full := by
  constructor
  intro P Q f
  let g : P →ₗ[A] Q :=
    { toFun := f.hom
      map_add' := map_add f.hom.hom
      map_smul' := fun a p ↦ by
        have h := congrArg (fun k ↦ k.hom (ULift.up a ⊗ₜ[ℤ] p))
          (IsModHom.smul_hom (A := AddCommGrpCat.of (ULift.{u + 1} A)) (f := f.hom))
        exact h }
  exact ⟨ModuleCat.ofHom g, rfl⟩

omit [TopologicalSpace A] [IsTopologicalRing A] in
private theorem scalarModules_faithful : (scalarModules A).Faithful := by
  constructor
  intro P Q f g h
  ext p
  exact ConcreteCategory.congr_hom (congrArg Mod.Hom.hom h) p

attribute [local instance] scalarModules_full scalarModules_faithful

private instance scalarModules_colimits : PreservesFiniteColimits (scalarModules A) :=
  scalarModules_preservesFiniteColimits A

private instance scalarModules_additive' : (scalarModules A).Additive :=
  scalarModules_additive A

private abbrev B : Ab.{u + 1} := AddCommGrpCat.of (ULift.{u + 1} A)
private abbrev Λ := Profinite.continuousCoefficientRingObj A
private abbrev F := constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
private abbrev φ := scalarToContinuous A
private abbrev H := (F.mapMod (B A)) ⋙ Mod.extendScalars (φ A)

private instance H_colimits : PreservesFiniteColimits (H A) := by
  dsimp only [H, F]
  infer_instance

private instance H_additive : (H A).Additive := by
  have : PreservesBinaryBiproducts (H A) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

private def regularIso : (H A).obj (Mod.regular (B A)) ≅ Mod.regular (Λ A) :=
  (Mod.extendScalars (φ A)).mapIso (Mod.isoMk (Iso.refl _) (by simp)) ≪≫
    Mod.regularExtensionIso (φ A)

private def scalarSection (a : 𝟙_ Ab.{u + 1} ⟶ B A) :
    𝟙_ (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ⟶ Λ A :=
  Functor.LaxMonoidal.ε F ≫ F.map a ≫ φ A

private def scalarConstants : ULift.{u + 1} A ≃+
    ULift.{u + 1} C(Profinite.of PUnit.{u + 1}, A) where
  toFun x := ULift.up (ContinuousMap.const _ x.down)
  invFun f := ULift.up (f.down PUnit.unit)
  left_inv _ := rfl
  right_inv f := by
    apply ULift.ext
    ext y
    exact congrArg f.down (Subsingleton.elim PUnit.unit y)
  map_add' _ _ := rfl

private def scalarHom : B A ⟶
    ((sheafSections (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
      (Opposite.op (Profinite.of PUnit.{u + 1}))).obj (Λ A) :=
  (scalarConstants A).toAddCommGrpIso.hom

private instance scalarHom_iso : IsIso (scalarHom A) := by
  unfold scalarHom
  infer_instance

private theorem scalarCounit : F.map (scalarHom A) ≫
    (constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
      Profinite.isTerminalPUnit).counit.app (Λ A) = φ A := by
  let adj := constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
    Profinite.isTerminalPUnit
  change (adj.homEquiv _ _).symm (scalarHom A) = _
  apply (adj.homEquiv _ _).injective
  rw [Equiv.apply_symm_apply]
  dsimp only [adj, constantSheafAdj]
  rw [Adjunction.comp_homEquiv]
  erw [Equiv.trans_apply, Equiv.apply_symm_apply]
  change scalarHom A = 𝟙 _ ≫ (constantFunctions A).app
    (Opposite.op (Profinite.of PUnit.{u + 1}))
  rw [Category.id_comp]
  rfl

private theorem section_surjective : Function.Surjective (scalarSection A) := by
  intro b
  let adj := constantSheafAdj (coherentTopology Profinite.{u}) Ab.{u + 1}
    Profinite.isTerminalPUnit
  let a := adj.homEquiv _ _ (Functor.OplaxMonoidal.η F ≫ b)
  have ha := (adj.homEquiv _ _).symm_apply_apply (Functor.OplaxMonoidal.η F ≫ b)
  rw [adj.homEquiv_counit] at ha
  refine ⟨a ≫ inv (scalarHom A), ?_⟩
  change Functor.LaxMonoidal.ε F ≫ F.map (a ≫ inv (scalarHom A)) ≫ φ A = b
  rw [← scalarCounit]
  calc
    _ = Functor.LaxMonoidal.ε F ≫ F.map ((a ≫ inv (scalarHom A)) ≫ scalarHom A) ≫
        adj.counit.app (Λ A) := by
      simp only [Functor.map_comp, Category.assoc]
      rfl
    _ = Functor.LaxMonoidal.ε F ≫ (Functor.OplaxMonoidal.η F ≫ b) := by
      rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      exact congrArg (fun k ↦ Functor.LaxMonoidal.ε F ≫ k) ha
    _ = b := by rw [← Category.assoc, Functor.Monoidal.ε_η, Category.id_comp]

private theorem regular_entry (a : 𝟙_ Ab.{u + 1} ⟶ B A) :
    (H A).map (Mod.regularLift (Mod.regular (B A)) a) ≫ (regularIso A).hom =
      (regularIso A).hom ≫ Mod.regularLift (Mod.regular (Λ A)) (scalarSection A a) := by
  have hm : (F.mapMod (B A)).map (Mod.regularLift (Mod.regular (B A)) a) ≫
      (Mod.isoMk (Iso.refl _) (by simp) :
        (F.mapMod (B A)).obj (Mod.regular (B A)) ≅ Mod.regular (F.obj (B A))).hom =
      (Mod.isoMk (Iso.refl _) (by simp) :
        (F.mapMod (B A)).obj (Mod.regular (B A)) ≅ Mod.regular (F.obj (B A))).hom ≫
      Mod.regularLift (Mod.regular (F.obj (B A)))
        (Functor.LaxMonoidal.ε F ≫ F.map a) := by
    apply Mod.regular_hom_ext
    change (MonObj.one : 𝟙_ _ ⟶ F.obj (B A)) ≫
        (F.map (Mod.regularLift (Mod.regular (B A)) a).hom ≫ 𝟙 _) =
      (MonObj.one : 𝟙_ _ ⟶ F.obj (B A)) ≫ (𝟙 _ ≫ _)
    simp only [Category.comp_id, Category.id_comp]
    rw [Mod.one_comp_regularLift, Functor.obj.η_def, Category.assoc,
      ← F.map_comp, Mod.one_comp_regularLift]
  have h : Mod.regularLift (Mod.regular (F.obj (B A)))
        (Functor.LaxMonoidal.ε F ≫ F.map a) ≫ Mod.regularCoefficientMap (φ A) =
      Mod.regularCoefficientMap (φ A) ≫ (Mod.comap (φ A)).map
        (Mod.regularLift (Mod.regular (Λ A)) (scalarSection A a)) := by
    apply Mod.regular_hom_ext
    change (MonObj.one : 𝟙_ _ ⟶ F.obj (B A)) ≫
        ((Mod.regularLift (Mod.regular (F.obj (B A)))
          (Functor.LaxMonoidal.ε F ≫ F.map a)).hom ≫ φ A) =
      (MonObj.one : 𝟙_ _ ⟶ F.obj (B A)) ≫
        (φ A ≫ (Mod.regularLift (Mod.regular (Λ A)) (scalarSection A a)).hom)
    rw [← Category.assoc, Mod.one_comp_regularLift, ← Category.assoc,
      IsMonHom.one_hom (φ A), Mod.one_comp_regularLift]
    rfl
  have he := Mod.regularExtensionIso_naturality (φ A)
    (Mod.regularLift (Mod.regular (F.obj (B A))) (Functor.LaxMonoidal.ε F ≫ F.map a))
    (Mod.regularLift (Mod.regular (Λ A)) (scalarSection A a)) (congrArg Mod.Hom.hom h)
  dsimp only [H, regularIso, Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← (Mod.extendScalars (φ A)).map_comp, hm,
    (Mod.extendScalars (φ A)).map_comp, Category.assoc, he]
  exact (Category.assoc _ _ _).symm

private def freeIso (n : ℕ) : (H A).obj (Mod.finiteFree (B A) n) ≅
    Mod.finiteFree (Λ A) n :=
  (H A).mapBiproduct (fun _ : Fin n ↦ Mod.regular (B A)) ≪≫
    biproduct.mapIso (fun _ ↦ regularIso A)

private theorem free_map_surjective (m n : ℕ)
    (f : Mod.finiteFree (Λ A) m ⟶ Mod.finiteFree (Λ A) n) :
    ∃ g : Mod.finiteFree (B A) m ⟶ Mod.finiteFree (B A) n,
      (freeIso A m).inv ≫ (H A).map g ≫ (freeIso A n).hom = f := by
  classical
  let b (j : Fin m) (k : Fin n) := (MonObj.one : 𝟙_ _ ⟶ Λ A) ≫
    (biproduct.ι _ j ≫ f ≫ biproduct.π _ k).hom
  choose a ha using fun j k ↦ section_surjective A (b j k)
  let g := biproduct.matrix fun j k ↦ Mod.regularLift (Mod.regular (B A)) (a j k)
  refine ⟨g, ?_⟩
  have he : (freeIso A m).inv ≫ (H A).map g ≫ (freeIso A n).hom =
      biproduct.matrix (fun j k ↦ Mod.regularLift (Mod.regular (Λ A)) (scalarSection A (a j k))) :=
    by
    apply biproduct.hom_ext'
    intro j
    apply biproduct.hom_ext
    intro k
    simp only [freeIso, Iso.trans_inv, Iso.trans_hom, biproduct.mapIso_inv,
      biproduct.mapIso_hom, Category.assoc, biproduct.ι_map_assoc,
      Functor.mapBiproduct_inv, Functor.mapBiproduct_hom,
      biproduct.ι_desc_assoc, biproduct.map_π, biproduct.lift_π, g, biproduct.matrix]
    erw [biproduct.lift_π_assoc]
    simp only [← Category.assoc, ← Functor.map_comp, biproduct.ι_desc, biproduct.lift_π]
    simp only [Category.assoc]
    rw [regular_entry, Iso.inv_hom_id_assoc]
  rw [he]
  simp_rw [ha]
  apply biproduct.hom_ext'
  intro j
  apply biproduct.hom_ext
  intro k
  erw [biproduct.ι_matrix, biproduct.lift_π]
  apply Mod.regular_hom_ext
  simpa only [Category.assoc] using Mod.one_comp_regularLift (A := Λ A) _ _

private instance continuous_colimits : PreservesFiniteColimits (continuousScalarFunctor A) :=
  inferInstanceAs (PreservesFiniteColimits (scalarModules A ⋙ H A))

private def continuousFreeIso (n : ℕ) :
    (continuousScalarFunctor A).obj (freeScalars A n) ≅ Mod.finiteFree (Λ A) n :=
  (H A).mapIso (scalarFiniteFreeIso A n) ≪≫ freeIso A n

attribute [local irreducible] regularIso freeIso continuousFreeIso

private theorem continuous_free_map_surjective (m n : ℕ)
    (f : Mod.finiteFree (Λ A) m ⟶ Mod.finiteFree (Λ A) n) :
    ∃ g : freeScalars A m ⟶ freeScalars A n,
      (continuousFreeIso A m).inv ≫ (continuousScalarFunctor A).map g ≫
        (continuousFreeIso A n).hom = f := by
  obtain ⟨g, hg⟩ := free_map_surjective A m n f
  let g' := (scalarFiniteFreeIso A m).hom ≫ g ≫ (scalarFiniteFreeIso A n).inv
  refine ⟨(scalarModules A).preimage g', ?_⟩
  change (continuousFreeIso A m).inv ≫
    (H A).map ((scalarModules A).map ((scalarModules A).preimage g')) ≫
      (continuousFreeIso A n).hom = f
  rw [Functor.map_preimage]
  have hh : (H A).map (scalarFiniteFreeIso A m).inv ≫ (H A).map g' ≫
      (H A).map (scalarFiniteFreeIso A n).hom = (H A).map g := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    simp only [g', Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
      Category.comp_id]
  calc
    _ = (freeIso A m).inv ≫
        ((H A).map (scalarFiniteFreeIso A m).inv ≫ (H A).map g' ≫
          (H A).map (scalarFiniteFreeIso A n).hom) ≫ (freeIso A n).hom := by
      simp only [continuousFreeIso, Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv,
        Functor.mapIso_hom, Category.assoc]
    _ = f := by rw [hh]; exact hg

omit [TopologicalSpace A] [IsTopologicalRing A] in
private theorem cokernel_finite {m n : ℕ} (g : freeScalars A m ⟶ freeScalars A n) :
    Module.FinitePresentation A (cokernel g : ModuleCat.{u + 1} A) := by
  have : Module.FinitePresentation A (ULift.{u + 1} A) :=
    Module.FinitePresentation.of_equiv ULift.moduleEquiv.symm
  have (k : ℕ) : Module.FinitePresentation A (freeScalars A k) :=
    inferInstanceAs (Module.FinitePresentation A (Fin k → ULift.{u + 1} A))
  have (k : ℕ) : Module.Finite A (freeScalars A k) :=
    inferInstanceAs (Module.Finite A (Fin k → ULift.{u + 1} A))
  have : Module.FinitePresentation A ((freeScalars A n) ⧸ LinearMap.range g.hom) :=
    Module.finitePresentation_of_surjective (LinearMap.range g.hom).mkQ
      (Submodule.mkQ_surjective _) (by simp)
  exact Module.FinitePresentation.of_equiv (ModuleCat.cokernelIsoRangeQuotient g).symm.toLinearEquiv

omit [TopologicalSpace A] [IsTopologicalRing A] in
private theorem ordinary_presentation (N : ModuleCat.{u + 1} A)
    [Module.FinitePresentation A N] :
    ∃ (m n : ℕ) (g : freeScalars A m ⟶ freeScalars A n), Nonempty (N ≅ cokernel g) := by
  obtain ⟨n, m, f, g, hf, hg⟩ := Module.FinitePresentation.exists_fin' A N
  let fn := freeCoordinates A n
  let fm := freeCoordinates A m
  let g' : freeScalars A m ⟶ freeScalars A n :=
    ModuleCat.ofHom (fn.symm.toLinearMap.comp (g.comp fm.toLinearMap))
  let f' : freeScalars A n ⟶ N := ModuleCat.ofHom (f.comp fn.toLinearMap)
  have hsurj : Function.Surjective f' := hf.comp fn.surjective
  have hexact : Function.Exact g'.hom f'.hom := by
    intro x
    change f (fn x) = 0 ↔ _
    rw [hg]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨fm.symm y, ?_⟩
      change fn.symm (g (fm (fm.symm y))) = x
      rw [LinearEquiv.apply_symm_apply, hy, LinearEquiv.symm_apply_apply]
    · rintro ⟨y, hy⟩
      refine ⟨fm y, ?_⟩
      change fn.symm (g (fm y)) = x at hy
      exact fn.symm_apply_eq.mp hy
  let h := ModuleCat.isColimitCokernelCofork g' f' hexact hsurj
  exact ⟨m, n, g', ⟨h.coconePointUniqueUpToIso (colimit.isColimit _)⟩⟩

end ContinuousScalarPresentation

/-- Finitely presented modules over continuous condensed coefficients are precisely
extensions of ordinary finitely presented scalar modules.

Source: blueprint integral-heart triangulated proof, paragraph (2), finite scalar
presentations; Stacks Tag 0518
(auxiliary; not a blueprint node).

Proof: endomorphisms of the regular condensed module are its sections at the point.
Continuous functions on a point are the scalar ring A. Thus every matrix between
finite free condensed modules is the extension of an ordinary scalar matrix.
Constant sheafification and extension of scalars preserve cokernels and send the
regular scalar module to the regular condensed module. Transporting a finite
presentation proves the forward implication. Applying the same functors to a finite
ordinary presentation proves the reverse implication. This includes zero ranks,
zero rings and torsion quotients, and needs no flatness hypothesis. -/
theorem continuousScalarFinitePresentation (A : Type u) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A]
    (P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      (Profinite.continuousCoefficientRingObj A)) :
    Mod.IsFinitelyPresented (Profinite.continuousCoefficientRingObj A) P ↔
      ∃ N : ModuleCat.{u + 1} A, Module.FinitePresentation A N ∧
        Nonempty (P ≅ (continuousScalarFunctor A).obj N) := by
  classical
  let K := continuousScalarFunctor A
  have : PreservesFiniteColimits K := ContinuousScalarPresentation.continuous_colimits A
  constructor
  · rintro ⟨n, m, f, ⟨e⟩⟩
    obtain ⟨g, hg⟩ := ContinuousScalarPresentation.continuous_free_map_surjective A m n f
    refine ⟨cokernel g, ContinuousScalarPresentation.cokernel_finite A g, ⟨?_⟩⟩
    refine e ≪≫ (cokernel.mapIso (K.map g) f
      (ContinuousScalarPresentation.continuousFreeIso A m)
      (ContinuousScalarPresentation.continuousFreeIso A n) ?_).symm ≪≫
        (PreservesCokernel.iso K g).symm
    change K.map g ≫ _ = _ ≫ f
    rw [← hg]
    simp only [Iso.hom_inv_id_assoc]
    rfl
  · rintro ⟨N, hN, ⟨e⟩⟩
    have := hN
    obtain ⟨m, n, g, ⟨eg⟩⟩ := ContinuousScalarPresentation.ordinary_presentation A N
    let f := (ContinuousScalarPresentation.continuousFreeIso A m).inv ≫ K.map g ≫
      (ContinuousScalarPresentation.continuousFreeIso A n).hom
    refine ⟨n, m, f, ⟨e ≪≫ K.mapIso eg ≪≫ PreservesCokernel.iso K g ≪≫ ?_⟩⟩
    exact cokernel.mapIso (K.map g) f
      (ContinuousScalarPresentation.continuousFreeIso A m)
      (ContinuousScalarPresentation.continuousFreeIso A n) (by simp [f])

end AlgebraicGeometry.ProEtale
