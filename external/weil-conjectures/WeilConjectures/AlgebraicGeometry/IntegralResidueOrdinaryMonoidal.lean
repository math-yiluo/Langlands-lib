/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteCondensedRing
public import WeilConjectures.AlgebraicGeometry.IntegralResidueComparisonInterface
public import WeilConjectures.CategoryTheory.Monoidal.Mod.MapIhom
public import WeilConjectures.CategoryTheory.ModuleObjects.RelativeTensorCoequalizer

/-! # Strong monoidal ordinary pullback for condensed coefficient module objects

Balanced tensor coequalizers give the tensorator, with coherence checked on their
presentation epimorphisms. Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15.
(auxiliary; not a blueprint node)
-/

@[expose] public section
universe v u v' u'
open CategoryTheory MonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Bimod.monoidalCategory
namespace CategoryTheory.Mod.ResidueOrdinary
variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  {R : C} [MonObj R] [IsCommMonObj R]
attribute [local instance] MonoidalClosed.monoidalPreadditive_of_braided

lemma tensorπ_leftUnitor (M : Mod C R) :
    tensorObjπ (regular R) M ≫ (λ_ M).hom.hom = γ[R,M.X] := by
  change tensorObjπ (regular R) M ≫
    (Bimod.whiskerRight (toBimodRegularIso (R := R)).hom ((toBimod R).obj M)).hom ≫
      (Bimod.LeftUnitorBimod.hom ((toBimod R).obj M)) = _
  dsimp only [tensorObjπ]
  rw [Bimod.whiskerRight_hom]
  erw [ι_colimMap_assoc]
  simp only [parallelPairHom_app_one]
  erw [toBimodRegularIso_hom_hom, id_whiskerRight, Category.id_comp]
  exact coequalizer.π_desc _ _

lemma tensorπ_rightUnitor (M : Mod C R) :
    tensorObjπ M (regular R) ≫ (ρ_ M).hom.hom = rightAct M := by
  change tensorObjπ M (regular R) ≫
    (Bimod.whiskerLeft ((toBimod R).obj M) (toBimodRegularIso (R := R)).hom).hom ≫
      (Bimod.RightUnitorBimod.hom ((toBimod R).obj M)) = _
  dsimp only [tensorObjπ]
  rw [Bimod.whiskerLeft_hom]
  erw [ι_colimMap_assoc]
  simp only [parallelPairHom_app_one]
  erw [toBimodRegularIso_hom_hom, whiskerLeft_id, Category.id_comp]
  exact coequalizer.π_desc _ _

lemma relativeTensorRightIso_π (M N : Mod C R) :
    tensorLeftπ N M ≫ (relativeTensorRightIso N).hom.app M = relativeTensorπ M N := by
  simp [relativeTensorRightIso, tensorLeftπ, relativeTensorCofork]

variable {D : Type u'} [Category.{v'} D] [Abelian D] [IsGrothendieckAbelian.{v'} D]
  [MonoidalCategory D] [SymmetricCategory D] [MonoidalClosed D]
  {S : D} [MonObj S] [IsCommMonObj S]
  {G : C ⥤ D} [G.Braided]
  (ρ : S ⟶ G.obj R) [IsMonHom ρ] [IsIso ρ]
  [PreservesColimitsOfShape WalkingParallelPair (mapModComap ρ)]

noncomputable def tensorComparison (M N : Mod C R) :
    (mapModComap ρ).obj (M ⊗ N) ≅
      (mapModComap ρ).obj M ⊗ (mapModComap ρ).obj N :=
  (mapModComap ρ).mapIso ((relativeTensorRightIso N).app M).symm ≪≫
    (tensorLeftCompMapModComapIso ρ (fun X Y ↦ Functor.LaxBraided.braided (F := G) X Y) N).app M ≪≫
      (relativeTensorRightIso ((mapModComap ρ).obj N)).app ((mapModComap ρ).obj M)

lemma tensorComparison_π (M N : Mod C R) :
    G.map (tensorObjπ M N) ≫ (tensorComparison ρ M N).hom.hom =
      inv (Functor.LaxMonoidal.μ G M.X N.X) ≫
        tensorObjπ ((mapModComap ρ).obj M) ((mapModComap ρ).obj N) := by
  have h := map_tensorLeftπ_tensorLeftCompMapModComapIso_hom_app ρ
    (fun X Y ↦ Functor.LaxBraided.braided (F := G) X Y) N M
  have hπ := relativeTensorRightIso_π M N
  have hi : relativeTensorπ M N ≫ (relativeTensorRightIso N).inv.app M =
      tensorLeftπ N M := by rw [← hπ, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  dsimp [tensorComparison, Functor.mapIso]
  have hih := congrArg Hom.hom hi
  change tensorObjπ M N ≫ ((relativeTensorRightIso N).inv.app M).hom = _ at hih
  rw [← G.map_comp_assoc, hih]
  have hh := congrArg (fun z ↦ z ≫
    (relativeTensorRightIso ((mapModComap ρ).obj N)).hom.app ((mapModComap ρ).obj M)) h
  simp only [Category.assoc] at hh
  erw [relativeTensorRightIso_π] at hh
  exact congrArg Hom.hom hh

lemma tensorComparison_inv_π (M N : Mod C R) :
    tensorObjπ ((mapModComap ρ).obj M) ((mapModComap ρ).obj N) ≫
        (tensorComparison ρ M N).inv.hom =
      Functor.LaxMonoidal.μ G M.X N.X ≫ G.map (tensorObjπ M N) := by
  rw [← cancel_mono (tensorComparison ρ M N).hom.hom]
  simp only [Category.assoc, ← Mod.comp_hom', Iso.inv_hom_id, Mod.id_hom', Category.comp_id]
  rw [tensorComparison_π, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]

lemma tensorComparison_inv_natural_left {M M' : Mod C R} (f : M ⟶ M')
    (N : Mod C R) :
    ((mapModComap ρ).map f ▷ (mapModComap ρ).obj N) ≫ (tensorComparison ρ M' N).inv =
      (tensorComparison ρ M N).inv ≫ (mapModComap ρ).map (f ▷ N) := by
  apply Mod.hom_ext
  rw [← cancel_epi (tensorObjπ ((mapModComap ρ).obj M) ((mapModComap ρ).obj N))]
  simp only [Mod.comp_hom']
  erw [tensorObjπ_whiskerRight_assoc, tensorComparison_inv_π,
    reassoc_of% tensorComparison_inv_π]
  change G.map f.hom ▷ G.obj N.X ≫ Functor.LaxMonoidal.μ G M'.X N.X ≫
      G.map (tensorObjπ M' N) =
    Functor.LaxMonoidal.μ G M.X N.X ≫ G.map (tensorObjπ M N) ≫ G.map (f ▷ N).hom
  rw [Functor.LaxMonoidal.μ_natural_left_assoc, ← G.map_comp, ← tensorObjπ_whiskerRight, G.map_comp]

lemma tensorComparison_inv_natural_right (M : Mod C R) {N N' : Mod C R}
    (f : N ⟶ N') :
    ((mapModComap ρ).obj M ◁ (mapModComap ρ).map f) ≫ (tensorComparison ρ M N').inv =
      (tensorComparison ρ M N).inv ≫ (mapModComap ρ).map (M ◁ f) := by
  apply Mod.hom_ext
  rw [← cancel_epi (tensorObjπ ((mapModComap ρ).obj M) ((mapModComap ρ).obj N))]
  simp only [Mod.comp_hom']
  erw [tensorObjπ_whiskerLeft_assoc, tensorComparison_inv_π,
    reassoc_of% tensorComparison_inv_π]
  change G.obj M.X ◁ G.map f.hom ≫ Functor.LaxMonoidal.μ G M.X N'.X ≫
      G.map (tensorObjπ M N') =
    Functor.LaxMonoidal.μ G M.X N.X ≫ G.map (tensorObjπ M N) ≫ G.map (M ◁ f).hom
  rw [Functor.LaxMonoidal.μ_natural_right_assoc, ← G.map_comp, ← tensorObjπ_whiskerLeft, G.map_comp]

noncomputable def unitComparison :
    (mapModComap ρ).obj (regular R) ≅ regular S :=
  isoMk (asIso ρ).symm (by
    change (ρ ▷ G.obj R ≫ Functor.LaxMonoidal.μ G R R ≫ G.map μ[R]) ≫ inv ρ =
      S ◁ inv ρ ≫ μ[S]
    rw [← cancel_mono ρ, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [Category.assoc, IsMonHom.mul_hom]
    change ρ ▷ G.obj R ≫ Functor.LaxMonoidal.μ G R R ≫ G.map μ[R] =
      S ◁ inv ρ ≫ (ρ ⊗ₘ ρ) ≫ (Functor.LaxMonoidal.μ G R R ≫ G.map μ[R])
    rw [MonoidalCategory.tensorHom_def ρ ρ, Category.assoc]
    rw [whisker_exchange_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc, IsIso.inv_hom_id,
      MonoidalCategory.whiskerLeft_id, Category.id_comp])

lemma tensorComparison_left_unitality (M : Mod C R) :
    (λ_ ((mapModComap ρ).obj M)).hom =
      (unitComparison ρ).inv ▷ (mapModComap ρ).obj M ≫
        (tensorComparison ρ (regular R) M).inv ≫ (mapModComap ρ).map (λ_ M).hom := by
  apply Mod.hom_ext
  rw [← cancel_epi (tensorObjπ (regular S) ((mapModComap ρ).obj M))]
  simp only [Mod.comp_hom']
  rw [tensorπ_leftUnitor, tensorObjπ_whiskerRight_assoc]
  erw [reassoc_of% tensorComparison_inv_π]
  change γ[S,((mapModComap ρ).obj M).X] =
    ρ ▷ G.obj M.X ≫ Functor.LaxMonoidal.μ G R M.X ≫ G.map (tensorObjπ (regular R) M) ≫
      G.map (λ_ M).hom.hom
  rw [← G.map_comp, tensorπ_leftUnitor]
  rfl

lemma tensorComparison_right_unitality (M : Mod C R) :
    (ρ_ ((mapModComap ρ).obj M)).hom =
      (mapModComap ρ).obj M ◁ (unitComparison ρ).inv ≫
        (tensorComparison ρ M (regular R)).inv ≫ (mapModComap ρ).map (ρ_ M).hom := by
  apply Mod.hom_ext
  rw [← cancel_epi (tensorObjπ ((mapModComap ρ).obj M) (regular S))]
  simp only [Mod.comp_hom']
  rw [tensorπ_rightUnitor, tensorObjπ_whiskerLeft_assoc]
  erw [reassoc_of% tensorComparison_inv_π]
  change (β_ (G.obj M.X) S).hom ≫
      ρ ▷ G.obj M.X ≫ Functor.LaxMonoidal.μ G R M.X ≫ G.map γ[R,M.X] =
    G.obj M.X ◁ ρ ≫ Functor.LaxMonoidal.μ G M.X R ≫ G.map (tensorObjπ M (regular R)) ≫
      G.map (ρ_ M).hom.hom
  rw [← G.map_comp, tensorπ_rightUnitor]
  change _ = G.obj M.X ◁ ρ ≫ Functor.LaxMonoidal.μ G M.X R ≫
    G.map ((β_ M.X R).hom ≫ γ[R,M.X])
  rw [G.map_comp, Functor.LaxBraided.braided_assoc,
    BraidedCategory.braiding_naturality_right_assoc]

lemma tensorComparison_associativity (M N P : Mod C R) :
    (tensorComparison ρ M N).inv ▷ (mapModComap ρ).obj P ≫
      (tensorComparison ρ (M ⊗ N) P).inv ≫ (mapModComap ρ).map (α_ M N P).hom =
    (α_ ((mapModComap ρ).obj M) ((mapModComap ρ).obj N)
      ((mapModComap ρ).obj P)).hom ≫
      (mapModComap ρ).obj M ◁ (tensorComparison ρ N P).inv ≫
        (tensorComparison ρ M (N ⊗ P)).inv := by
  apply Mod.hom_ext
  rw [← cancel_epi (tensorObjπ
    ((mapModComap ρ).obj M ⊗ (mapModComap ρ).obj N) ((mapModComap ρ).obj P))]
  rw [← cancel_epi (tensorObjπ ((mapModComap ρ).obj M) ((mapModComap ρ).obj N) ▷
    ((mapModComap ρ).obj P).X)]
  simp only [Mod.comp_hom']
  rw [tensorObjπ_whiskerRight_assoc]
  rw [← comp_whiskerRight_assoc]
  erw [tensorComparison_inv_π]
  rw [comp_whiskerRight_assoc]
  erw [reassoc_of% tensorComparison_inv_π]
  erw [Functor.LaxMonoidal.μ_natural_left_assoc]
  rw [show ((mapModComap ρ).map (α_ M N P).hom).hom =
    G.map (α_ M N P).hom.hom from rfl]
  rw [← G.map_comp_assoc, ← G.map_comp]
  rw [Category.assoc, tensorObjπ_associator_hom]
  rw [tensorObjπ_associator_hom_assoc, tensorObjπ_whiskerLeft_assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc]
  erw [tensorComparison_inv_π]
  rw [MonoidalCategory.whiskerLeft_comp_assoc]
  erw [tensorComparison_inv_π]
  erw [Functor.LaxMonoidal.μ_natural_right_assoc]
  simp only [G.map_comp]
  erw [Functor.LaxMonoidal.associativity_assoc]
  rfl

@[instance_reducible]
noncomputable def mapModComapMonoidal : (mapModComap ρ).Monoidal :=
  (Functor.CoreMonoidal.toMonoidal
    { εIso := (unitComparison ρ).symm
      μIso M N := (tensorComparison ρ M N).symm
      μIso_hom_natural_left := tensorComparison_inv_natural_left ρ
      μIso_hom_natural_right M f := tensorComparison_inv_natural_right ρ M f
      associativity := tensorComparison_associativity ρ
      left_unitality := tensorComparison_left_unitality ρ
      right_unitality := tensorComparison_right_unitality ρ })

end CategoryTheory.Mod.ResidueOrdinary

namespace AlgebraicGeometry.ProEtale.CondensedRing

-- Use the same ambient braiding as the tensor-presentation and tensor-model interfaces.
attribute [local instance 20000] sheafBraidedCategory

/-- Ordinary pullback for any condensed commutative coefficient ring is strong monoidal. -/
@[instance_reducible] noncomputable def residueOrdinaryUpperStarMonoidal
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) : (f)^*⟦Λ⟧.Monoidal := by
  let G := (f)^*[Ab.{u + 1}]
  letI : G.Braided :=
    { toMonoidal := inferInstance
      braided X Y := Functor.LaxBraided.braided (F := G) X Y }
  let ρ := (asIso (condensedPullbackHom Λ f)).inv
  letI : (Mod.mapModComap ρ).Monoidal := Mod.ResidueOrdinary.mapModComapMonoidal ρ
  exact Functor.Monoidal.transport
    (Functor.isoWhiskerLeft (G.mapMod (condensedRingObj Λ Y))
      (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f))).symm

end AlgebraicGeometry.ProEtale.CondensedRing

section OrdinaryBraiding
open MonObj
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace CategoryTheory.Mod.ResidueOrdinary
variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [IsGrothendieckAbelian.{v'} D]
  [MonoidalCategory D] [SymmetricCategory D] [MonoidalClosed D]
  {R : C} [MonObj R] [IsCommMonObj R] {S : D} [MonObj S] [IsCommMonObj S]
  {G : C ⥤ D} [G.Braided] (ρ : S ⟶ G.obj R) [IsMonHom ρ] [IsIso ρ]
  [PreservesColimitsOfShape WalkingParallelPair (mapModComap ρ)]
end CategoryTheory.Mod.ResidueOrdinary
attribute [local irreducible] Functor.leftDerivedFunctor Functor.mapDerivedCategory
namespace AlgebraicGeometry.ProEtale.CondensedRing
attribute [local instance 20000] sheafBraidedCategory
attribute [local instance] _root_.instEssentiallySmallProfinite_weilConjectures
end AlgebraicGeometry.ProEtale.CondensedRing

end OrdinaryBraiding
