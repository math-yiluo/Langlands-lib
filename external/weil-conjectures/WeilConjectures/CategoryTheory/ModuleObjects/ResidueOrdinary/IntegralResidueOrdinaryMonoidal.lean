/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResidueComparisonInterface
public import WeilConjectures.CategoryTheory.Monoidal.Mod.MapIhom
public import WeilConjectures.AlgebraicGeometry.IntegralResidueOrdinaryMonoidal

/-! # Strong monoidal ordinary pullback for condensed coefficient module objects

Balanced tensor coequalizers give the tensorator, with coherence checked on their
presentation epimorphisms. Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15.
(blueprint: new-integral-residue-ordinary-monoidal)
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
/-- The quotient map defining the relative tensor product is linear in its first factor. -/
noncomputable def relativeTensorπ (M N : Mod C R) :
    (Mod.tensorRight R N.X).obj M ⟶ M ⊗ N :=
  homMk (M := (Mod.tensorRight R N.X).obj M) (N := M ⊗ N) (tensorObjπ M N) (by
    change ((α_ R M.X N.X).inv ≫ γ[R,M.X] ▷ N.X) ≫ tensorObjπ M N =
      R ◁ tensorObjπ M N ≫ γ[R,(M ⊗ N).X]
    simpa only [Category.assoc] using (whiskerLeft_tensorπ_smul M N).symm)

/-- The relative tensor product is a cofork of the two action maps on module objects. -/
noncomputable def relativeTensorCofork (M N : Mod C R) :
    Cofork ((tensorRightMap R γ[R,N.X]).app M)
      ((tensorRightRightAct R N.X).app M) :=
  Cofork.ofπ (relativeTensorπ M N) (by
    apply Mod.hom_ext
    change M.X ◁ γ[R,N.X] ≫ tensorObjπ M N =
      ((α_ M.X R N.X).inv ≫ rightAct M ▷ N.X) ≫ tensorObjπ M N
    rw [Category.assoc, tensorObjπ_condition]
    simp only [Category.assoc, Iso.inv_hom_id_assoc])

/-- The tensor cofork is a coequalizer, as can be checked after forgetting the module action. -/
noncomputable def isColimitRelativeTensorCofork (M N : Mod C R) :
    IsColimit (relativeTensorCofork M N) := by
  apply isColimitOfIsColimitCoforkMap (forget R)
  change IsColimit (Cofork.ofπ (tensorObjπ M N) _ :
    Cofork (M.X ◁ γ[R,N.X]) ((α_ M.X R N.X).inv ≫ rightAct M ▷ N.X))
  refine Cofork.IsColimit.mk _
    (fun s ↦ coequalizer.desc (f := rightAct M ▷ N.X)
      (g := (α_ M.X R N.X).hom ≫ M.X ◁ γ[R,N.X]) s.π ?_) ?_ ?_
  · have h := s.condition
    change M.X ◁ γ[R,N.X] ≫ s.π =
      ((α_ M.X R N.X).inv ≫ rightAct M ▷ N.X) ≫ s.π at h
    rw [← cancel_epi (α_ M.X R N.X).inv]
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h.symm
  · intro s
    exact coequalizer.π_desc _ _
  · intro s m hm
    apply coequalizer.hom_ext (f := rightAct M ▷ N.X)
      (g := (α_ M.X R N.X).hom ≫ M.X ◁ γ[R,N.X])
    exact hm.trans (coequalizer.π_desc _ _).symm

/-- The previously constructed coequalizer tensor functor agrees with the monoidal tensor. -/
noncomputable def relativeTensorRightIso (N : Mod C R) :
    Mod.tensorLeft N ≅ MonoidalCategory.tensorRight N :=
  NatIso.ofComponents
    (fun M ↦ by
      change colimit ((tensorLeftDiagram R N).flip.obj M) ≅ M ⊗ N
      exact HasColimit.isoOfNatIso
        (diagramIsoParallelPair ((tensorLeftDiagram R N).flip.obj M)) ≪≫
        (colimit.isColimit _).coconePointUniqueUpToIso (isColimitRelativeTensorCofork M N)) (by
    intro M M' f
    apply colimit.hom_ext
    intro j
    simp only [id_eq, Iso.trans_hom, tensorLeft, Functor.comp_map, colim_map, Category.assoc,
      ι_colimMap_assoc, HasColimit.ι_isoOfNatIso_hom_assoc]
    cases j <;> apply Mod.hom_ext <;>
      simp [relativeTensorCofork, relativeTensorπ, tensorObjπ_whiskerRight])




variable {D : Type u'} [Category.{v'} D] [Abelian D] [IsGrothendieckAbelian.{v'} D]
  [MonoidalCategory D] [SymmetricCategory D] [MonoidalClosed D]
  {S : D} [MonObj S] [IsCommMonObj S]
  {G : C ⥤ D} [G.Braided]
  (ρ : S ⟶ G.obj R) [IsMonHom ρ] [IsIso ρ]
  [PreservesColimitsOfShape WalkingParallelPair (mapModComap ρ)]











end CategoryTheory.Mod.ResidueOrdinary

namespace AlgebraicGeometry.ProEtale.CondensedRing

-- Use the same ambient braiding as the tensor-presentation and tensor-model interfaces.
attribute [local instance 20000] sheafBraidedCategory


/-- The ordinary integral pullback is strong monoidal, constructed from the ambient
inverse image and the coefficient-pullback isomorphism. -/
@[instance_reducible] noncomputable def residueExchangeOrdinaryPullMonoidal
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    {X Y : Scheme.{u}} (f : X ⟶ Y) : (f)^*⟦integralCoeff ℓ E⟧.Monoidal :=
  residueOrdinaryUpperStarMonoidal (integralCoeff ℓ E) f

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
-- Allow elaboration of the explicitly constructed module tensor comparisons.
private theorem mapModComap_braided (M N : Mod C R) :
    let := mapModComapMonoidal ρ
    Functor.LaxMonoidal.μ (mapModComap ρ) M N ≫
        (mapModComap ρ).map (β_ M N).hom =
      (β_ ((mapModComap ρ).obj M) ((mapModComap ρ).obj N)).hom ≫
        Functor.LaxMonoidal.μ (mapModComap ρ) N M := by
  let := mapModComapMonoidal ρ
  apply Mod.hom_ext
  rw [← cancel_epi (tensorObjπ ((mapModComap ρ).obj M) ((mapModComap ρ).obj N))]
  change tensorObjπ _ _ ≫ (tensorComparison ρ M N).inv.hom ≫
      G.map (β_ M N).hom.hom =
    tensorObjπ _ _ ≫ (β_ ((mapModComap ρ).obj M) ((mapModComap ρ).obj N)).hom.hom ≫
      (tensorComparison ρ N M).inv.hom
  erw [reassoc_of% tensorComparison_inv_π, ← G.map_comp]
  erw [Mod.braiding_hom_hom, Mod.tensorObjπ_braidingHomX, G.map_comp]
  rw [Functor.LaxBraided.braided_assoc]
  erw [Mod.braiding_hom_hom, Mod.tensorObjπ_braidingHomX_assoc, tensorComparison_inv_π]
  rfl
end CategoryTheory.Mod.ResidueOrdinary
attribute [local irreducible] Functor.leftDerivedFunctor Functor.mapDerivedCategory
namespace AlgebraicGeometry.ProEtale.CondensedRing
attribute [local instance 20000] sheafBraidedCategory
local instance instEssentiallySmallProfinite_integralResidueOrdinaryMonoidal
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _
-- Allow elaboration of the explicitly constructed module tensor comparisons.
@[instance_reducible] private noncomputable def ordinary_braided
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    let := residueOrdinaryUpperStarMonoidal Λ f
    (f)^*⟦Λ⟧.LaxBraided := by
  let G := (f)^*[Ab.{u + 1}]
  let : G.Braided :=
    { toMonoidal := inferInstance
      braided X Y := Functor.LaxBraided.braided (F := G) X Y }
  let ρ := (asIso (condensedPullbackHom Λ f)).inv
  let : (Mod.mapModComap ρ).Monoidal := Mod.ResidueOrdinary.mapModComapMonoidal ρ
  let : (Mod.mapModComap ρ).LaxBraided :=
    { toLaxMonoidal := inferInstance
      braided := Mod.ResidueOrdinary.mapModComap_braided ρ }
  let i := Functor.isoWhiskerLeft (G.mapMod (condensedRingObj Λ Y))
    (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f))
  let : (G.mapMod (condensedRingObj Λ Y) ⋙
      Mod.extendScalars (condensedPullbackHom Λ f)).Monoidal :=
    Functor.Monoidal.transport i.symm
  let : NatTrans.IsMonoidal i.symm.hom :=
    { unit := by simp [Functor.Monoidal.transport_ε]
      tensor M N := by
        simp [Functor.Monoidal.transport_μ] }
  let h := Functor.LaxBraided.ofNatIso
    (G := G.mapMod (condensedRingObj Λ Y) ⋙
      Mod.extendScalars (condensedPullbackHom Λ f)) i.symm
  exact
    { toLaxMonoidal := (residueOrdinaryUpperStarMonoidal Λ f).toLaxMonoidal
      braided := h.braided }
/-- Canonical ordinary module pullback commutes with the braiding.

The relative tensor coequalizer epimorphism reduces this to braiding compatibility
of ambient sheaf pullback. Transport along the coefficient pullback isomorphism
preserves that equation; invert the monoidal tensorator to obtain the oplax form.

Source: Bhatt--Scholze, Lemma 6.5.9(5); ordinary symmetric monoidal pullback.
(blueprint: new-integral-residue-ordinary-braiding) -/
theorem residueOrdinaryUpperStar_braiding
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)) :
    letI := residueOrdinaryUpperStarMonoidal Λ f
    (f)^*⟦Λ⟧.map (β_ M N).hom ≫ Functor.OplaxMonoidal.δ (f)^*⟦Λ⟧ N M =
      Functor.OplaxMonoidal.δ (f)^*⟦Λ⟧ M N ≫
        (β_ ((f)^*⟦Λ⟧.obj M) ((f)^*⟦Λ⟧.obj N)).hom := by
  let := residueOrdinaryUpperStarMonoidal Λ f
  have h := (ordinary_braided Λ f).braided M N
  rw [← cancel_epi (Functor.LaxMonoidal.μ (f)^*⟦Λ⟧ M N)]
  rw [← Category.assoc, h, Category.assoc, Functor.Monoidal.μ_δ,
    Category.comp_id, Functor.Monoidal.μ_δ_assoc]

end AlgebraicGeometry.ProEtale.CondensedRing

end OrdinaryBraiding
