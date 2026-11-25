/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule

/-! # Braiding compatibility for native module pullback

Source: the balanced coequalizer calculation of the ordinary pullback tensorator;
Stacks 03EL. The private calculations are the ordinary braiding helpers of the trace base change,
specialized below to its native tensorator.
(auxiliary; not a blueprint node). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj

section OrdinaryBraidingHelpers
universe v u' v'
section
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [HasCoequalizers C]
  [∀ A : C, PreservesColimitsOfSize.{0, 0} (tensorLeft A)]
  [∀ A : C, PreservesColimitsOfSize.{0, 0} (tensorRight A)]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [SymmetricCategory D]
  [HasCoequalizers D]
  [∀ A : D, PreservesColimitsOfSize.{0, 0} (tensorLeft A)]
  [∀ A : D, PreservesColimitsOfSize.{0, 0} (tensorRight A)]
  (F : C ⥤ D) [F.Braided] [PreservesColimitsOfShape WalkingParallelPair F]
  {R : C} [MonObj R] [IsCommMonObj R]
private theorem mapMod_braided (M N : Mod C R) :
    Functor.LaxMonoidal.μ (F.mapMod R) M N ≫ (F.mapMod R).map (β_ M N).hom =
      (β_ ((F.mapMod R).obj M) ((F.mapMod R).obj N)).hom ≫
        Functor.LaxMonoidal.μ (F.mapMod R) N M := by
  apply Mod.hom_ext
  rw [← cancel_epi (Mod.tensorObjπ ((F.mapMod R).obj M) ((F.mapMod R).obj N))]
  change Mod.tensorObjπ _ _ ≫ (F.mapModTensorIso M N).hom.hom ≫
      F.map (β_ M N).hom.hom =
    Mod.tensorObjπ _ _ ≫ (β_ ((F.mapMod R).obj M) ((F.mapMod R).obj N)).hom.hom ≫
      (F.mapModTensorIso N M).hom.hom
  erw [reassoc_of% Functor.tensorπ_mapModTensorIso_hom_hom, ← F.map_comp]
  erw [Mod.braiding_hom_hom, Mod.tensorObjπ_braidingHomX, F.map_comp]
  rw [Functor.LaxBraided.braided_assoc]
  erw [Mod.braiding_hom_hom, Mod.tensorObjπ_braidingHomX_assoc,
    Functor.tensorπ_mapModTensorIso_hom_hom]
  rfl
end
section
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [HasCoequalizers C]
  [∀ A : C, PreservesColimitsOfSize.{0, 0} (tensorLeft A)]
  [∀ A : C, PreservesColimitsOfSize.{0, 0} (tensorRight A)]
  {R S : C} [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
  (ψ : S ⟶ R) [IsMonHom ψ] [IsIso ψ]
private theorem comap_braided (M N : Mod C R) :
    Functor.LaxMonoidal.μ (Mod.comap ψ) M N ≫ (Mod.comap ψ).map (β_ M N).hom =
      (β_ ((Mod.comap ψ).obj M) ((Mod.comap ψ).obj N)).hom ≫
        Functor.LaxMonoidal.μ (Mod.comap ψ) N M := by
  apply Mod.hom_ext
  rw [← cancel_epi (Mod.tensorObjπ ((Mod.comap ψ).obj M) ((Mod.comap ψ).obj N))]
  change Mod.tensorObjπ _ _ ≫ (Mod.comapTensorIso ψ M N).hom.hom ≫
      (β_ M N).hom.hom =
    Mod.tensorObjπ _ _ ≫ (β_ ((Mod.comap ψ).obj M) ((Mod.comap ψ).obj N)).hom.hom ≫
      (Mod.comapTensorIso ψ N M).hom.hom
  have ht := Mod.tensorπ_comapTensorIso_hom_hom ψ M N
  rw [← Category.assoc, ht]
  erw [Mod.braiding_hom_hom, Mod.tensorObjπ_braidingHomX]
  erw [Mod.braiding_hom_hom, Mod.tensorObjπ_braidingHomX_assoc,
    Mod.tensorπ_comapTensorIso_hom_hom]
  rfl
end
section Extend
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [HasCoequalizers C] [HasEqualizers C] [MonoidalClosed C]
  [∀ A : C, PreservesColimitsOfSize.{0, 0} (tensorLeft A)]
  [∀ A : C, PreservesColimitsOfSize.{0, 0} (tensorRight A)]
  {R S : C} [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
  (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]
@[instance_reducible]
private noncomputable def extend_braided : (Mod.extendScalars φ).LaxBraided := by
  let ψ := (asIso φ).inv
  let : (Mod.comap ψ : Mod C R ⥤ Mod C S).LaxBraided :=
    { braided := comap_braided ψ }
  let i := Mod.extendScalarsIsoComapInv φ
  let : NatTrans.IsMonoidal i.symm.hom := {
    unit := by simp [i, Functor.Monoidal.transport_ε]
    tensor M N := by simp [i, Functor.Monoidal.transport_μ] }
  exact Functor.LaxBraided.ofNatIso i.symm
end Extend

end OrdinaryBraidingHelpers

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The native composite module pullback preserves the braiding in oplax form.

Source: Stacks 03EL; the ordinary coequalizer calculations of the trace base change.
(auxiliary; not a blueprint node).

Proof. Precompose the mapMod tensorator with the relative tensor coequalizer
map. Its defining equation reduces the braided square to the ambient sheaf
pullback's braided square. The same calculation proves that comap along a ring
isomorphism is braided. Extension along an isomorphism is the specified monoidal
transport of this comap, so it is braided as well. Compose these two braided
functors to obtain the native module pullback. Precompose the resulting lax
braided identity with the inverse tensorator to obtain the oplax identity.
All coequalizer maps used for cancellation are epimorphisms. The argument also
applies to zero modules and the zero coefficient ring. -/
theorem nativeUpperStar_braiding
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    letI := monoidal_upperStar Λ f
    (upperStar Λ f).map (β_ M N).hom ≫ Functor.OplaxMonoidal.δ (upperStar Λ f) N M =
      Functor.OplaxMonoidal.δ (upperStar Λ f) M N ≫
        (β_ ((upperStar Λ f).obj M) ((upperStar Λ f).obj N)).hom := by
  let G := ProEtale.upperStar Ab.{u + 1} f
  let : (G.mapMod (condensedRingObj Λ Y)).LaxBraided :=
    { braided := mapMod_braided G }
  let := extend_braided (condensedPullbackHom Λ f)
  have hμ : Functor.LaxMonoidal.μ (upperStar Λ f) M N ≫
      (upperStar Λ f).map (β_ M N).hom =
        (β_ ((upperStar Λ f).obj M) ((upperStar Λ f).obj N)).hom ≫
          Functor.LaxMonoidal.μ (upperStar Λ f) N M := by
    exact Functor.LaxBraided.braided
      (F := G.mapMod (condensedRingObj Λ Y) ⋙
        Mod.extendScalars (condensedPullbackHom Λ f)) M N
  rw [← cancel_epi (Functor.LaxMonoidal.μ (upperStar Λ f) M N)]
  rw [← Category.assoc, hμ, Category.assoc, Functor.Monoidal.μ_δ,
    Category.comp_id, Functor.Monoidal.μ_δ_assoc]

end AlgebraicGeometry.ProEtale.CondensedRing
