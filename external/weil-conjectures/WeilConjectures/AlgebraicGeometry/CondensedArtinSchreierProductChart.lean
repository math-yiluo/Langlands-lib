/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreier
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.StalkLowerStarProj
public import WeilConjectures.CategoryTheory.ModuleObjects.ModuleRegularUnitIso
import WeilConjectures.AlgebraicGeometry.SplitProEtaleModuleProductMap

/-! # The product chart of the condensed Artin–Schreier pushforward -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option quotPrecheck false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The normalized restriction to a sheet, for an arbitrary morphism of schemes.
Source: the counit restriction and monoidal unit comparison
(blueprint: lem-kernel-condensed-product-chart). -/
def condensedRegularSheetProjection
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Y : Scheme.{u}} (p : U ⟶ X)
    (g : Y ⟶ X) (t : Y ⟶ U) (w : t ≫ p = g) :
    (CondensedRing.upperStar Λ g).obj
      ((CondensedRing.lowerStar Λ p).obj (Mod.regular (condensedRingObj Λ U))) ⟶
        Mod.regular (condensedRingObj Λ Y) :=
  CondensedRing.stalkLowerStarProj Λ w (Mod.regular (condensedRingObj Λ U)) ≫
    (Mod.regularMapIso (condensedRingObj Λ U) (CondensedRing.upperStar Λ t)).hom

/-- Evaluation on the sheet given by translation by `a`, normalized to the regular module.
Source: latest blueprint `prop-kernel-lisse.proof.md`, splitting chart
(blueprint: lem-kernel-condensed-product-chart). -/
def condensedArtinSchreierChartProjection
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [Fintype k] (a : k) :
    (CondensedRing.upperStar Λ
      (AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k))).obj
        (condensedArtinSchreierPushforward Λ k) ⟶
      Mod.regular (condensedRingObj Λ (AffineSpace PUnit (Spec (.of k)))) :=
  condensedRegularSheetProjection Λ
    (AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k))
    (AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k))
    (Etale.artinSchreierTranslation k a)
    (Etale.artinSchreierTranslation_comp_artinSchreierMap k a)

private theorem transport_symm
    {T C D : Type*} [Category C] [Category D]
    (H : T → (C ⥤ D)) {a b : T} (h : a = b) :
    eqToIso (congrArg H h.symm) = (eqToIso (congrArg H h)).symm := by
  subst b
  rfl

private theorem sheet_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Y : Scheme.{u}} (p : U ⟶ X) (g : Y ⟶ X)
    (t : Y ⟶ U) (w : t ≫ p = g)
    (N : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)) :
    CondensedRing.stalkLowerStarProj Λ w N =
      ((eqToIso (congrArg (CondensedRing.upperStar Λ) w)).symm ≪≫
        CondensedRing.upperStarComp Λ t p).hom.app ((CondensedRing.lowerStar Λ p).obj N) ≫
      (CondensedRing.upperStar Λ t).map
        ((CondensedRing.upperStarLowerStarAdjunction Λ p).counit.app N) := by
  have hh : CondensedRing.upperStarCongr Λ w.symm =
      (eqToIso (congrArg (CondensedRing.upperStar Λ) w)).symm :=
    transport_symm (CondensedRing.upperStar Λ) w
  calc
    _ = (CondensedRing.upperStarCongr Λ w.symm).hom.app
        ((CondensedRing.lowerStar Λ p).obj N) ≫
      (CondensedRing.upperStarComp Λ t p).hom.app
        ((CondensedRing.lowerStar Λ p).obj N) ≫
      (CondensedRing.upperStar Λ t).map
        ((CondensedRing.upperStarLowerStarAdjunction Λ p).counit.app N) :=
      CondensedRing.stalkLowerStarProj_eq Λ w N
    _ = _ := by rw [hh]; simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc]

private theorem sheets_product
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Y : Scheme.{u}} (p : U ⟶ X)
    (g : Y ⟶ X) [WeaklyEtale g] (n : ℕ) (t : Fin n → (Y ⟶ U))
    (w : ∀ j, t j ≫ p = g)
    (hc : Nonempty (IsColimit (Cofan.mk (pullback p g)
      (fun j ↦ pullback.lift (t j) (𝟙 Y) (by simpa only [Category.id_comp] using w j)))))
    (N : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)) :
    IsIso (Pi.lift (fun j ↦ CondensedRing.stalkLowerStarProj Λ (w j) N)) := by
  have h := CondensedRing.splitProEtaleModuleProductMap_isIso Λ p g n t w hc N
  have hs : (fun j ↦ CondensedRing.stalkLowerStarProj Λ (w j) N) =
      (fun j ↦ ((eqToIso (congrArg (CondensedRing.upperStar Λ) (w j))).symm ≪≫
        CondensedRing.upperStarComp Λ (t j) p).hom.app
          ((CondensedRing.lowerStar Λ p).obj N) ≫
        (CondensedRing.upperStar Λ (t j)).map
          ((CondensedRing.upperStarLowerStarAdjunction Λ p).counit.app N)) := by
    funext j
    exact sheet_eq Λ p g (t j) (w j) N
  rw [hs]
  exact h

private theorem regular_sheets_finite
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Y : Scheme.{u}} (p : U ⟶ X)
    (g : Y ⟶ X) [WeaklyEtale g] (n : ℕ) (t : Fin n → (Y ⟶ U))
    (w : ∀ j, t j ≫ p = g)
    (hc : Nonempty (IsColimit (Cofan.mk (pullback p g)
      (fun j ↦ pullback.lift (t j) (𝟙 Y) (by simpa only [Category.id_comp] using w j))))) :
    IsIso (Pi.lift (fun j ↦ CondensedRing.stalkLowerStarProj Λ (w j)
      (Mod.regular (condensedRingObj Λ U)))) :=
  sheets_product Λ p g n t w hc (Mod.regular (condensedRingObj Λ U))

private def sheet_regular_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U Y : Scheme.{u}} (t : Y ⟶ U) :
    (CondensedRing.upperStar Λ t).obj (Mod.regular (condensedRingObj Λ U)) ≅
      Mod.regular (condensedRingObj Λ Y) :=
  Mod.regularMapIso (condensedRingObj Λ U) (CondensedRing.upperStar Λ t)

private theorem sheet_regular_iso_hom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U Y : Scheme.{u}} (t : Y ⟶ U) :
    (sheet_regular_iso Λ t).hom =
      (Mod.regularMapIso (condensedRingObj Λ U) (CondensedRing.upperStar Λ t)).hom := rfl

private theorem regular_sheets_product
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Y : Scheme.{u}} (p : U ⟶ X)
    (g : Y ⟶ X) [WeaklyEtale g] (n : ℕ) (t : Fin n → (Y ⟶ U))
    (w : ∀ j, t j ≫ p = g)
    (hc : Nonempty (IsColimit (Cofan.mk (pullback p g)
      (fun j ↦ pullback.lift (t j) (𝟙 Y)
        (by simpa only [Category.id_comp] using w j))))) :
    IsIso (Pi.lift (fun j ↦ condensedRegularSheetProjection Λ p g (t j) (w j))) := by
  let ρ := fun j ↦ CondensedRing.stalkLowerStarProj Λ (w j)
    (Mod.regular (condensedRingObj Λ U))
  let e := fun j ↦ sheet_regular_iso Λ (t j)
  have : IsIso (Pi.lift ρ) := regular_sheets_finite Λ p g n t w hc
  have hf : Pi.lift (fun j ↦ condensedRegularSheetProjection Λ p g (t j) (w j)) =
      Pi.lift ρ ≫ (Pi.mapIso e).hom := by
    apply Pi.hom_ext
    intro j
    simp only [Category.assoc, Pi.mapIso_hom_π, Pi.lift_comp_π, Pi.lift_comp_π_assoc]
    simp only [condensedRegularSheetProjection, e, sheet_regular_iso_hom, ρ]
  rw [hf]
  infer_instance

private theorem sheet_condition (k : Type u) [Field k] [Fintype k] (a : k) :
    Etale.artinSchreierTranslation k a ≫
      AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k) =
    𝟙 (AffineSpace PUnit (Spec (.of k))) ≫
      AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k) := by
  simpa only [Category.id_comp] using
    Etale.artinSchreierTranslation_comp_artinSchreierMap k a

private theorem sheets_colimit (k : Type u) [Field k] [Fintype k] :
    let A := AffineSpace PUnit.{u + 1} (Spec (.of k));
    let q : A ⟶ A := AffineSpace.artinSchreierMap PUnit _ (Fintype.card k);
    Nonempty (IsColimit (Cofan.mk (pullback q q)
      (fun j : Fin (Fintype.card k) ↦ pullback.lift
        (Etale.artinSchreierTranslation k ((Fintype.equivFin k).symm j)) (𝟙 A)
        (sheet_condition k ((Fintype.equivFin k).symm j))))) := by
  classical
  let A := AffineSpace PUnit.{u + 1} (Spec (.of k))
  let q : A ⟶ A := AffineSpace.artinSchreierMap PUnit _ (Fintype.card k)
  let σ : k → (A ⟶ A) := Etale.artinSchreierTranslation k
  let ε : Fin (Fintype.card k) ≃ k := (Fintype.equivFin k).symm
  let θ : Fin (Fintype.card k) ≃ (PUnit.{u + 1} → k) :=
    ε.trans (Equiv.funUnique PUnit k).symm
  let t : Fin (Fintype.card k) → (A ⟶ A) := fun j ↦ σ (ε j)
  have w (j : Fin (Fintype.card k)) : t j ≫ q = q :=
    Etale.artinSchreierTranslation_comp_artinSchreierMap k (ε j)
  have : IsIso (AffineSpace.artinSchreierTorsorMap (n := PUnit.{u + 1})
      k (Scheme.ΓSpecIso (.of k)).inv.hom) :=
    AffineSpace.isIso_artinSchreierTorsorMap k (Scheme.ΓSpecIso (.of k)).inv.hom
  have hd : (Sigma.desc fun j ↦ pullback.lift (t j) (𝟙 A)
      (by simpa only [Category.id_comp] using w j)) =
      (Sigma.reindex θ (fun _ : PUnit.{u + 1} → k ↦ A)).hom ≫
        AffineSpace.artinSchreierTorsorMap k (Scheme.ΓSpecIso (.of k)).inv.hom ≫
          (pullbackSymmetry q q).hom := by
    apply Sigma.hom_ext
    intro j
    rw [Sigma.ι_comp_desc]
    have hr := Sigma.ι_reindex_hom θ (fun _ : PUnit.{u + 1} → k ↦ A) j
    dsimp only [Function.comp_def] at hr
    rw [reassoc_of% hr]
    apply pullback.hom_ext <;>
      simp only [AffineSpace.artinSchreierTorsorMap, Category.assoc,
        pullback.lift_fst, pullback.lift_snd, pullbackSymmetry_hom_comp_fst,
        pullbackSymmetry_hom_comp_snd]
    all_goals
      erw [Sigma.ι_comp_desc_assoc]
      first | erw [pullback.lift_snd] | erw [pullback.lift_fst]
      all_goals simp [t, σ, Etale.artinSchreierTranslation, θ, ε, Equiv.funUnique]
  have : IsIso (Sigma.desc fun j ↦ pullback.lift (t j) (𝟙 A)
      (by simpa only [Category.id_comp] using w j)) := by rw [hd]; infer_instance
  let c := Cofan.mk (pullback q q)
    (fun j ↦ pullback.lift (t j) (𝟙 A) (by simpa only [Category.id_comp] using w j))
  have : IsIso (Sigma.desc c.inj) := by
    change IsIso (Sigma.desc fun j ↦ pullback.lift (t j) (𝟙 A) _)
    rw [hd]
    infer_instance
  have hc : Nonempty (IsColimit (Cofan.mk (pullback q q)
      (fun j ↦ pullback.lift (t j) (𝟙 A) (by simpa only [Category.id_comp] using w j)))) :=
    ⟨Cofan.isColimitOfIsIsoSigmaDesc c⟩
  exact hc

/-- The pullback of the Artin–Schreier pushforward is the product of the regular modules,
with the counit-defined sheet evaluations enumerated by Fin |k| as coordinates.

Source: latest blueprint `prop-kernel-lisse.proof.md`, first paragraph, and the proved
Artin–Schreier torsor decomposition
(blueprint: lem-kernel-condensed-product-chart).

Proof. The Artin–Schreier torsor map identifies the self fibre product with the coproduct
of copies of the affine line indexed by the additive field. Swap the two projections
so that the sheet labelled `a` is `(σ_a,id)`. Reindex by `Fin |k|` and apply the canonical
split-cover product-map theorem to the regular module. Normalize each pulled-back regular
module using the strong monoidal unit comparison. The resulting product isomorphism
has exactly the displayed enumerated sheet evaluations as its projections. -/
theorem condensedArtinSchreierChart_isIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [Fintype k] :
    IsIso (Pi.lift (fun j : Fin (Fintype.card k) ↦
      condensedArtinSchreierChartProjection Λ k ((Fintype.equivFin k).symm j))) := by
  have : AlgebraicGeometry.Etale
      (AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k)) :=
    Etale.etale_artinSchreierMap (k := k)
  rw [show condensedArtinSchreierChartProjection Λ k =
    (fun a : k ↦ condensedRegularSheetProjection Λ
      (AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k))
      (AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k))
      (Etale.artinSchreierTranslation k a)
      (Etale.artinSchreierTranslation_comp_artinSchreierMap k a)) from rfl]
  exact regular_sheets_product Λ _ _ (Fintype.card k)
    (fun j ↦ Etale.artinSchreierTranslation k ((Fintype.equivFin k).symm j))
    (fun j ↦ Etale.artinSchreierTranslation_comp_artinSchreierMap k
      ((Fintype.equivFin k).symm j)) (sheets_colimit k)

end AlgebraicGeometry.ProEtale
