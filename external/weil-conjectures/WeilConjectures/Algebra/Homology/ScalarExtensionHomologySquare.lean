/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Transposing an ordinary homology square by scalar extension

Source: Stacks Project, Tags 05G3 and 06Y6.
(blueprint: lem-pc-scalar-extension-homology-square). -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped TensorProduct ChangeOfRings

namespace ModuleCat

private theorem map_homology_pi {C D : Type*} [Category C] [Category D]
    [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms D]
    (S : ShortComplex C) [S.HasHomology]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] [F.PreservesHomology] :
    (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
      (S.mapCyclesIso F).hom ≫ F.map S.homologyπ := by
  rw [ShortComplex.LeftHomologyData.mapHomologyIso_eq (hl := S.leftHomologyData)]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom_assoc]
  rw [ShortComplex.LeftHomologyData.mapCyclesIso_eq (hl := S.leftHomologyData)]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
  change _ ≫ F.map S.leftHomologyData.π ≫ F.map S.leftHomologyData.homologyIso.inv = _
  rw [← F.map_comp, ShortComplex.LeftHomologyData.π_comp_homologyIso_inv]
  simp only [Functor.map_comp]

private theorem forget_restrict_cyclesIso
    (E D : Type u) [CommRing E] [CommRing D] (f : E →+* D)
    (S : ShortComplex (ModuleCat.{u} D)) :
    ((S.map (ModuleCat.restrictScalars f)).mapCyclesIso
      (forget₂ (ModuleCat.{u} E) AddCommGrpCat.{u})).hom ≫
        (forget₂ (ModuleCat.{u} E) AddCommGrpCat.{u}).map
          (S.mapCyclesIso (ModuleCat.restrictScalars f)).hom =
    (S.mapCyclesIso (forget₂ (ModuleCat.{u} D) AddCommGrpCat.{u})).hom := by
  apply (cancel_mono ((forget₂ (ModuleCat.{u} D) AddCommGrpCat.{u}).map S.iCycles)).1
  simp only [Category.assoc]
  rw [← ModuleCat.forget₂_map_restrictScalars f S.iCycles]
  rw [← Functor.map_comp, ShortComplex.mapCyclesIso_hom_iCycles]
  rw [ShortComplex.mapCyclesIso_hom_iCycles]
  rw [ModuleCat.forget₂_map_restrictScalars, ShortComplex.mapCyclesIso_hom_iCycles]
  rfl

private theorem forget_restrict_homologyIso
    (E D : Type u) [CommRing E] [CommRing D] (f : E →+* D)
    (S : ShortComplex (ModuleCat.{u} D)) :
    ((S.map (ModuleCat.restrictScalars f)).mapHomologyIso
      (forget₂ (ModuleCat.{u} E) AddCommGrpCat.{u})).hom ≫
        (forget₂ (ModuleCat.{u} E) AddCommGrpCat.{u}).map
          (S.mapHomologyIso (ModuleCat.restrictScalars f)).hom =
    (S.mapHomologyIso (forget₂ (ModuleCat.{u} D) AddCommGrpCat.{u})).hom := by
  apply (cancel_epi (((S.map (ModuleCat.restrictScalars f)).map
    (forget₂ (ModuleCat.{u} E) AddCommGrpCat.{u})).homologyπ)).1
  rw [← Category.assoc, map_homology_pi (S.map (ModuleCat.restrictScalars f))
    (forget₂ (ModuleCat.{u} E) AddCommGrpCat.{u})]
  simp only [Category.assoc]
  rw [← Functor.map_comp, map_homology_pi, Functor.map_comp]
  rw [← Category.assoc, forget_restrict_cyclesIso]
  rw [ModuleCat.forget₂_map_restrictScalars]
  exact (map_homology_pi S (forget₂ (ModuleCat.{u} D) AddCommGrpCat.{u})).symm

/-- An ordinary additive cohomology square and a coefficient-complex square imply
its scalar-extended square. Source: Stacks Project, Tags 05G3 and 06Y6.
(blueprint: lem-pc-scalar-extension-homology-square).

Proof: equality of D-linear maps is tested on the generators 1 tensor m.
The adjunction identities express both localized maps on these generators through
ordinary homology. Apply homology to the coefficient-complex square and use
naturality of the homology isomorphism for the exact forgetful functors. Substitute
the ordinary cohomology square, then the generator formula for e. Faithfulness of
forgetting the D-action gives equality. No flatness of D or invertibility of any
map is needed; zero rings, zero modules and zero complexes satisfy the same argument. -/
theorem scalarExtension_homology_square
    (E F D : Type u) [CommRing E] [CommRing F] [CommRing D]
    (f : E →+* D) (g : F →+* D)
    (M : ModuleCat.{u} E) (N : ModuleCat.{u} F)
    (X : CochainComplex (ModuleCat.{u} E) ℤ)
    (Y : CochainComplex (ModuleCat.{u} F) ℤ)
    (XL YL : CochainComplex (ModuleCat.{u} D) ℤ) (i : ℤ)
    (a : M ⟶ X.homology i) (b : N ⟶ Y.homology i)
    (vX : X ⟶ ((restrictScalars f).mapHomologicalComplex (.up ℤ)).obj XL)
    (vY : Y ⟶ ((restrictScalars g).mapHomologicalComplex (.up ℤ)).obj YL)
    (aD : (extendScalars f).obj M ⟶ XL.homology i)
    (bD : (extendScalars g).obj N ⟶ YL.homology i)
    (ha : (extendRestrictScalarsAdj f).unit.app M ≫ (restrictScalars f).map aD =
      a ≫ HomologicalComplex.homologyMap vX i ≫
        (XL.sc i |>.mapHomologyIso (restrictScalars f)).hom)
    (hb : (extendRestrictScalarsAdj g).unit.app N ≫ (restrictScalars g).map bD =
      b ≫ HomologicalComplex.homologyMap vY i ≫
        (YL.sc i |>.mapHomologyIso (restrictScalars g)).hom)
    (c : (forget₂ (ModuleCat.{u} E) AddCommGrpCat.{u}).obj M ⟶
      (forget₂ (ModuleCat.{u} F) AddCommGrpCat.{u}).obj N)
    (φ : ((forget₂ (ModuleCat.{u} E) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℤ)).obj X ⟶
      ((forget₂ (ModuleCat.{u} F) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℤ)).obj Y)
    (hφ : (forget₂ (ModuleCat.{u} E) AddCommGrpCat.{u}).map a ≫
        (X.sc i |>.mapHomologyIso (forget₂ (ModuleCat.{u} E) AddCommGrpCat.{u})).inv ≫
          HomologicalComplex.homologyMap φ i =
      c ≫ (forget₂ (ModuleCat.{u} F) AddCommGrpCat.{u}).map b ≫
        (Y.sc i |>.mapHomologyIso (forget₂ (ModuleCat.{u} F) AddCommGrpCat.{u})).inv)
    (τ : XL ⟶ YL)
    (hv : ((forget₂ (ModuleCat.{u} E) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℤ)).map vX ≫
        ((forget₂ (ModuleCat.{u} D) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℤ)).map τ =
      φ ≫ ((forget₂ (ModuleCat.{u} F) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℤ)).map vY)
    (e : (extendScalars f).obj M ⟶ (extendScalars g).obj N)
    (he : ∀ m : M, e ((1 : D) ⊗ₜ[E,f] m) = (1 : D) ⊗ₜ[F,g] (show N from c m)) :
    aD ≫ HomologicalComplex.homologyMap τ i = e ≫ bD := by
  let UE := forget₂ (ModuleCat.{u} E) AddCommGrpCat.{u}
  let UF := forget₂ (ModuleCat.{u} F) AddCommGrpCat.{u}
  let UD := forget₂ (ModuleCat.{u} D) AddCommGrpCat.{u}
  let sx := (X.sc i).mapHomologyIso UE
  let sy := (Y.sc i).mapHomologyIso UF
  let sxl := (XL.sc i).mapHomologyIso UD
  let syl := (YL.sc i).mapHomologyIso UD
  have hx : UE.map (HomologicalComplex.homologyMap vX i) ≫
      UE.map ((XL.sc i).mapHomologyIso (restrictScalars f)).hom =
      sx.inv ≫ HomologicalComplex.homologyMap
        ((UE.mapHomologicalComplex (.up ℤ)).map vX) i ≫ sxl.hom := by
    apply (cancel_epi sx.hom).1
    simp only [Iso.hom_inv_id_assoc]
    let tx := ((((restrictScalars f).mapHomologicalComplex (.up ℤ)).obj
      XL).sc i).mapHomologyIso UE
    have hn : HomologicalComplex.homologyMap
        ((UE.mapHomologicalComplex (.up ℤ)).map vX) i ≫
          tx.hom = sx.hom ≫
              UE.map (HomologicalComplex.homologyMap vX i) := by
      exact ShortComplex.mapHomologyIso_hom_naturality
        ((HomologicalComplex.shortComplexFunctor _ (.up ℤ) i).map vX) UE
    have hc : tx.hom ≫
          UE.map ((XL.sc i).mapHomologyIso (restrictScalars f)).hom = sxl.hom := by
      exact forget_restrict_homologyIso E D f (XL.sc i)
    rw [← Category.assoc, ← hn, Category.assoc, hc]
  have hy : UF.map (HomologicalComplex.homologyMap vY i) ≫
      UF.map ((YL.sc i).mapHomologyIso (restrictScalars g)).hom =
      sy.inv ≫ HomologicalComplex.homologyMap
        ((UF.mapHomologicalComplex (.up ℤ)).map vY) i ≫ syl.hom := by
    apply (cancel_epi sy.hom).1
    simp only [Iso.hom_inv_id_assoc]
    let ty := ((((restrictScalars g).mapHomologicalComplex (.up ℤ)).obj
      YL).sc i).mapHomologyIso UF
    have hn : HomologicalComplex.homologyMap
        ((UF.mapHomologicalComplex (.up ℤ)).map vY) i ≫
          ty.hom = sy.hom ≫
              UF.map (HomologicalComplex.homologyMap vY i) := by
      exact ShortComplex.mapHomologyIso_hom_naturality
        ((HomologicalComplex.shortComplexFunctor _ (.up ℤ) i).map vY) UF
    have hc : ty.hom ≫
          UF.map ((YL.sc i).mapHomologyIso (restrictScalars g)).hom = syl.hom := by
      exact forget_restrict_homologyIso F D g (YL.sc i)
    rw [← Category.assoc, ← hn, Category.assoc, hc]
  have hax := congrArg UE.map ha
  have hby := congrArg UF.map hb
  dsimp only [UE, UF, UD] at hax hby
  simp only [Functor.map_comp, forget₂_map_restrictScalars] at hax hby
  rw [hx] at hax
  rw [hy] at hby
  have ht : sxl.hom ≫ UD.map (HomologicalComplex.homologyMap τ i) =
      HomologicalComplex.homologyMap ((UD.mapHomologicalComplex (.up ℤ)).map τ) i ≫
        syl.hom := by
    exact (ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} D) (.up ℤ) i).map τ) UD).symm
  have hvH := congrArg (fun ψ ↦ HomologicalComplex.homologyMap ψ i) hv
  simp only [HomologicalComplex.homologyMap_comp] at hvH
  have hw : UE.map ((extendRestrictScalarsAdj f).unit.app M) ≫
      UD.map aD ≫ UD.map (HomologicalComplex.homologyMap τ i) =
      c ≫ UF.map ((extendRestrictScalarsAdj g).unit.app N) ≫ UD.map bD := by
    calc
      _ = UE.map a ≫ sx.inv ≫ HomologicalComplex.homologyMap
          ((UE.mapHomologicalComplex (.up ℤ)).map vX) i ≫
          HomologicalComplex.homologyMap ((UD.mapHomologicalComplex (.up ℤ)).map τ) i ≫
          syl.hom := by
        rw [← Category.assoc, hax]
        simp only [Category.assoc]
        rw [ht]
      _ = UE.map a ≫ sx.inv ≫ HomologicalComplex.homologyMap φ i ≫
          HomologicalComplex.homologyMap ((UF.mapHomologicalComplex (.up ℤ)).map vY) i ≫
          syl.hom := by
        simpa only [Category.assoc] using congrArg
          (fun k ↦ UE.map a ≫ sx.inv ≫ k ≫ syl.hom) hvH
      _ = c ≫ UF.map b ≫ sy.inv ≫ HomologicalComplex.homologyMap
          ((UF.mapHomologicalComplex (.up ℤ)).map vY) i ≫ syl.hom := by
        simpa only [Category.assoc] using congrArg
          (fun k ↦ k ≫ HomologicalComplex.homologyMap
            ((UF.mapHomologicalComplex (.up ℤ)).map vY) i ≫ syl.hom) hφ
      _ = _ := by
        simpa only [Category.assoc] using congrArg (fun k ↦ c ≫ k) hby.symm
  apply ExtendScalars.hom_ext
  intro m
  change HomologicalComplex.homologyMap τ i (aD ((1 : D) ⊗ₜ[E,f] m)) =
    bD (e ((1 : D) ⊗ₜ[E,f] m))
  rw [he]
  exact congrArg (fun k ↦ k m) hw

end ModuleCat
