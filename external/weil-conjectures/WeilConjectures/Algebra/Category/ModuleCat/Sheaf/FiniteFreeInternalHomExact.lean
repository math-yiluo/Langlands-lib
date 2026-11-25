/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.CategoryTheory.Abelian.ShortExact

import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-! # Exactness of internal Hom from finite free sheaves

Source: literature/stacks-project/cohomology.tex, Tag 0GM8, finite locally free Hom
calculation used in case (2) (blueprint: lem-sc-finite-free-internal-hom-exact).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  {R : Sheaf J CommRingCat.{u}}

private noncomputable def finiteFreeHomIso
    (I : Type u) [Fintype I]
    (E N : SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (hE : E ≅ free (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) I) :
    homObj E N ≅ ∐ (fun _ : I ↦ N) :=
  ((homFunctor R).flip.obj N).mapIso hE.symm.op ≪≫ homObjFreeIso N I ≪≫
    biproduct.isoCoproduct _

private theorem finiteFreeHomIso_projection
    (I : Type u) [Fintype I] [DecidableEq I]
    (E N : SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (hE : E ≅ free (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) I)
    (j : I) :
    (finiteFreeHomIso I E N hE).hom ≫
        Sigma.desc (fun l : I ↦ if l = j then 𝟙 N else 0) =
      homObjMap (ιFree j ≫ hE.inv) (𝟙 N) ≫ (homObjUnitIso N).hom := by
  classical
  have hp : (biproduct.isoCoproduct (fun _ : I ↦ N)).hom ≫
      Sigma.desc (fun l : I ↦ if l = j then 𝟙 N else 0) =
      biproduct.π (fun _ : I ↦ N) j := by
    apply biproduct.hom_ext'
    intro l
    simp [biproduct.isoCoproduct_hom, biproduct.ι_π]
  dsimp only [finiteFreeHomIso, Iso.trans_hom]
  rw [Category.assoc, Category.assoc, hp]
  simp [homObjFreeIso, Functor.opMapBiproductIso,
    biproduct.uniqueUpToIso, Functor.opMapBicone, ιFree]

private theorem finiteFreeHomIso_naturality
    (I : Type u) [Fintype I]
    (E N N' : SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (hE : E ≅ free (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) I)
    (f : N ⟶ N') :
    homObjMap (𝟙 E) f ≫ (finiteFreeHomIso I E N' hE).hom =
      (finiteFreeHomIso I E N hE).hom ≫ Limits.Sigma.map (fun _ : I ↦ f) := by
  classical
  apply (cancel_mono (biproduct.isoCoproduct (fun _ : I ↦ N')).inv).1
  apply biproduct.hom_ext
  intro j
  have hp : (biproduct.isoCoproduct (fun _ : I ↦ N')).inv ≫
      biproduct.π (fun _ : I ↦ N') j =
      Sigma.desc (fun l : I ↦ if l = j then 𝟙 N' else 0) := by
    apply Sigma.hom_ext
    intro l
    simp [biproduct.isoCoproduct_inv, biproduct.ι_π]
  have hm : Limits.Sigma.map (fun _ : I ↦ f) ≫
      Sigma.desc (fun l : I ↦ if l = j then 𝟙 N' else 0) =
      Sigma.desc (fun l : I ↦ if l = j then 𝟙 N else 0) ≫ f := by
    apply Sigma.hom_ext
    intro l
    simp only [Sigma.ι_map_assoc, Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc]
    split_ifs <;> simp
  simp only [Category.assoc, hp]
  rw [hm, ← Category.assoc (finiteFreeHomIso I E N hE).hom,
    finiteFreeHomIso_projection, finiteFreeHomIso_projection]
  rw [← Category.assoc, homObjMap_comp_homObjMap]
  simp only [Category.comp_id]
  have hn : homObjMap (𝟙 (unit _)) f ≫ (homObjUnitIso N').hom =
      (homObjUnitIso N).hom ≫ f := by
    ext U φ
    rfl
  simpa only [← Category.assoc, homObjMap_comp_homObjMap, Category.id_comp] using
    congrArg (homObjMap (ιFree j ≫ hE.inv) (𝟙 N) ≫ ·) hn

set_option backward.isDefEq.respectTransparency false in
private theorem finiteSumShortExact
    (I : Type u) [Finite I]
    (S : ShortComplex (SheafOfModules
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))) (hS : S.ShortExact) :
    ∃ hz : Limits.Sigma.map (fun _ : I ↦ S.f) ≫
        Limits.Sigma.map (fun _ : I ↦ S.g) = 0,
      (ShortComplex.mk (Limits.Sigma.map (fun _ : I ↦ S.f))
        (Limits.Sigma.map (fun _ : I ↦ S.g)) hz).ShortExact := by
  let A := SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  have : PreservesFiniteLimits (colim (J := Discrete I) (C := A)) :=
    preservesFiniteLimits_of_natIso HasBiproductsOfShape.colimIsoLim.symm
  let F : A ⥤ A := Functor.const (Discrete I) ⋙ colim
  have : PreservesFiniteLimits F := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits F := comp_preservesFiniteColimits _ _
  have : F.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_preserves_initial_object (F := F)
  have ht := hS.map_of_exact F
  let e (M : A) : ∐ (fun _ : I ↦ M) ≅ F.obj M :=
    Sigma.isoColimit ((Functor.const (Discrete I)).obj M)
  have hf (M N : A) (f : M ⟶ N) :
      Limits.Sigma.map (fun _ : I ↦ f) ≫ (e N).hom = (e M).hom ≫ F.map f := by
    apply Sigma.hom_ext
    intro j
    have hM : Sigma.ι (fun _ : I ↦ M) j ≫ (e M).hom =
        colimit.ι ((Functor.const (Discrete I)).obj M) (Discrete.mk j) :=
      Sigma.ι_isoColimit_hom ((Functor.const (Discrete I)).obj M) j
    have hN : Sigma.ι (fun _ : I ↦ N) j ≫ (e N).hom =
        colimit.ι ((Functor.const (Discrete I)).obj N) (Discrete.mk j) :=
      Sigma.ι_isoColimit_hom ((Functor.const (Discrete I)).obj N) j
    rw [Sigma.ι_map_assoc,
      ← Category.assoc (Sigma.ι (fun _ : I ↦ M) j) (e M).hom, hM, hN]
    exact (colimit.ι_map ((Functor.const (Discrete I)).map f) (Discrete.mk j)).symm
  have hz : Limits.Sigma.map (fun _ : I ↦ S.f) ≫
      Limits.Sigma.map (fun _ : I ↦ S.g) = 0 := by
    apply (cancel_mono (e S.X₃).hom).1
    rw [Category.assoc, hf, ← Category.assoc, hf, Category.assoc]
    have hzF := (S.map F).zero
    change F.map S.f ≫ F.map S.g = 0 at hzF
    simpa only [zero_comp, comp_zero] using congrArg ((e S.X₁).hom ≫ ·) hzF
  refine ⟨hz, ?_⟩
  let T := ShortComplex.mk (Limits.Sigma.map (fun _ : I ↦ S.f))
    (Limits.Sigma.map (fun _ : I ↦ S.g)) hz
  let eT : T ≅ S.map F :=
    ShortComplex.isoMk (e S.X₁) (e S.X₂) (e S.X₃)
      (hf S.X₁ S.X₂ S.f).symm (hf S.X₂ S.X₃ S.g).symm
  exact ShortComplex.shortExact_of_iso eT.symm ht

/-- Internal Hom from a finite free sheaf preserves a short exact sequence, with the
canonical finite-sum identifications and the induced coordinatewise sequence maps.
Source: literature/stacks-project/cohomology.tex, Tag 0GM8, finite locally free calculation
(blueprint: lem-sc-finite-free-internal-hom-exact).

Proof:
1. On every localized site, precompose with the chosen isomorphism `hE.inv` and evaluate
   on the `r` basis sections. This identifies each internal Hom with the corresponding
   finite direct sum, compatibly with restriction (`def-pur-sheaf-hom`). The coordinate
   equation below specifies exactly these identifications, for `N = ![A, B, C]`.
2. Postcomposition by the sequence maps becomes their coordinatewise finite direct sums.
   Finite direct sums preserve short exact sequences in the abelian category of sheaves
   of modules (`situation-conventions`), also when `r = 0`.
3. The two displayed commutative squares transport that exactness to the internal-Hom
   sequence and provide the claimed canonical identifications.
-/
theorem finiteFreeInternalHomExact
    (r : ℕ)
    (E : SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (hE : E ≅ SheafOfModules.free
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
      (ULift.{u} (Fin r)))
    (S : ShortComplex (SheafOfModules
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))
    (hS : S.ShortExact) :
    ∃ hz : SheafOfModules.homObjMap (𝟙 E) S.f ≫
        SheafOfModules.homObjMap (𝟙 E) S.g = 0,
      (ShortComplex.mk (SheafOfModules.homObjMap (𝟙 E) S.f)
        (SheafOfModules.homObjMap (𝟙 E) S.g) hz).ShortExact ∧
      let N : Fin 3 → SheafOfModules
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) :=
        ![S.X₁, S.X₂, S.X₃]
      ∃ i : ∀ k : Fin 3, SheafOfModules.homObj E (N k) ≅
          ∐ (fun _ : ULift.{u} (Fin r) ↦ N k),
        (∀ (k : Fin 3) (U : C) (φ : (SheafOfModules.homObj E (N k)).val.obj
            (Opposite.op U)) (j : ULift.{u} (Fin r)),
          ((Limits.Sigma.desc (fun l : ULift.{u} (Fin r) ↦
            if l = j then 𝟙 (N k) else 0)).val.app (Opposite.op U))
              (((i k).hom.val.app (Opposite.op U)) φ) =
            (φ.app (Opposite.op (Over.mk (𝟙 U))))
              ((hE.inv.val.app (Opposite.op U))
                (((SheafOfModules.ιFree
                  (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) j).val.app
                    (Opposite.op U)) (1 : R.obj.obj (Opposite.op U))))) ∧
        SheafOfModules.homObjMap (𝟙 E) S.f ≫ (i 1).hom =
          (i 0).hom ≫ Limits.Sigma.map (fun _ ↦ S.f) ∧
        SheafOfModules.homObjMap (𝟙 E) S.g ≫ (i 2).hom =
          (i 1).hom ≫ Limits.Sigma.map (fun _ ↦ S.g) := by
  classical
  let I := ULift.{u} (Fin r)
  let N : Fin 3 → SheafOfModules
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) := ![S.X₁, S.X₂, S.X₃]
  let i (k : Fin 3) : homObj E (N k) ≅ ∐ (fun _ : I ↦ N k) :=
    finiteFreeHomIso I E (N k) hE
  have hf : homObjMap (𝟙 E) S.f ≫ (i 1).hom =
      (i 0).hom ≫ Limits.Sigma.map (fun _ : I ↦ S.f) :=
    finiteFreeHomIso_naturality I E S.X₁ S.X₂ hE S.f
  have hg : homObjMap (𝟙 E) S.g ≫ (i 2).hom =
      (i 1).hom ≫ Limits.Sigma.map (fun _ : I ↦ S.g) :=
    finiteFreeHomIso_naturality I E S.X₂ S.X₃ hE S.g
  have hz : homObjMap (𝟙 E) S.f ≫ homObjMap (𝟙 E) S.g = 0 := by
    rw [homObjMap_comp_homObjMap, S.zero, Category.id_comp]
    ext U φ
    rfl
  obtain ⟨hzSum, hSum⟩ := finiteSumShortExact I S hS
  let T := ShortComplex.mk (homObjMap (𝟙 E) S.f) (homObjMap (𝟙 E) S.g) hz
  let TSum := ShortComplex.mk (Limits.Sigma.map (fun _ : I ↦ S.f))
    (Limits.Sigma.map (fun _ : I ↦ S.g)) hzSum
  let e : T ≅ TSum := ShortComplex.isoMk (i 0) (i 1) (i 2) hf.symm hg.symm
  refine ⟨hz, ShortComplex.shortExact_of_iso e.symm hSum, i, ?_, hf, hg⟩
  intro k U φ j
  have hp := finiteFreeHomIso_projection I E (N k) hE j
  exact congrArg (fun f ↦ f.val.app (Opposite.op U) φ) hp

end SheafOfModules
