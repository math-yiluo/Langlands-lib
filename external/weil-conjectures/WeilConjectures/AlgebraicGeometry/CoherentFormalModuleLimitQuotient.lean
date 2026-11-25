/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleAffineProjections
import WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-! # Ideal-power quotients of coherent formal-module limit sheaves

Source: Stacks Project, Lemma 087W, the formula M/I^n M = M_n.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem affine_projection {Y : Scheme.{u}} [IsNoetherian Y]
    (J : Y.IdealSheafData) (G : CoherentFormalModule Y J)
    (V : Y.affineOpens) (n : ℕ) :
    Function.Surjective ((limit.π G.obj (op n)).app V.1) ∧
      LinearMap.ker ((limit.π G.obj (op n)).val.app (op V.1)).hom =
        J.ideal V ^ (n + 1) • (⊤ : Submodule Γ(Y, V.1) Γ(limit G.obj, V.1)) := by
  let E := SheafOfModules.evaluation Y.ringCatSheaf (op V.1)
  let e := preservesLimitIso E G.obj
  have he : e.hom ≫ limit.π (G.obj ⋙ E) (op n) =
      E.map (limit.π G.obj (op n)) := preservesLimitIso_hom_π E G.obj (op n)
  obtain ⟨hs, hk⟩ := coherentFormalModule_affine_projections Y J G V n
  have hsurj : Function.Surjective e.hom.hom :=
    (ModuleCat.epi_iff_surjective e.hom).mp inferInstance
  have hinj : Function.Injective e.hom.hom :=
    (ModuleCat.mono_iff_injective e.hom).mp inferInstance
  constructor
  · intro y
    obtain ⟨z, hz⟩ := hs y
    obtain ⟨x, rfl⟩ := hsurj z
    refine ⟨x, ?_⟩
    exact (congrArg (fun f ↦ f x) he).symm.trans hz
  · change LinearMap.ker (E.map (limit.π G.obj (op n))).hom = _
    rw [← he, ModuleCat.hom_comp, LinearMap.ker_comp, hk,
      Submodule.comap_smul'' hinj]
    · simp
    · exact (LinearMap.range_eq_top.mpr hsurj).ge

/-- The canonical limit projection identifies the ideal-power quotient with its level.
Source: Stacks Project, Lemma 087W, the projection-kernel calculation; the local
uniqueness argument in Lemma 088B.
(blueprint: lem-weil-pbc-coherent-formal-module-limit-quotient)

Proof: Evaluation on an affine open V preserves limits. The unique isomorphism of
limiting cones identifies the evaluated projection with the module-limit projection.
Apply coherentFormalModule_affine_projections: it is surjective and has kernel
J(V)^(n+1) times the section limit. Apply the ideal-power clauses of
ideal_times_quasiCoherent_affine_sections to the unit sheaf, which is quasi-coherent:
the power inclusion has range J(V)^(n+1). Multiplication followed by the projection
vanishes on pure tensor germs, since the ideal power annihilates the projected level.
Pure tensors generate tensor stalks, so the composite sheaf morphism is zero.
Hence its sheaf image lies in
the kernel, without any assertion that evaluation preserves images of arbitrary
module sheaves. Conversely the kernel formula expresses each affine kernel section
as a finite sum of ideal-power sections times limit sections. Lift each ideal scalar
through the power inclusion and form the sum of pure tensor sections; its image is
that kernel section. Thus the kernel lies in the multiplication image locally, and
the two subsheaves coincide. Affine surjectivity makes the projection epic.
The projection is consequently
a cokernel of that multiplication-image inclusion. Uniqueness of cokernels gives
the displayed isomorphism and its projection equation. No quasi-coherence of the
limit sheaf is asserted or used. For J=0 the kernel is zero; for J=1 every level is
zero and the quotient is zero. The same calculation includes zero and empty schemes.
-/
theorem coherentFormalModule_limit_quotient {Y : Scheme.{u}} [IsNoetherian Y]
    (J : Y.IdealSheafData) (G : CoherentFormalModule Y J) (n : ℕ) :
    ∃ e : formalModuleQuotient J (n + 1) (limit G.obj) ≅ G.obj.obj (op n),
      formalModuleQuotientπ J (n + 1) (limit G.obj) ≫ e.hom =
        limit.π G.obj (op n) := by
  classical
  let L := limit G.obj
  let p : L ⟶ G.obj.obj (op n) := limit.π G.obj (op n)
  let i := Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι (n + 1)).2 L
  let q := formalModuleQuotientπ J (n + 1) L
  have hz : i ≫ p = 0 := by
    obtain ⟨k, hk⟩ := formalModuleQuotient_factor J p (Nat.le_refl (n + 1))
    rw [show i ≫ p = k ≫ Scheme.idealModuleProductι
      (Scheme.idealSheafPower J.toModulesι (n + 1)).2 (G.obj.obj (op n)) from hk]
    rw [(G.property.2.1 n).eq_zero_of_src
      (Scheme.idealModuleProductι
        (Scheme.idealSheafPower J.toModulesι (n + 1)).2 (G.obj.obj (op n))), comp_zero]
  have hp : ∀ V : Y.affineOpens,
      Function.Surjective (p.app V.1) ∧
        LinearMap.ker (p.val.app (op V.1)).hom =
          J.ideal V ^ (n + 1) • (⊤ : Submodule Γ(Y, V.1) Γ(L, V.1)) :=
    fun V ↦ affine_projection J G V n
  have : Epi p := by
    apply Scheme.Modules.epi_of_forall_exists_app_eq
    intro W y x hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open hx W.2
    obtain ⟨z, hz⟩ := (hp ⟨V, hV⟩).1
      ((G.obj.obj (op n)).presheaf.map (homOfLE hVW).op y)
    exact ⟨V, hVW, hxV, z, hz⟩
  have hker : kernel.ι p ≫ q = 0 := by
    apply (SheafOfModules.toSheaf Y.ringCatSheaf).map_injective
    apply CategoryTheory.Sheaf.hom_ext
    apply TopCat.Sheaf.hom_ext _ _ (B := fun V : Y.affineOpens ↦ V.1)
      (by
        simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using Y.isBasis_affineOpens)
    intro V
    ext s
    change q.app V.1 ((kernel.ι p).app V.1 s) = 0
    have hs : (kernel.ι p).app V.1 s ∈ LinearMap.ker (p.val.app (op V.1)).hom := by
      exact congrArg (fun f ↦ f.app V.1 s) (kernel.condition p)
    rw [(hp V).2] at hs
    have hq : J.ideal V ^ (n + 1) • (⊤ : Submodule Γ(Y, V.1) Γ(L, V.1)) ≤
        LinearMap.ker (q.val.app (op V.1)).hom := by
      apply Submodule.smul_le.mpr
      intro a ha t _
      have := SheafOfModules.isQuasicoherent_unit (R := Y.ringCatSheaf)
      have hpow := ((Scheme.Modules.ideal_times_quasiCoherent_affine_sections J
        (SheafOfModules.unit Y.ringCatSheaf)).2.2.2.1 V).2.2.2
        (n + 1) (Nat.succ_pos n)
      have ha' : a ∈ Set.range
          ((Scheme.idealSheafPower J.toModulesι (n + 1)).2.app V.1) := by
        rw [hpow]
        exact ha
      obtain ⟨b, hb⟩ := ha'
      let : MonoidalCategory Y.Modules := SheafOfModules.monoidalCategory Y.sheaf
      let j := (Scheme.idealSheafPower J.toModulesι (n + 1)).2
      let m := MonoidalCategoryStruct.whiskerRight j L ≫
        (MonoidalCategoryStruct.leftUnitor L).hom
      have hm : m ≫ q = 0 := by
        change m ≫ cokernel.π (image.ι m) = 0
        calc
          _ = (factorThruImage m ≫ image.ι m) ≫ cokernel.π (image.ι m) :=
            congrArg (· ≫ cokernel.π (image.ι m)) (image.fac m).symm
          _ = 0 := by rw [Category.assoc, cokernel.condition, comp_zero]
      have ht : m.app V.1 (Scheme.Modules.tmulSection b t) = a • t := by
        change (MonoidalCategoryStruct.leftUnitor L).hom.app V.1
          ((MonoidalCategoryStruct.whiskerRight j L).app V.1
            (Scheme.Modules.tmulSection b t)) = _
        rw [Scheme.Modules.whiskerRight_app_tmulSection,
          Scheme.Modules.leftUnitor_hom_app_tmulSection']
        exact congrArg (· • t) hb
      change q.app V.1 (a • t) = 0
      rw [← ht]
      exact congrArg (fun f ↦ f.app V.1 (Scheme.Modules.tmulSection b t)) hm
    exact hq hs
  let a := cokernel.desc i p hz
  let b := Abelian.epiDesc p q hker
  have ha : q ≫ a = p := cokernel.π_desc i p hz
  have hb : p ≫ b = q := Abelian.comp_epiDesc p q hker
  have : Epi q := inferInstanceAs (Epi (cokernel.π i))
  refine ⟨⟨a, b, ?_, ?_⟩, ha⟩
  · apply (cancel_epi q).mp
    rw [← Category.assoc, ha, hb, Category.comp_id]
  · apply (cancel_epi p).mp
    rw [← Category.assoc, hb, ha, Category.comp_id]

end AlgebraicGeometry
