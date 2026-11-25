/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import Mathlib.AlgebraicGeometry.FunctionField
import WeilConjectures.AlgebraicGeometry.QuasiCoherentIdealZeroSetAffine
import WeilConjectures.AlgebraicGeometry.IntegralIdealAffineSections

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
/-- The generic stalk criterion for a nonzero ideal sheaf on an integral scheme.
Source: Stacks Project, Cohomology of Schemes, proof of Lemma 01YL.
Proof: Choose an affine neighborhood U of the generic point. The affine zero-set theorem
and the fact that the corresponding prime is zero identify stalk surjectivity with a
nonzero section ideal on U. The affine-section criterion gives surjectivity for a nonzero
ideal, while the zero ideal has zero section ideal and cannot give surjectivity.
For nontriviality, lift a nonzero element of J(U) to a section of J.toModules and take its
germ. If this germ vanished, its image germ in the structure sheaf would vanish. Equality
of germs gives zero after restriction to a smaller nonempty open, contradicting the
injectivity of restriction maps on an integral scheme. Conversely, for the zero ideal,
represent any stalk element by a section and shrink to an affine neighborhood. Its image
belongs to the zero section ideal; sectionwise injectivity makes the restricted section
zero, so the original germ is zero. Thus a nontrivial stalk excludes the zero ideal.
(blueprint: lem-weil-pbc-integral-scheme-ideal-generic-stalk-stalk)
-/
theorem integral_ideal_nonzero_iff_generic_stalk (X : Scheme.{u}) [IsIntegral X]
    (J : X.IdealSheafData) :
    (J ≠ ⊥ ↔
        Nontrivial ((RingedSpace.moduleStalkFunctor X.toRingedSpace (genericPoint X)).obj
          J.toModules)) ∧
      (J ≠ ⊥ ↔
        Function.Surjective
          ((RingedSpace.moduleStalkFunctor X.toRingedSpace (genericPoint X)).map
            J.toModulesι).hom) := by
  let F : TopCat.Presheaf Ab X.toTopCat := J.toModules.val.presheaf
  let O := (SheafOfModules.unit X.ringCatSheaf : X.Modules)
  let G : TopCat.Presheaf Ab X.toTopCat := O.val.presheaf
  let f : F ⟶ G := (PresheafOfModules.toPresheaf _).map J.toModulesι.val
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show genericPoint X ∈ (⊤ : X.Opens) from trivial) isOpen_univ
  let _ : Nonempty U := ⟨⟨genericPoint X, hxU⟩⟩
  have hsurj : Function.Surjective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace (genericPoint X)).map
        J.toModulesι).hom ↔ J.ideal ⟨U, hU⟩ ≠ ⊥ := by
    rw [(quasi_coherent_ideal_zero_set_affine X J).2.1 ⟨U, hU⟩
      ⟨genericPoint X, hxU⟩]
    have hp : (hU.primeIdealOf ⟨genericPoint X, hxU⟩).asIdeal = ⊥ := by
      rw [hU.primeIdealOf_genericPoint, genericPoint_eq_bot_of_affine]
      rfl
    rw [hp, le_bot_iff]
  have hn : J ≠ ⊥ ↔ Nontrivial (F.stalk (genericPoint X)) := by
    constructor
    · intro hJ
      have hi := (integral_ideal_nonzero_iff_affine_sections X J).mp hJ ⟨U, hU⟩
        inferInstance
      obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hi
      have har : a ∈ Set.range (J.toModulesι.app U) := by
        rw [J.range_toModulesι_app ⟨U, hU⟩]
        exact ha
      obtain ⟨m, hm⟩ := har
      refine ⟨⟨F.germ U (genericPoint X) hxU m, 0, ?_⟩⟩
      intro he
      have he' := congrArg ((TopCat.Presheaf.stalkFunctor Ab (genericPoint X)).map f) he
      rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, map_zero] at he'
      change G.germ U (genericPoint X) hxU (J.toModulesι.app U m) = 0 at he'
      rw [hm, ← map_zero (G.germ U (genericPoint X) hxU).hom] at he'
      obtain ⟨W, hxW, iU, iV, hw⟩ := G.germ_eq (genericPoint X) hxU hxU a 0 he'
      change X.presheaf.map iU.op a = X.presheaf.map iV.op 0 at hw
      rw [map_zero] at hw
      exact ha0 (map_injective_of_isIntegral X iU
        (H := ⟨⟨genericPoint X, hxW⟩⟩) (hw.trans (map_zero _).symm))
    · intro h hb
      have hz (m : F.stalk (genericPoint X)) : m = 0 := by
        obtain ⟨V, hxV, m, rfl⟩ := F.exists_germ_eq m
        obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
          X.isBasis_affineOpens.exists_subset_of_mem_open hxV V.isOpen
        have hm : J.toModulesι.app W (F.map (homOfLE hWV).op m) = 0 := by
          have hr : J.toModulesι.app W (F.map (homOfLE hWV).op m) ∈ J.ideal ⟨W, hW⟩ := by
            change _ ∈ (J.ideal ⟨W, hW⟩ : Set Γ(X, W))
            rw [← J.range_toModulesι_app ⟨W, hW⟩]
            exact ⟨_, rfl⟩
          simpa [hb, IdealSheafData.ideal_bot] using hr
        have hm0 := J.injective_toModulesι_app W (hm.trans (map_zero _).symm)
        rw [← F.germ_res_apply (homOfLE hWV) (genericPoint X) hxW m]
        exact (congrArg (F.germ W (genericPoint X) hxW) hm0).trans
          (map_zero (F.germ W (genericPoint X) hxW).hom)
      obtain ⟨a, b, hab⟩ := h.exists_pair_ne
      exact hab ((hz a).trans (hz b).symm)
  refine ⟨hn, ?_⟩
  constructor
  · intro hJ
    exact hsurj.mpr ((integral_ideal_nonzero_iff_affine_sections X J).mp hJ
      ⟨U, hU⟩ inferInstance)
  · intro hs hb
    have hi := hsurj.mp hs
    exact hi (by simp [hb, IdealSheafData.ideal_bot])

end AlgebraicGeometry.Scheme
