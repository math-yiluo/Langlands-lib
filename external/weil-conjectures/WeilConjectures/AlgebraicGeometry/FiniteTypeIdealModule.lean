/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import WeilConjectures.Compactification.FiniteTypeExtension
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Finite-type ideal modules
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- A finite-type ideal sheaf defines a sheaf of modules of finite type.

Source: Stacks Project, Properties, Tag 01PG, and Sheaves of Modules,
Tag 01B4 (the local finite-generator definition).
(blueprint: lem-pqf-finite-type-ideal-module).

Proof: Cover X by affine opens U. By hI, choose a finite family generating I.ideal U.
The range equality for I.toModulesι on U lifts these generators to sections of the
ideal module; injectivity makes the lifts unique. On every smaller affine open V in U,
map_ideal identifies its ideal with the extension of I.ideal U, so the restricted
generators generate the ideal there. The range equality and injectivity identify these ideal
generators with generators of the module sections. The resulting morphism from the
finite free sheaf to I.toModules restricted to U is therefore surjective on this
basis, hence locally surjective and an epimorphism. These finite generating families
on the affine cover give LocalGeneratorsData.IsFiniteType, and therefore IsFiniteType.
For the zero ideal use the empty generating family; the empty scheme has an empty
affine cover, so the same local criterion applies. No compactness is required. -/
theorem isFiniteType_toModules_sheaf {X : Scheme.{u}} (I : X.IdealSheafData)
    (hI : I.ofFiniteType) : I.toModules.IsFiniteType := by
  classical
  have hgen (U : X.affineOpens) :
      ∃ σ : (I.toModules.over U.1).GeneratingSections, σ.IsFiniteType := by
    obtain ⟨t, ht⟩ := hI U le_top
    have hm (j : t) : ∃ m : Γ(I.toModules, U.1), I.toModulesι.app U.1 m = j.val := by
      have hj : (j.val : Γ(X, U.1)) ∈ I.ideal U := by
        rw [← ht]
        exact Ideal.subset_span j.property
      exact (I.range_toModulesι_app U).superset hj
    choose m hm using hm
    let G : t → (I.toModules.over U.1).sections := fun j ↦
      PresheafOfModules.sectionsMk
        (fun V ↦ I.toModules.val.map V.unop.hom.op (m j)) (by
          intro V W f
          change I.toModules.presheaf.map f.unop.left.op
              (I.toModules.presheaf.map V.unop.hom.op (m j)) =
            I.toModules.presheaf.map W.unop.hom.op (m j)
          rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, Over.w])
    let π : SheafOfModules.free t ⟶ I.toModules.over U.1 :=
      (I.toModules.over U.1).freeHomEquiv.symm G
    have hsurj (V : Over U.1) (hV : IsAffineOpen V.left) :
        Function.Surjective (π.val.app (.op V)) := by
      let V' : X.affineOpens := ⟨V.left, hV⟩
      let P := (SheafOfModules.free (R := X.ringCatSheaf.over U.1) t).val.obj (.op V)
      let L : P →ₗ[Γ(X, V.left)] Γ(X, V.left) :=
        (I.toModulesι.val.app (.op V.left)).hom.comp (π.val.app (.op V)).hom
      have hle : I.ideal V' ≤ LinearMap.range L := by
        rw [← I.map_ideal (leOfHom V.hom), ← ht, Ideal.map_span]
        apply Submodule.span_le.mpr
        rintro x ⟨j, hj, rfl⟩
        let q := (SheafOfModules.freeSection (R := X.ringCatSheaf.over U.1) (⟨j, hj⟩ : t))
        refine ⟨q.val (.op V), ?_⟩
        have hq := congrArg (fun s ↦ s.val (.op V))
          (SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection G (⟨j, hj⟩ : t))
        change (π.val.app (.op V)) (q.val (.op V)) =
          I.toModules.presheaf.map V.hom.op (m ⟨j, hj⟩) at hq
        change I.toModulesι.app V.left ((π.val.app (.op V)) (q.val (.op V))) = _
        rw [hq]
        exact (PresheafOfModules.naturality_apply I.toModulesι.val V.hom.op _).trans
          (congrArg (X.presheaf.map V.hom.op) (hm ⟨j, hj⟩))
      intro x
      have hx : I.toModulesι.app V.left x ∈ I.ideal V' :=
        (I.range_toModulesι_app V').subset ⟨x, rfl⟩
      obtain ⟨z, hz⟩ := hle hx
      exact ⟨z, I.injective_toModulesι_app V.left hz⟩
    have hloc : Sheaf.IsLocallySurjective
        ((SheafOfModules.toSheaf (X.ringCatSheaf.over U.1)).map π) := by
      constructor
      intro W x
      rw [GrothendieckTopology.mem_over_iff]
      intro p hp
      obtain ⟨_, ⟨V, hV, rfl⟩, hpV, hVW⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open hp W.left.isOpen
      let V' : Over U.1 := Over.mk (homOfLE (hVW.trans (leOfHom W.hom)))
      let f : V' ⟶ W := Over.homMk (homOfLE hVW)
      refine ⟨V, homOfLE hVW, ?_, hpV⟩
      rw [Sieve.overEquiv_iff]
      exact hsurj V' hV _
    have : Epi π := (SheafOfModules.toSheaf (X.ringCatSheaf.over U.1)).epi_of_epi_map
      (Sheaf.epi_of_isLocallySurjective _)
    exact ⟨⟨t, G, inferInstance⟩, ⟨inferInstanceAs (Finite t)⟩⟩
  choose σ hσ using hgen
  let q : I.toModules.LocalGeneratorsData :=
    { I := X.affineOpens
      X := fun U ↦ U.1
      coversTop := (Opens.coversTop_iff _ _).mpr (iSup_affineOpens_eq_top X)
      generators := σ }
  exact { exists_localGeneratorsData := ⟨q, { isFiniteType := hσ }⟩ }

end AlgebraicGeometry.Scheme.IdealSheafData
