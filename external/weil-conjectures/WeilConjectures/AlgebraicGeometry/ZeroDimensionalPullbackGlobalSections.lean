/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
import WeilConjectures.AlgebraicGeometry.ZeroDimensionalBaseChangeGeometricPoints
import WeilConjectures.AlgebraicGeometry.GlobalSectionsStalkComparison
import WeilConjectures.AlgebraicGeometry.ZeroDimensionalSectionsStalks

/-!
# Global sections under field extension in dimension zero

Source: the degree-zero argument of blueprint lemma-sheaves-finite-support-finite-morphisms--2.
(blueprint: lem-weil-pbc-zero-dimensional-pullback-global-sections).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Pullback on global sections of an abelian etale sheaf is bijective for a
 zero-dimensional finite-type scheme over an algebraically closed field.
 Source: blueprint lemma-sheaves-finite-support-finite-morphisms--2, proof steps 1 and 4;
 Stacks Project, Tags 03Q1 and 0GJA.
 (blueprint: lemma-sheaves-finite-support-finite-morphisms--2).

 Proof: The source has finitely many closed points with residue field k, and after
 extending k to k' the projection gives a bijection of these point sets, by
 lemma-sheaves-finite-support-finite-morphisms--2. Choose an algebraically closed
 geometric point above each point of the base change and compose it with the projection.
 The germ maps identify global sections on both schemes with products of these stalks,
 by lemma-sheaves-finite-support-finite-morphisms--2. Inverse image identifies each target
 stalk with the corresponding source stalk, compatibly with germs of sections, by
 lemma-sheaves-finite-support-finite-morphisms--2. Consequently the global sections pullback is,
 under these product identifications, the product of the stalk isomorphisms reindexed
 along the point bijection. It is therefore bijective. The empty scheme gives empty
 products and is covered by the same argument. Neither torsion nor reducedness is used. -/
theorem bijective_globalSectionsUpperStarMap_of_dim_zero {k k' : Type u}
    [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k'] {C C' : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsCurve f] (hC : topologicalKrullDim C ≤ 0)
    {ι : Spec (.of k') ⟶ Spec (.of k)} {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C}
    (h : IsPullback ι' f' f ι) (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Function.Bijective (globalSectionsUpperStarMap AddCommGrpCat.{u + 1} ι' F) := by
  classical
  obtain ⟨hf', hC', b, hb, t, ht⟩ := zeroDimensional_baseChange_geometric_points f hC h
  let : IsCurve f' := hf'
  let : C.Over (Spec (.of k)) := ⟨f⟩
  let : C'.Over (Spec (.of k')) := ⟨f'⟩
  have : IsSeparated (C ↘ Spec (.of k)) := (inferInstance : IsSeparated f)
  have : LocallyOfFiniteType (C ↘ Spec (.of k)) := (inferInstance : LocallyOfFiniteType f)
  have : QuasiCompact (C ↘ Spec (.of k)) := (inferInstance : QuasiCompact f)
  have : IsSeparated (C' ↘ Spec (.of k')) := (inferInstance : IsSeparated f')
  have : LocallyOfFiniteType (C' ↘ Spec (.of k')) :=
    (inferInstance : LocallyOfFiniteType f')
  have : QuasiCompact (C' ↘ Spec (.of k')) := (inferInstance : QuasiCompact f')
  let s : C → (Spec (.of k') ⟶ C) := fun c ↦ t (b.symm c) ≫ ι'
  have hs : ∀ c, s c default = c := by
    intro c
    change ι' (t (b.symm c) default) = c
    rw [ht, ← hb, b.apply_symm_apply]
  let G := ((ι')^*[AddCommGrpCat.{u + 1}]).obj F
  let a := (Sheaf.ΓNatIsoSheafSections _ AddCommGrpCat.{u + 1}
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale C)).hom.app F
  let a' := (Sheaf.ΓNatIsoSheafSections _ AddCommGrpCat.{u + 1}
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale C')).hom.app G
  let q : F.obj.obj (Opposite.op (Scheme.Etale.mk (𝟙 C))) ⟶
      ∏ᶜ (fun c : C ↦ (Scheme.pointSmallEtale (s c)).sheafFiber.obj F) :=
    Limits.Pi.lift (fun c : C ↦
    (Scheme.pointSmallEtale (s c)).toPresheafFiber (Scheme.Etale.mk (𝟙 C))
      (Over.homMk (s c) (Category.comp_id (s c))) F.obj)
  let q' : G.obj.obj (Opposite.op (Scheme.Etale.mk (𝟙 C'))) ⟶
      ∏ᶜ (fun c' : C' ↦ (Scheme.pointSmallEtale (t c')).sheafFiber.obj G) :=
    Limits.Pi.lift (fun c' : C' ↦
    (Scheme.pointSmallEtale (t c')).toPresheafFiber (Scheme.Etale.mk (𝟙 C'))
      (Over.homMk (t c') (Category.comp_id (t c'))) G.obj)
  have hq : IsIso q :=
    (Scheme.zeroDimensional_sections_stalks k C hC (fun _ ↦ k') s hs).2.1 F
  have hq' : IsIso q' :=
    (Scheme.zeroDimensional_sections_stalks k' C' hC' (fun _ ↦ k') t ht).2.1 G
  have hd (c' : C') :
      ∃ d : (Scheme.pointSmallEtale (t c')).sheafFiber.obj G ≅
          (Scheme.pointSmallEtale (s (b c'))).sheafFiber.obj F,
        globalSectionsUpperStarMap AddCommGrpCat.{u + 1} ι' F ≫ a' ≫
          (Scheme.pointSmallEtale (t c')).toPresheafFiber (Scheme.Etale.mk (𝟙 C'))
            (Over.homMk (t c') (Category.comp_id (t c'))) G.obj ≫ d.hom =
        a ≫ (Scheme.pointSmallEtale (s (b c'))).toPresheafFiber (Scheme.Etale.mk (𝟙 C))
          (Over.homMk (s (b c')) (Category.comp_id (s (b c')))) F.obj := by
    have hsbc : s (b c') = t c' ≫ ι' := by simp only [s, b.symm_apply_apply]
    rw [hsbc]
    exact exists_globalSections_stalk_comparison ι' (t c') F
  let d := fun c' ↦ Classical.choose (hd c')
  let r := Limits.Pi.reindex b (fun c : C ↦ (Scheme.pointSmallEtale (s c)).sheafFiber.obj F)
  let e := Limits.Pi.mapIso
    (g := (fun c : C ↦ (Scheme.pointSmallEtale (s c)).sheafFiber.obj F) ∘ b) d
  have he : globalSectionsUpperStarMap AddCommGrpCat.{u + 1} ι' F ≫
      a' ≫ q' ≫ e.hom = a ≫ q ≫ r.inv := by
    apply Limits.Pi.hom_ext (f := (fun c : C ↦ (Scheme.pointSmallEtale (s c)).sheafFiber.obj F) ∘ b)
    intro c'
    simp only [q, q', r, e, Category.assoc]
    rw [Limits.Pi.mapIso_hom_π (g := (fun c : C ↦
      (Scheme.pointSmallEtale (s c)).sheafFiber.obj F) ∘ b) d c']
    simp only [Limits.Pi.lift_comp_π_assoc]
    rw [Limits.Pi.reindex_inv_π b (fun c : C ↦ (Scheme.pointSmallEtale (s c)).sheafFiber.obj F) c']
    simp only [Limits.Pi.lift_comp_π]
    exact Classical.choose_spec (hd c')
  have ha : IsIso a := by dsimp [a]; infer_instance
  have ha' : IsIso a' := by dsimp [a']; infer_instance
  have hg : IsIso (globalSectionsUpperStarMap AddCommGrpCat.{u + 1} ι' F) := by
    have : IsIso (globalSectionsUpperStarMap AddCommGrpCat.{u + 1} ι' F ≫
        a' ≫ q' ≫ e.hom) := by rw [he]; infer_instance
    exact IsIso.of_isIso_comp_right _ (a' ≫ q' ≫ e.hom)
  exact (ConcreteCategory.isIso_iff_bijective _).1 hg

end AlgebraicGeometry.Etale
