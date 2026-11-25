/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Subobject
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTorsion
public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

import Mathlib.Order.Shrink
import WeilConjectures.Mathlib.CategoryTheory.Abelian.Subobject
import WeilConjectures.AlgebraicGeometry.Curve.FiniteStalkSubobjectsCover

@[expose] public section
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme
private theorem finite_fiber_sup
    {C : Type*} [Category C] [Abelian C]
    (Φ : C ⥤ AddCommGrpCat.{u + 1}) [Φ.Additive]
    [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
    {M : C} (S T : Subobject M)
    (hS : Finite (Φ.obj (S : C))) (hT : Finite (Φ.obj (T : C))) :
    Finite (Φ.obj ((S ⊔ T : Subobject M) : C)) := by
  have : Epi (Subobject.supDesc S T) := Subobject.epi_supDesc S T
  have : PreservesBinaryBiproducts Φ :=
    preservesBinaryBiproducts_of_preservesBinaryProducts Φ
  let e := Φ.mapBiprod (S : C) (T : C) ≪≫
    AddCommGrpCat.biprodIsoProd (Φ.obj (S : C)) (Φ.obj (T : C))
  have : Finite (Φ.obj ((S : C) ⊞ (T : C))) :=
    Finite.of_injective e.hom (ConcreteCategory.bijective_of_isIso e.hom).1
  exact Finite.of_surjective (Φ.map (Subobject.supDesc S T))
    ((AddCommGrpCat.epi_iff_surjective _).mp inferInstance)

private theorem torsion_of_mono
    {X : Scheme.{u}} {N M : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (f : N ⟶ M) [Mono f] (hM : M.IsTorsion) : N.IsTorsion := by
  intro U s
  obtain ⟨R, hR, hs⟩ := hM (f.hom.app U s)
  refine ⟨R, hR, ?_⟩
  intro V g hg
  obtain ⟨n, hn, he⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp (hs hg)
  refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n, hn, ?_⟩
  have hinj : Function.Injective (f.hom.app (Opposite.op V)) := by
    rw [← AddCommGrpCat.mono_iff_injective]
    exact ((sheafToPresheaf X.smallEtaleTopology _ ⋙
      (CategoryTheory.evaluation _ _).obj (Opposite.op V)).map_mono f :)
  apply hinj
  rw [map_nsmul, map_zero]
  have hw := ConcreteCategory.congr_hom (f.hom.naturality g.op) s
  change f.hom.app (Opposite.op V) (N.obj.map g.op s) =
    M.obj.map g.op (f.hom.app U s) at hw
  rw [hw]
  exact he

/-- Finite-stalk torsion approximation of a torsion generic sheaf.
Source: blueprint `theorem-cohomology-curves--2`, finite stable subgroup construction.
(blueprint: lem-sc-generic-torsion-finite-stalk-colimit-finite)
The finite stable subgroups of the corresponding discrete continuous Galois module form a
filtered poset and transport through the sheaf/module equivalence to the asserted cocone.
-/
theorem exists_generic_torsion_finite_stalk_colimit
    (X : Scheme.{u}) [IsIntegral X] [CompactSpace X] [QuasiSeparatedSpace X]
    (M : Sheaf (Spec X.functionField).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hM : M.IsTorsion) :
    ∃ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsFiltered I)
      (F : I ⥤ Sheaf (Spec X.functionField).smallEtaleTopology AddCommGrpCat.{u + 1})
      (ι : F ⟶ (Functor.const I).obj M),
      (∀ i, (F.obj i).IsTorsion) ∧
      (∀ i, Finite (((pointSmallEtale
        (Spec.map (CommRingCat.ofHom
          (algebraMap X.functionField (AlgebraicClosure X.functionField))))).sheafFiber
            (A := AddCommGrpCat.{u + 1})).obj (F.obj i))) ∧
      Nonempty (IsColimit (Cocone.mk M ι)) := by
  classical
  let C := Sheaf (Spec X.functionField).smallEtaleTopology AddCommGrpCat.{u + 1}
  have : HasColimitsOfSize.{u + 1, u + 1} C := IsGrothendieckAbelian.hasColimits C
  let : CompleteLattice (Subobject M) := Subobject.instCompleteLattice.{u + 1}
  let Φ := (pointSmallEtale
    (Spec.map (CommRingCat.ofHom
      (algebraMap X.functionField (AlgebraicClosure X.functionField))))).sheafFiber
        (A := AddCommGrpCat.{u + 1})
  have : AB5OfSize.{u, u} AddCommGrpCat.{u + 1} :=
    AB5OfSize_shrink.{u, u, u + 1, u + 1} _
  have : Φ.Additive := Functor.additive_of_preserves_binary_products Φ
  let B := {N : Subobject M // Finite (Φ.obj (N : C))}
  have hbot : Finite (Φ.obj ((⊥ : Subobject M) : C)) := by
    have hz : IsZero ((⊥ : Subobject M) : C) :=
      (isZero_zero C).of_iso Subobject.botCoeIsoZero
    have : Subsingleton (Φ.obj ((⊥ : Subobject M) : C)) :=
      AddCommGrpCat.subsingleton_of_isZero (Φ.map_isZero hz)
    infer_instance
  have : Nonempty B := ⟨⟨⊥, hbot⟩⟩
  have : IsDirectedOrder B := ⟨fun a b ↦
    ⟨⟨a.val ⊔ b.val, finite_fiber_sup Φ a.val b.val a.property b.property⟩,
      (show a.val ≤ a.val ⊔ b.val from le_sup_left),
      (show b.val ≤ a.val ⊔ b.val from le_sup_right)⟩⟩
  have : IsFiltered B := inferInstance
  let I := Shrink.{u + 1} B
  let : SmallCategory I := inferInstanceAs (SmallCategory (Shrink.{u + 1} B))
  let e : B ≌ I := (orderIsoShrink.{u + 1} B).equivalence
  have : IsFiltered I := IsFiltered.of_equivalence e
  let j : B ⥤ Subobject M :=
    (show Monotone (fun b : B ↦ b.val) from fun _ _ h ↦ h).functor
  let D : I ⥤ MonoOver M := e.inverse ⋙ j ⋙ Subobject.representative
  let F : I ⥤ C := D ⋙ MonoOver.forget M ⋙ Over.forget M
  let c : Cocone (D ⋙ MonoOver.forget M) :=
    { pt := Over.mk (𝟙 M)
      ι :=
        { app := fun i ↦ Over.homMk (D.obj i).obj.hom (by simp)
          naturality := by
            intro i k f
            ext
            simp } }
  have hcover : (⨆ b : B, b.val) = ⊤ :=
    torsion_finite_stalk_subobjects_iSup_eq_top X.functionField M hM
  have : Mono c.pt.hom := inferInstanceAs (Mono (𝟙 M))
  have htop : Subobject.mk c.pt.hom = ⊤ := (Subobject.top_eq_id M).symm
  have hsup : Subobject.mk c.pt.hom = ⨆ i, Subobject.mk (D.obj i).obj.hom := by
    apply le_antisymm
    · rw [htop, ← hcover]
      refine iSup_le fun b ↦ ?_
      have hb : e.inverse.obj (e.functor.obj b) = b :=
        (orderIsoShrink.{u + 1} B).symm_apply_apply b
      have h := le_iSup (fun i ↦ Subobject.mk (D.obj i).obj.hom) (e.functor.obj b)
      change Subobject.mk ((e.inverse.obj (e.functor.obj b)).val.arrow) ≤ _ at h
      simpa only [Subobject.mk_arrow, hb] using h
    · rw [htop]
      exact le_top
  let hc := IsGrothendieckAbelian.isColimitMapCoconeOfSubobjectMkEqISup D c hsup
  refine ⟨I, inferInstance, inferInstance, F, ((Over.forget M).mapCocone c).ι, ?_, ?_, ?_⟩
  · intro i
    exact torsion_of_mono (D.obj i).obj.hom hM
  · intro i
    exact (e.inverse.obj i).property
  · exact ⟨hc⟩
end AlgebraicGeometry.Scheme
