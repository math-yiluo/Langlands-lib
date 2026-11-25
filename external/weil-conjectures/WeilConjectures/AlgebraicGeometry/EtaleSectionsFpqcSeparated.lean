/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageRestriction
import WeilConjectures.AlgebraicGeometry.EtaleSectionsEqualOpen

/-! # EtaleSectionsFpqcSeparated

Source: Stacks Project, Tag 09XN
(blueprint: lem-weil-pbc-etale-sections-fpqc-separated). -/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private noncomputable def sectionPullback {S T : Scheme.{u}}
    (F : Sheaf S.smallEtaleTopology (Type (u + 1))) (V : S.Etale)
    (a : T ⟶ V.left) (e : T ⟶ S) (he : a ≫ V.hom = e)
    (s : F.obj.obj (op V)) :
    ((Scheme.etaleSetPullback e).obj F).obj.obj (op (Scheme.Etale.mk (𝟙 T))) :=
  ((Scheme.etaleSetPullback e).obj F).obj.map
    (MorphismProperty.Over.homMk
      (A := Scheme.Etale.mk (𝟙 T))
      (B := (MorphismProperty.Over.pullback @Etale ⊤ e).obj V)
      (pullback.lift a (𝟙 T) (he.trans (Category.id_comp e).symm))
      (by simp)).op
    (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ e) (Type (u + 1))
      (S.smallGrothendieckTopology @Etale)
      (T.smallGrothendieckTopology @Etale)).unit.app F).hom.app (op V) s)

private theorem sectionPullback_eq_iff {S T : Scheme.{u}}
    (F : Sheaf S.smallEtaleTopology (Type (u + 1))) (V : S.Etale)
    (a : T ⟶ V.left) (e : T ⟶ S) (he : a ≫ V.hom = e)
    (s t : F.obj.obj (op V)) :
    sectionPullback F V a (a ≫ V.hom) rfl s =
        sectionPullback F V a (a ≫ V.hom) rfl t ↔
      sectionPullback F V a e he s = sectionPullback F V a e he t := by
  subst e
  rfl

/-- Source: Stacks Project, Tag 09XN, uniqueness, and Tag 03S2, identity restriction.
(blueprint: lem-weil-pbc-etale-sections-fpqc-separated).

Proof:
Apply the largest agreement open theorem to the identity etale object and the
two global sections. Equality of their pullbacks factors every g_i through the
agreement open. An fpqc covering is jointly surjective, so every point of S lies in
this open, which is therefore all of S. Test its universal property on the identity
of S. Inverse image along the identity is canonically restriction along the identity;
the unit followed by restriction along the diagonal is the identity section map.
Thus equality after this identity pullback gives equality of the original sections.
This also handles an empty base or an empty indexing type whenever it is a cover. -/
theorem etaleSections_eq_of_fpqc_pullbacks
    {S : Scheme.{u}} {I : Type v} (T : I → Scheme.{u}) (g : ∀ i, T i ⟶ S)
    (hcover : Presieve.ofArrows T g ∈ Scheme.fpqcPrecoverage S)
    (F : Sheaf S.smallEtaleTopology (Type (u + 1)))
    (t t' : F.obj.obj (op (Scheme.Etale.mk (𝟙 S))))
    (heq : ∀ i,
      ((Scheme.etaleSetPullback (g i)).obj F).obj.map
        (MorphismProperty.Over.homMk (pullback.lift (g i) (𝟙 (T i))
          ((Category.comp_id _).trans (Category.id_comp _).symm)) (by simp) :
          Scheme.Etale.mk (𝟙 (T i)) ⟶
            (MorphismProperty.Over.pullback @Etale ⊤ (g i)).obj (Scheme.Etale.mk (𝟙 S))).op
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (MorphismProperty.Over.pullback @Etale ⊤ (g i)) _
          (S.smallGrothendieckTopology @Etale)
          ((T i).smallGrothendieckTopology @Etale)).unit.app F).hom.app
            (op (Scheme.Etale.mk (𝟙 S))) t) =
      ((Scheme.etaleSetPullback (g i)).obj F).obj.map
        (MorphismProperty.Over.homMk (pullback.lift (g i) (𝟙 (T i))
          ((Category.comp_id _).trans (Category.id_comp _).symm)) (by simp) :
          Scheme.Etale.mk (𝟙 (T i)) ⟶
            (MorphismProperty.Over.pullback @Etale ⊤ (g i)).obj (Scheme.Etale.mk (𝟙 S))).op
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (MorphismProperty.Over.pullback @Etale ⊤ (g i)) _
          (S.smallGrothendieckTopology @Etale)
          ((T i).smallGrothendieckTopology @Etale)).unit.app F).hom.app
            (op (Scheme.Etale.mk (𝟙 S))) t')) : t = t'  := by
  obtain ⟨W, hW, _⟩ :=
    existsUnique_etaleSections_equal_open S F (Scheme.Etale.mk (𝟙 S)) t t'
  have hg (i : I) : ∃ b : T i ⟶ W.toScheme, b ≫ W.ι = g i := by
    apply (hW (T i) (g i)).mpr
    exact (sectionPullback_eq_iff F (Scheme.Etale.mk (𝟙 S)) (g i) (g i)
      (Category.comp_id _) t t').mpr (heq i)
  have hall (x : S) : x ∈ W := by
    obtain ⟨Y, f, hf, y, hy⟩ :=
      Scheme.JointlySurjective.exists_eq (Presieve.ofArrows T g)
        (Scheme.propQCPrecoverage_le_precoverage S hcover) x
    obtain ⟨i⟩ := hf
    obtain ⟨b, hb⟩ := hg i
    have hpoint := congrArg (fun f : T i ⟶ S ↦ f y) hb
    rw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply] at hpoint
    rw [← hy, ← hpoint]
    exact (b y).property
  have hid := (hW S (𝟙 S)).mp
    ⟨IsOpenImmersion.lift W.ι (𝟙 S) (by
        rw [Scheme.Opens.range_ι]
        exact fun x _ ↦ hall x), IsOpenImmersion.lift_fac _ _ _⟩
  have hid' := (sectionPullback_eq_iff F (Scheme.Etale.mk (𝟙 S)) (𝟙 S) (𝟙 S)
    (Category.comp_id _) t t').mp hid
  obtain ⟨ρ, hρ⟩ := etaleSetInverseImageRestriction (𝟙 S)
  let V := Scheme.Etale.mk (𝟙 S)
  let B := MorphismProperty.Over.pullback @Etale ⊤ (𝟙 S)
  let M := MorphismProperty.Over.map ⊤ (inferInstance : Etale (𝟙 S))
  let δ : V ⟶ B.obj V := MorphismProperty.Over.homMk
    (pullback.lift (𝟙 S) (𝟙 S) rfl) (pullback.lift_snd _ _ _)
  let ε := (MorphismProperty.Over.mapPullbackAdj @Etale ⊤ (𝟙 S)
    inferInstance trivial).counit.app V
  let e : M.obj V ≅ V := MorphismProperty.Over.isoMk (Iso.refl S) rfl
  have hcomp : M.map δ ≫ ε = e.hom := by
    apply MorphismProperty.Over.Hom.ext
    simp [M, δ, ε, e, V]
  have hnat := (ρ.hom.app F).hom.naturality δ.op
  have hsection (s : F.obj.obj (op V)) :
      (ρ.hom.app F).hom.app (op V)
        (sectionPullback F V (𝟙 S) (𝟙 S) (Category.comp_id _) s) =
      F.obj.map e.hom.op s := by
    have hn := congrArg (fun f ↦ f
      (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        B (Type (u + 1)) (S.smallGrothendieckTopology @Etale)
        (S.smallGrothendieckTopology @Etale)).unit.app F).hom.app (op V) s)) hnat
    simp only [CategoryTheory.comp_apply] at hn
    rw [show (ρ.hom.app F).hom.app (op (B.obj V))
      (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        B (Type (u + 1)) (S.smallGrothendieckTopology @Etale)
        (S.smallGrothendieckTopology @Etale)).unit.app F).hom.app (op V) s) =
        F.obj.map ε.op s from hρ F V s] at hn
    change _ = F.obj.map (M.map δ).op (F.obj.map ε.op s) at hn
    have hh : F.obj.map ε.op ≫ F.obj.map (M.map δ).op = F.obj.map e.hom.op :=
      (F.obj.map_comp _ _).symm.trans
        (congrArg (fun f : M.obj V ⟶ V ↦ F.obj.map f.op) hcomp)
    exact hn.trans (ConcreteCategory.congr_hom hh s)
  apply (CategoryTheory.injective_of_mono (F.obj.map e.hom.op))
  rw [← hsection t, ← hsection t']
  exact congrArg ((ρ.hom.app F).hom.app (op V)) hid'

end AlgebraicGeometry
