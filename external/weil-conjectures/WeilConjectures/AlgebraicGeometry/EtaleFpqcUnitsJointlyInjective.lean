/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageStalkGerm
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Joint injectivity of fpqc inverse-image units on étale objects

Source: Stacks Project, Tags 09XM and 09XN, agreement-open uniqueness.
(blueprint: lem-weil-pbc-etale-fpqc-units-jointly-injective). -/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Source: Stacks Project, Tag 03Q1 (3), inverse-image stalk comparison;
Tag 03PU, sections determined by geometric germs; Tag 09XN, fpqc uniqueness.
(blueprint: lem-weil-pbc-etale-fpqc-units-jointly-injective).

Proof:
1. Base change the fpqc covering to V. For every point v of V choose a point y
   above it on some T_i ×_S V, using joint surjectivity. Take the algebraic closure
   of the residue field of y and its canonical geometric lift to T_i ×_S V.
2. Its projection to T_i and its projection to V define a pointed étale
   neighbourhood of the image point of S. The inverse-image stalk comparison,
   including its adjunction-unit formula, sends the two equal pulled-back germs
   to the original germs of t and t'. Thus these original germs agree.
3. Equality in the filtered colimit of pointed étale neighbourhoods is witnessed
   on a common refinement W → V. This gives equal restrictions on W and a point
   of W mapping to v. These W cover V as v varies.
4. Sheaf separatedness on this covering gives t = t'. If V is empty the family
   is empty and separatedness for the empty cover applies. No overlap datum or
   existence of matching representatives is assumed. -/
theorem etaleFpqcUnits_jointly_injective
    {S : Scheme.{u}} {I : Type v} (T : I → Scheme.{u}) (g : ∀ i, T i ⟶ S)
    (hcover : Presieve.ofArrows T g ∈ Scheme.fpqcPrecoverage S)
    (F : Sheaf S.smallEtaleTopology (Type (u + 1)))
    (V : S.Etale) (t t' : F.obj.obj (op V))
    (heq : ∀ i,
      let β := MorphismProperty.Over.pullback @Etale ⊤ (g i)
      let η := (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        β (Type (u + 1)) (S.smallGrothendieckTopology @Etale)
        ((T i).smallGrothendieckTopology @Etale)).unit.app F
      η.hom.app (op V) t = η.hom.app (op V) t') : t = t' := by
  classical
  have local_agree (v : V.left) : ∃ (W : S.Etale) (m : W ⟶ V) (w : W.left),
      m.left w = v ∧ F.obj.map m.op t = F.obj.map m.op t' := by
    have hcover' : Presieve.ofArrows (fun i ↦ pullback (g i) V.hom)
        (fun i ↦ pullback.snd (g i) V.hom) ∈ Scheme.fpqcPrecoverage V.left := by
      rw [Presieve.ofArrows_pullback]
      exact Precoverage.pullbackArrows_mem V.hom hcover
    obtain ⟨Y, f, hf, y, hy⟩ := Scheme.JointlySurjective.exists_eq
      (Presieve.ofArrows (fun i ↦ pullback (g i) V.hom)
        (fun i ↦ pullback.snd (g i) V.hom))
      (Scheme.propQCPrecoverage_le_precoverage V.left hcover') v
    obtain ⟨i⟩ := hf
    let Ω := AlgebraicClosure ((pullback (g i) V.hom).residueField y)
    let r : Spec (.of Ω) ⟶ pullback (g i) V.hom :=
      (Scheme.SpecToEquivOfField Ω _).symm
        ⟨y, CommRingCat.ofHom (algebraMap ((pullback (g i) V.hom).residueField y) Ω)⟩
    let e := r ≫ pullback.fst (g i) V.hom
    let q := e ≫ g i
    let z : (Scheme.pointSmallEtale q).fiber.obj V :=
      Over.homMk (r ≫ pullback.snd (g i) V.hom) (by
        change (r ≫ pullback.snd (g i) V.hom) ≫ V.hom = q
        dsimp only [q, e]
        rw [Category.assoc, Category.assoc, pullback.condition])
    obtain ⟨c, _, hg, _⟩ := etaleSetInverseImageStalkGerm S (T i) (g i) F Ω e
    have h := heq i
    dsimp only at h
    have hgerm : (Scheme.pointSmallEtale q).toPresheafFiber V z F.obj t =
        (Scheme.pointSmallEtale q).toPresheafFiber V z F.obj t' := by
      rw [← hg V z t, ← hg V z t', h]
    obtain ⟨W, m, w, hw, hm⟩ :=
      ((Scheme.pointSmallEtale q).toPresheafFiber_eq_iff'
        (A := Type (u + 1)) (P := F.obj) V z t t').1 hgerm
    refine ⟨W, m, w.left (default : Spec (.of Ω)), ?_, hm⟩
    have hv := congrArg (fun a ↦ a.left (default : Spec (.of Ω))) hw
    have hr : r (default : Spec (.of Ω)) = y := by
      simp [r]
    have hz : (r ≫ pullback.snd (g i) V.hom) (default : Spec (.of Ω)) = v := by
      rw [Scheme.Hom.comp_apply, hr]
      exact hy
    change m.left (w.left (default : Spec (.of Ω))) =
      (r ≫ pullback.snd (g i) V.hom) (default : Spec (.of Ω)) at hv
    exact hv.trans hz
  choose W m w hw hm using local_agree
  have hW : Sieve.ofArrows W m ∈ S.smallEtaleTopology V := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    ext v
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨v, w v, hw v⟩
  have H : (↾(fun _ : PUnit.{u + 2} ↦ t)) = (↾(fun _ : PUnit.{u + 2} ↦ t')) := by
    apply F.property.hom_ext_ofArrows m hW
    intro v
    ext a
    exact hm v
  exact ConcreteCategory.congr_hom H PUnit.unit

end AlgebraicGeometry
