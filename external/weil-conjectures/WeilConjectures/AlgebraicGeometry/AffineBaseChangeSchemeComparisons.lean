/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineBaseChangeRingDiagram
public import WeilConjectures.AlgebraicGeometry.Picard.TwistedDescent
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Filtered.Connected

/-! # Scheme identifications for the affine base-change diagram

Source: Stacks Project, Tags 01JO and 09RE.
(blueprint: lem-pc-affine-base-change-scheme-comparisons). -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Identify the explicitly constructed pushout diagram with geometric base change,
including its colimit and its transition arrows. This is entirely a statement
about rings and schemes; it contains no complexes or derived categories.

Source: Stacks Project, Tag 01JO (affine fibre products), and Tag 09RE,
affine calculation (blueprint: lem-pc-affine-base-change-scheme-comparisons).

Proof: Put B = Gamma(Y) and a = Spec.preimage(t.hom followed by s).
At j the definition of F is the pushout of R(i) to R(j) and a. Apply
isPullback_SpecMap_pushout, then transport its B vertex along t. The
universal-property isomorphism gives σ(j); its first projection is the
map from B obtained by composing r with the initial-to-j arrow of F.
The upper tail is nonempty and final in the directed preorder. Restrict
hc to that tail. Pushing out in the under category preserves the colimit,
since Under.pushout is left adjoint, and Under.forget creates connected
nonempty colimits. Hence C.pt is the pushout of a along c.ι(i). Applying
Spec and transporting along t gives τ with the displayed first projection.
For each transition, both sides of the claimed equality have the same
first and second pullback projections: these are the naturality equations
of the pushout system, and at the limit the cocone equations. Pullback
hom-ext proves both arrow compatibilities. All arguments are universal
properties, so zero rings and empty spectra require no exception. -/
theorem exists_affineBaseChangeSchemeComparisons
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (Y : Scheme.{u}) (s : Y ⟶ Spec (R.obj i))
    (t : Spec (Scheme.Γ.obj (.op Y)) ≅ Y) :
    let F := affineBaseChangeRingDiagram R i Y s t
    let C := colimit.cocone F
    let r := affineBaseChangeInitialMap R i Y s t
    ∃ (σ : ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i),
      Spec (F.obj j.val) ≅ pullback s (Spec.map (R.map (homOfLE j.val.property))))
    (τ : Spec C.pt ≅ pullback s (Spec.map (c.ι.app i))),
      (∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i),
        (σ j).hom ≫ pullback.fst s (Spec.map (R.map (homOfLE j.val.property))) =
          Spec.map (CommRingCat.ofHom r ≫ F.map (homOfLE j.property)) ≫ t.hom) ∧
      (τ.hom ≫ pullback.fst s (Spec.map (c.ι.app i)) =
        Spec.map (CommRingCat.ofHom r ≫ C.ι.app ⟨i, le_rfl⟩) ≫ t.hom) ∧
      (∀ (j k : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i)) (hjk : j ≤ k),
        (σ k).hom ≫ baseChangeMap s
          (T := Over.mk (Spec.map (R.map (homOfLE j.val.property))))
          (T' := Over.mk (Spec.map (R.map (homOfLE k.val.property))))
          (Over.homMk (Spec.map (R.map (homOfLE hjk)))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)) =
          Spec.map (F.map (homOfLE hjk)) ≫ (σ j).hom) ∧
      (∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i),
        τ.hom ≫ baseChangeMap s
          (T := Over.mk (Spec.map (R.map (homOfLE j.val.property))))
          (T' := Over.mk (Spec.map (c.ι.app i)))
          (Over.homMk (Spec.map (c.ι.app j.val))
            (by dsimp; rw [← Spec.map_comp, c.w (homOfLE j.val.property)])) =
          Spec.map (C.ι.app j.val) ≫ (σ j).hom)  := by
  classical
  dsimp only
  unfold affineBaseChangeRingDiagram affineBaseChangeInitialMap
  have : Nonempty I := ⟨i⟩
  have : IsFiltered I := inferInstance
  have : Nonempty (Set.Ici i) := ⟨⟨i, le_rfl⟩⟩
  have : IsDirected (Set.Ici i) (· ≤ ·) := ⟨by
    intro j k
    obtain ⟨l, hjl, hkl⟩ := exists_ge_ge j.val k.val
    exact ⟨⟨l, j.property.trans hjl⟩, hjl, hkl⟩⟩
  have : IsFiltered (Set.Ici i) := inferInstance
  have : (affineBaseChangeTail i).Faithful := ⟨by
    intro X Y f g h
    subsingleton⟩
  have : (affineBaseChangeTail i).Full := ⟨by
    intro j k f
    exact ⟨homOfLE (leOfHom f.right), rfl⟩⟩
  have : (affineBaseChangeTail i).EssSurj := ⟨by
    intro j
    refine ⟨⟨j.right, leOfHom j.hom⟩, ⟨?_⟩⟩
    exact Under.isoMk (Iso.refl _)⟩
  have : (affineBaseChangeTail i).IsEquivalence := {}
  let B := Scheme.Γ.obj (.op Y)
  let a : R.obj i ⟶ B := Spec.preimage (t.hom ≫ s)
  let G := Under.pushout a ⋙ Under.forget B
  let p := (c.underPost i).whisker (affineBaseChangeTail i)
  have hp : IsColimit p :=
    (Functor.Final.isColimitWhiskerEquiv (affineBaseChangeTail i) _).symm
      (hc.underPost i)
  have : IsConnected (Set.Ici i) := IsFiltered.isConnected (Set.Ici i)
  have : (Under.pushout a).IsLeftAdjoint := inferInstance
  have : PreservesColimitsOfShape (Set.Ici i) (Under.pushout a) := inferInstance
  have : PreservesColimitsOfShape (Set.Ici i) (Under.forget B) := inferInstance
  have : PreservesColimitsOfShape (Set.Ici i) G := by
    dsimp only [G]
    infer_instance
  let q := G.mapCocone p
  have hq : IsColimit q := isColimitOfPreserves G hp
  let F := affineBaseChangeTail i ⋙ Under.post R ⋙ Under.pushout a ⋙ Under.forget B
  have hq' : IsColimit (show Cocone F from q) := hq
  let η := (colimit.isColimit F).coconePointUniqueUpToIso hq'
  have hg (A : CommRingCat.{u}) (b : R.obj i ⟶ A) :
      IsPullback (Spec.map (pushout.inr b a) ≫ t.hom)
        (Spec.map (pushout.inl b a)) s (Spec.map b) := by
    apply (isPullback_SpecMap_pushout b a).flip.of_iso
      (Iso.refl _) t (Iso.refl _) (Iso.refl _)
    · simp
    · simp
    · simp [a]
    · simp
  let σ : ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i),
      Spec (F.obj j.val) ≅ pullback s (Spec.map (R.map (homOfLE j.val.property))) := by
    intro j
    dsimp only [F, Functor.comp_obj, affineBaseChangeTail, Under.post_obj,
      Under.pushout_obj, Under.forget_obj, Under.mk_right, Under.mk_hom]
    exact (hg _ (R.map (homOfLE j.val.property))).isoPullback
  let τ : Spec (colimit F) ≅ pullback s (Spec.map (c.ι.app i)) :=
    Scheme.Spec.mapIso η.symm.op ≪≫ (hg _ (c.ι.app i)).isoPullback
  refine ⟨σ, τ, ?_, ?_, ?_, ?_⟩
  · intro j
    change (hg _ (R.map (homOfLE j.val.property))).isoPullback.hom ≫ _ = _
    rw [IsPullback.isoPullback_hom_fst]
    congr 2
    change pushout.inr (R.map (homOfLE j.val.property)) a =
      pushout.inr (R.map (homOfLE (le_rfl : i ≤ i))) a ≫
        pushout.desc (R.map (homOfLE j.val.property) ≫
          pushout.inl (R.map (homOfLE j.val.property)) a)
          (pushout.inr (R.map (homOfLE j.val.property)) a) _
    exact (pushout.inr_desc _ _ _).symm
  · change (Spec.map η.inv ≫ (hg _ (c.ι.app i)).isoPullback.hom) ≫ _ = _
    rw [Category.assoc, IsPullback.isoPullback_hom_fst, ← Category.assoc,
      ← Spec.map_comp]
    congr 2
    have hη : q.ι.app ⟨i, le_rfl⟩ ≫ η.inv = colimit.ι F ⟨i, le_rfl⟩ := by
      exact IsColimit.comp_coconePointUniqueUpToIso_inv _ _ _
    change pushout.inr (c.ι.app i) a ≫ η.inv =
      pushout.inr (R.map (homOfLE (le_rfl : i ≤ i))) a ≫ colimit.ι F ⟨i, le_rfl⟩
    rw [← hη, ← Category.assoc]
    congr 1
    change pushout.inr (c.ι.app i) a =
      pushout.inr (R.map (homOfLE (le_rfl : i ≤ i))) a ≫
        pushout.desc (c.ι.app i ≫ pushout.inl (c.ι.app i) a)
          (pushout.inr (c.ι.app i) a) _
    exact (pushout.inr_desc _ _ _).symm
  · intro j k hjk
    apply pullback.hom_ext
    · simp only [Category.assoc, baseChangeMap_fst]
      change (hg _ (R.map (homOfLE k.val.property))).isoPullback.hom ≫
          pullback.fst s (Spec.map (R.map (homOfLE k.val.property))) =
        Spec.map (F.map (homOfLE hjk)) ≫
          (hg _ (R.map (homOfLE j.val.property))).isoPullback.hom ≫
            pullback.fst s (Spec.map (R.map (homOfLE j.val.property)))
      rw [IsPullback.isoPullback_hom_fst, IsPullback.isoPullback_hom_fst,
        ← Category.assoc, ← Spec.map_comp]
      congr 2
      change pushout.inr (R.map (homOfLE k.val.property)) a =
        pushout.inr (R.map (homOfLE j.val.property)) a ≫
          pushout.desc (R.map (homOfLE hjk) ≫
            pushout.inl (R.map (homOfLE k.val.property)) a)
            (pushout.inr (R.map (homOfLE k.val.property)) a) _
      exact (pushout.inr_desc _ _ _).symm
    · simp only [Category.assoc, baseChangeMap_snd]
      change ((hg _ (R.map (homOfLE k.val.property))).isoPullback.hom ≫
          pullback.snd s (Spec.map (R.map (homOfLE k.val.property)))) ≫
          Spec.map (R.map (homOfLE hjk)) =
        Spec.map (F.map (homOfLE hjk)) ≫
          (hg _ (R.map (homOfLE j.val.property))).isoPullback.hom ≫
            pullback.snd s (Spec.map (R.map (homOfLE j.val.property)))
      rw [IsPullback.isoPullback_hom_snd, IsPullback.isoPullback_hom_snd,
        ← Spec.map_comp, ← Spec.map_comp]
      congr 1
      change R.map (homOfLE hjk) ≫ pushout.inl (R.map (homOfLE k.val.property)) a =
        pushout.inl (R.map (homOfLE j.val.property)) a ≫
          pushout.desc (R.map (homOfLE hjk) ≫
            pushout.inl (R.map (homOfLE k.val.property)) a)
            (pushout.inr (R.map (homOfLE k.val.property)) a) _
      exact (pushout.inl_desc _ _ _).symm
  · intro j
    have hη : q.ι.app j.val ≫ η.inv = colimit.ι F j.val :=
      IsColimit.comp_coconePointUniqueUpToIso_inv _ _ _
    apply pullback.hom_ext
    · simp only [Category.assoc, baseChangeMap_fst]
      change Spec.map η.inv ≫ (hg _ (c.ι.app i)).isoPullback.hom ≫
          pullback.fst s (Spec.map (c.ι.app i)) =
        Spec.map (colimit.ι F j.val) ≫
          (hg _ (R.map (homOfLE j.val.property))).isoPullback.hom ≫
            pullback.fst s (Spec.map (R.map (homOfLE j.val.property)))
      rw [IsPullback.isoPullback_hom_fst, IsPullback.isoPullback_hom_fst,
        ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
      congr 2
      rw [← hη, ← Category.assoc]
      congr 1
      change pushout.inr (c.ι.app i) a =
        pushout.inr (R.map (homOfLE j.val.property)) a ≫
          pushout.desc (c.ι.app j.val ≫ pushout.inl (c.ι.app i) a)
            (pushout.inr (c.ι.app i) a) _
      exact (pushout.inr_desc _ _ _).symm
    · simp only [Category.assoc, baseChangeMap_snd]
      change (Spec.map η.inv ≫ (hg _ (c.ι.app i)).isoPullback.hom ≫
          pullback.snd s (Spec.map (c.ι.app i))) ≫ Spec.map (c.ι.app j.val) =
        Spec.map (colimit.ι F j.val) ≫
          (hg _ (R.map (homOfLE j.val.property))).isoPullback.hom ≫
            pullback.snd s (Spec.map (R.map (homOfLE j.val.property)))
      simp only [Category.assoc, IsPullback.isoPullback_hom_snd]
      rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
      congr 1
      rw [← hη, ← Category.assoc]
      congr 1
      change c.ι.app j.val ≫ pushout.inl (c.ι.app i) a =
        pushout.inl (R.map (homOfLE j.val.property)) a ≫
          pushout.desc (c.ι.app j.val ≫ pushout.inl (c.ι.app i) a)
            (pushout.inr (c.ι.app i) a) _
      exact (pushout.inl_desc _ _ _).symm


end AlgebraicGeometry
