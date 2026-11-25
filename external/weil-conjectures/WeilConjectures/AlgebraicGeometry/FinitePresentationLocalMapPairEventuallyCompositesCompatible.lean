/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OpenCoverTensorPullbackComparison
public import WeilConjectures.AlgebraicGeometry.LocalOverlapTransitions
public import WeilConjectures.AlgebraicGeometry.LocalMapPairCompatibility
public import WeilConjectures.AlgebraicGeometry.LocalMapPairDefect
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.FinitePresentationTestMapZeroEventually
import WeilConjectures.AlgebraicGeometry.LocalMapPairOverlapBaseChange

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

attribute [local irreducible] Scheme.Modules.tensorPullback
  Scheme.Modules.openCoverTensorPullbackComparison

private lemma pairCompatibility_of_hom
    {C : Type*} [Category C] {P : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat}
    {ι : Type*} {S : C} {X : ι → C} {f : ∀ x, X x ⟶ S}
    {D₁ D₂ : P.DescentData f} (φ : D₁ ⟶ D₂) (a b : ι) :
    Pseudofunctor.DescentData.PairCompatibility φ.hom a b := by
  constructor
  intro W t g₁ g₂ h₁ h₂
  exact φ.comm t g₁ g₂ h₁ h₂

private lemma pairDefectZero_of_pairCompatibility
    {C : Type*} [Category C] {P : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat}
    {ι : Type*} {S : C} {X : ι → C} {f : ∀ x, X x ⟶ S}
    {D₁ D₂ : P.DescentData f} {r : ∀ x, D₁.obj x ⟶ D₂.obj x} {a b : ι}
    (h : Pseudofunctor.DescentData.PairCompatibility r a b) :
    Pseudofunctor.DescentData.PairDefectZero r a b := by
  intro W t g₁ g₂ h₁ h₂
  exact ⟨_, rfl, (h.comm t g₁ g₂ h₁ h₂).symm⟩

private lemma transportedPairCompatibility_of_globalMap
    {X Y : Scheme.{u}} (U : X.OpenCover.{u}) (F G : X.Modules)
    (r₀ : ∀ x, (Scheme.Modules.pullback (U.f x)).obj F ⟶
      (Scheme.Modules.pullback (U.f x)).obj G) (a b : U.I₀) (q : Y ⟶ X)
    (δ : (Scheme.Modules.tensorPullback q).obj F ⟶
      (Scheme.Modules.tensorPullback q).obj G)
    (hr : ∀ x,
      let e := Scheme.Modules.openCoverTensorPullbackComparison q U x
      e.inv.app F ≫ (Scheme.Modules.pullback (U.pullbackHom q x)).map (r₀ x) ≫
        e.hom.app G = (Scheme.Modules.pullback ((U.pullback₁ q).f x)).map δ) :
    let V := U.pullback₁ q
    let Q := modulesPseudofunctor.toDescentData V.f
    let C := Scheme.Modules.tensorPullback q
    let r : ∀ x, (Q.obj (C.obj F)).obj x ⟶ (Q.obj (C.obj G)).obj x := fun x ↦
      let e := Scheme.Modules.openCoverTensorPullbackComparison q U x
      e.inv.app F ≫ (Scheme.Modules.pullback (U.pullbackHom q x)).map (r₀ x) ≫
        e.hom.app G
    Pseudofunctor.DescentData.PairCompatibility r a b := by
  intro V Q C r
  have heq : r = fun x ↦ (Scheme.Modules.pullback (V.f x)).map δ := funext hr
  rw [heq]
  exact pairCompatibility_of_hom (Q.map (X := C.obj F) (Y := C.obj G) δ) a b

private lemma pullback_map_zero_of_comp
    {X Y Z : Scheme.{u}} (g : Z ⟶ Y) (f : Y ⟶ X) (h : Z ⟶ X)
    (hw : g ≫ f = h) {M N : X.Modules} (d : M ⟶ N)
    (hz : (Scheme.Modules.pullback f).map d = 0) :
    (Scheme.Modules.pullback h).map d = 0 := by
  subst h
  have hn := (Scheme.Modules.pullbackComp g f).hom.naturality d
  dsimp at hn
  rw [hz, Functor.map_zero, zero_comp] at hn
  apply (cancel_epi ((Scheme.Modules.pullbackComp g f).hom.app M)).mp
  simpa using hn.symm

set_option backward.defeqAttrib.useBackward true in
/-- At a sufficiently late stage, the two composites in the pairwise square
have a common value on every universal test. This is the overlap-defect
construction; its proof uses quasi-compactness and finite-presentation
vanishing on the overlap.
Source: Stacks Project, Tag 01ZR (3), first proof by Zariski gluing.
Proof: construct the overlap defect on the quasi-compact overlap, apply finite-presentation
vanishing, and transport the resulting equality through canonical comparisons.
(blueprint: lem-pc-fp-local-map-pair-composites-compatible). -/
/- Core overlap-defect eventual vanishing.
   (blueprint: lem-pc-fp-local-map-pair-composites-defect-zero-core)
   Proof: isolated overlap-defect construction. -/
theorem finitePresentation_local_map_pair_eventually_composites_defect_zero_core
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [QuasiSeparated f]
    (k : I) (hik : i ≤ k)
    (F G : (pullback f (Spec.map (R.map (homOfLE hik)))).Modules)
    (hF : F.IsFinitePresentation) (hFq : F.IsQuasicoherent)
    (hG : G.IsFinitePresentation) (hGq : G.IsQuasicoherent)
    (U₀ : (pullback f (Spec.map (R.map (homOfLE hik)))).OpenCover.{u})
    (a b : U₀.I₀) [IsAffine (U₀.X a)] [IsAffine (U₀.X b)]
    (δ : (Scheme.Modules.tensorPullback (overlapLimitMap R c f hik)).obj F ⟶
      (Scheme.Modules.tensorPullback (overlapLimitMap R c f hik)).obj G)
    (r₀ : ∀ x, (Scheme.Modules.pullback (U₀.f x)).obj F ⟶
      (Scheme.Modules.pullback (U₀.f x)).obj G)
    (hr : ∀ x,
      let p := overlapLimitMap R c f hik
      let e := Scheme.Modules.openCoverTensorPullbackComparison p U₀ x
      e.inv.app F ≫ (Scheme.Modules.pullback (U₀.pullbackHom p x)).map (r₀ x) ≫
        e.hom.app G = (Scheme.Modules.pullback ((U₀.pullback₁ p).f x)).map δ) :
    ∃ (l : I) (_hkl : k ≤ l), ∀ (m : I) (hkm : k ≤ m), l ≤ m →
      let q := baseChangeMap f
        (T := Over.mk (Spec.map (R.map (homOfLE hik))))
        (T' := Over.mk (Spec.map (R.map (homOfLE (hik.trans hkm)))))
        (Over.homMk (Spec.map (R.map (homOfLE hkm)))
          (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
      let U := U₀.pullback₁ q
      let Q := modulesPseudofunctor.toDescentData U.f
      let C := Scheme.Modules.tensorPullback q
      let r : ∀ x, (Q.obj (C.obj F)).obj x ⟶ (Q.obj (C.obj G)).obj x := fun x ↦
        let e := Scheme.Modules.openCoverTensorPullbackComparison q U₀ x
        e.inv.app F ≫ (Scheme.Modules.pullback (U₀.pullbackHom q x)).map (r₀ x) ≫
          e.hom.app G
      Pseudofunctor.DescentData.PairDefectZero r a b := by
  classical
  let W := pullback (U₀.f a) (U₀.f b)
  let g₁ : W ⟶ U₀.X a := pullback.fst (U₀.f a) (U₀.f b)
  let g₂ : W ⟶ U₀.X b := pullback.snd (U₀.f a) (U₀.f b)
  let t := g₁ ≫ U₀.f a
  let A := (Scheme.Modules.pullback g₁).obj ((Scheme.Modules.pullback (U₀.f a)).obj F)
  let B := (Scheme.Modules.pullback g₂).obj ((Scheme.Modules.pullback (U₀.f b)).obj G)
  let d : A ⟶ B := localMapPairOverlapDefect U₀ F G r₀ a b
  let := hF
  let := hFq
  let := hG
  let := hGq
  have hA : A.IsFinitePresentation := inferInstance
  have hAq : A.IsQuasicoherent := inferInstance
  have hB : B.IsFinitePresentation := inferInstance
  have hBq : B.IsQuasicoherent := inferInstance
  have : QuasiSeparatedSpace
      (pullback f (Spec.map (R.map (homOfLE hik))) : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated
      (pullback.snd f (Spec.map (R.map (homOfLE hik))))
  have : QuasiCompact (U₀.f b) := inferInstance
  have : CompactSpace W := by dsimp [W]; infer_instance
  have : QuasiCompact (t ≫ pullback.snd f (Spec.map (R.map (homOfLE hik)))) :=
    inferInstance
  have hd : (Scheme.Modules.pullback
      (pullback.fst t (overlapLimitMap R c f hik))).map d = 0 := by
    apply (localMapPairOverlapDefect_baseChange_iff U₀ F G r₀ a b
      (overlapLimitMap R c f hik)).mp
    exact transportedPairCompatibility_of_globalMap U₀ F G r₀ a b
      (overlapLimitMap R c f hik) δ hr
  obtain ⟨l, hkl, hl⟩ := finitePresentation_test_map_zero_eventually
    R c hc i f k hik t A B hA hAq hB hBq d hd
  refine ⟨l, hkl, ?_⟩
  intro m hkm hlm
  have hz : (Scheme.Modules.pullback
      (pullback.fst t (overlapStageMap R f hik hkm))).map d = 0 := by
    let ql := overlapStageMap R f hik hkl
    let qlm := overlapStageMap R f (hik.trans hkl) hlm
    let ψ : pullback t (overlapStageMap R f hik hkm) ⟶ pullback t ql :=
      pullback.lift (pullback.fst t (overlapStageMap R f hik hkm))
        (pullback.snd t (overlapStageMap R f hik hkm) ≫ qlm) (by
          rw [Category.assoc, overlapStageMap_comp]
          exact pullback.condition)
    exact pullback_map_zero_of_comp ψ (pullback.fst t ql)
      (pullback.fst t (overlapStageMap R f hik hkm)) (pullback.lift_fst _ _ _) d hl
  have hcStage := (localMapPairOverlapDefect_baseChange_iff U₀ F G r₀ a b
    (overlapStageMap R f hik hkm)).mpr hz
  exact pairDefectZero_of_pairCompatibility hcStage

/-- (blueprint: lem-pc-fp-local-map-pair-composites-compatible) -/
theorem finitePresentation_local_map_pair_eventually_composites_compatible
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [QuasiSeparated f]
    (k : I) (hik : i ≤ k)
    (F G : (pullback f (Spec.map (R.map (homOfLE hik)))).Modules)
    (hF : F.IsFinitePresentation) (hFq : F.IsQuasicoherent)
    (hG : G.IsFinitePresentation) (hGq : G.IsQuasicoherent)
    (U₀ : (pullback f (Spec.map (R.map (homOfLE hik)))).OpenCover.{u})
    (a b : U₀.I₀) [IsAffine (U₀.X a)] [IsAffine (U₀.X b)]
    (δ : (Scheme.Modules.tensorPullback (overlapLimitMap R c f hik)).obj F ⟶
      (Scheme.Modules.tensorPullback (overlapLimitMap R c f hik)).obj G)
    (r₀ : ∀ x, (Scheme.Modules.pullback (U₀.f x)).obj F ⟶
      (Scheme.Modules.pullback (U₀.f x)).obj G)
    (hr : ∀ x,
      let p := overlapLimitMap R c f hik
      let e := Scheme.Modules.openCoverTensorPullbackComparison p U₀ x
      e.inv.app F ≫ (Scheme.Modules.pullback (U₀.pullbackHom p x)).map (r₀ x) ≫
        e.hom.app G = (Scheme.Modules.pullback ((U₀.pullback₁ p).f x)).map δ) :
    ∃ (l : I) (_hkl : k ≤ l), ∀ (m : I) (hkm : k ≤ m), l ≤ m →
      let q := baseChangeMap f
        (T := Over.mk (Spec.map (R.map (homOfLE hik))))
        (T' := Over.mk (Spec.map (R.map (homOfLE (hik.trans hkm)))))
        (Over.homMk (Spec.map (R.map (homOfLE hkm)))
          (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
      let U := U₀.pullback₁ q
      let Q := modulesPseudofunctor.toDescentData U.f
      let C := Scheme.Modules.tensorPullback q
      let r : ∀ x, (Q.obj (C.obj F)).obj x ⟶ (Q.obj (C.obj G)).obj x := fun x ↦
        let e := Scheme.Modules.openCoverTensorPullbackComparison q U₀ x
        e.inv.app F ≫ (Scheme.Modules.pullback (U₀.pullbackHom q x)).map (r₀ x) ≫
          e.hom.app G
      Pseudofunctor.DescentData.PairCompatibility r a b := by
  obtain ⟨l, hkl, h⟩ := finitePresentation_local_map_pair_eventually_composites_defect_zero_core
    R c hc i f k hik F G hF hFq hG hGq U₀ a b δ r₀ hr
  refine ⟨l, hkl, ?_⟩
  intro m hkm hlm
  exact Pseudofunctor.DescentData.pairCompatibility_of_pairDefectZero _ _ _ (h m hkm hlm)

end AlgebraicGeometry
