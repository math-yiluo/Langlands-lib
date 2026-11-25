/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OpenCoverTensorPullbackComparison
public import WeilConjectures.AlgebraicGeometry.LocalOverlapTransitions
public import WeilConjectures.AlgebraicGeometry.LocalMapPairCompatibility
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.FinitePresentationTestMapZeroEventually
public import WeilConjectures.AlgebraicGeometry.LocalMapPairDefect
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent
import WeilConjectures.AlgebraicGeometry.FinitePresentationLocalMapPairEventuallyCompositesCompatible

/-! # Eventual compatibility for one pair of local maps

Source: Stacks Project, Tag 01ZR (3), first proof by Zariski gluing.
(blueprint: lem-pc-fp-local-map-pair-eventually). -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

attribute [local irreducible] Scheme.Modules.tensorPullback
  Scheme.Modules.openCoverTensorPullbackComparison

private theorem pairDefectZero_of_pairCompatibility
    {C : Type*} [Category C] {P : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat}
    {ι : Type*} {S : C} {X : ι → C} {f : ∀ a, X a ⟶ S}
    {D₁ D₂ : P.DescentData f} (r : ∀ a, D₁.obj a ⟶ D₂.obj a) (a b : ι)
    (h : Pseudofunctor.DescentData.PairCompatibility r a b) :
    Pseudofunctor.DescentData.PairDefectZero r a b := by
  refine fun {W} t g₁ g₂ h₁ h₂ => ?_
  exact ⟨_, rfl, (h.comm t g₁ g₂ h₁ h₂).symm⟩

/-- At a sufficiently late stage, the two composites in the pairwise square
have a common value on every universal test. This is the overlap-defect
construction; its proof uses quasi-compactness and finite-presentation
vanishing on the overlap.
Source: Stacks Project, Tag 01ZR (3), first proof by Zariski gluing.
(blueprint: lem-pc-fp-local-map-pair-defect-zero). -/
theorem finitePresentation_local_map_pair_eventually_defect_zero
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
  obtain ⟨l, hkl, h⟩ := finitePresentation_local_map_pair_eventually_composites_compatible
    R c hc i f k hik F G hF hFq hG hGq U₀ a b δ r₀ hr
  refine ⟨l, hkl, ?_⟩
  intro m hkm hlm
  exact pairDefectZero_of_pairCompatibility _ a b (h m hkm hlm)


set_option linter.unusedVariables false in
/-- One pair of recovered local maps satisfies the overlap equation at every
sufficiently late stage.
Source: Stacks Project, Tag 01ZR (3), first proof by Zariski gluing.
(blueprint: lem-pc-fp-local-map-pair-eventually). -/
theorem finitePresentation_local_map_pair_eventually
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
    ∃ (l : I) (hkl : k ≤ l), ∀ (m : I) (hkm : k ≤ m), l ≤ m →
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
  obtain ⟨l, hkl, h⟩ := finitePresentation_local_map_pair_eventually_defect_zero
    R c hc i f k hik F G hF hFq hG hGq U₀ a b δ r₀ hr
  exact ⟨l, hkl, fun m hkm hlm =>
    CategoryTheory.Pseudofunctor.DescentData.pairCompatibility_of_pairDefectZero
      _ _ _ (h m hkm hlm)⟩

end AlgebraicGeometry
