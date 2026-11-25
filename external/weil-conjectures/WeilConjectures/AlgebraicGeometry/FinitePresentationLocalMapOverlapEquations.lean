/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
public import WeilConjectures.AlgebraicGeometry.OpenCoverTensorPullbackComparison
public import WeilConjectures.AlgebraicGeometry.LocalMapPullbackFamily
public import WeilConjectures.AlgebraicGeometry.LocalMapRecovery
import WeilConjectures.AlgebraicGeometry.FinitePresentationLocalMapPairEventually
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent
import Mathlib.Data.Finset.Order

/-! # Eventual overlap equations

Source: Stacks Project, Tags 01ZR and 05N7.
(blueprint: lem-pc-fp-local-map-overlap-equations). -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem finiteCommonStage
    {J : Type*} [Preorder J] [IsDirected J (· ≤ ·)]
    {A : Type*} [Finite A] (k : J) {P : A → (m : J) → k ≤ m → Prop}
    (h : ∀ a, ∃ (l : J) (_hkl : k ≤ l), ∀ (m : J) (hkm : k ≤ m), l ≤ m → P a m hkm) :
    ∃ (l : J) (hkl : k ≤ l), ∀ a, P a l hkl := by
  classical
  choose stage hstage hcomm using h
  let : Fintype A := Fintype.ofFinite _
  let : Nonempty J := ⟨k⟩
  obtain ⟨l, hl⟩ := (insert k (Finset.univ.image stage)).exists_le
  have hkl : k ≤ l := hl k (Finset.mem_insert_self _ _)
  refine ⟨l, hkl, fun a ↦ hcomm a l hkl ?_⟩
  exact hl (stage a)
    (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩))

attribute [local irreducible] Scheme.Modules.tensorPullback
  Scheme.Modules.pullback Scheme.Modules.pushforward Scheme.Modules.pullbackComp
  Scheme.Modules.openCoverTensorPullbackComparison

private theorem tensorPullbackProperties {X Y : Scheme.{u}} (p : Y ⟶ X)
    (M : X.Modules) (hM : M.IsFinitePresentation) (hMq : M.IsQuasicoherent) :
    ((Scheme.Modules.tensorPullback p).obj M).IsFinitePresentation ∧
      ((Scheme.Modules.tensorPullback p).obj M).IsQuasicoherent := by
  let := hM
  let := hMq
  let e := (Scheme.Modules.nonempty_tensorPullbackAdjunction p).some.leftAdjointUniq
    (Scheme.Modules.pullbackPushforwardAdjunction p)
  refine ⟨Scheme.Modules.isFinitePresentation_of_iso (e.app M).symm, ?_⟩
  exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
    (e.app M).symm inferInstance

private theorem restrictionComponent {X : Scheme.{u}} (U : X.OpenCover.{u})
    {M N : X.Modules} (φ : M ⟶ N) (a : U.I₀) :
    ((modulesPseudofunctor.toDescentData U.f).map φ).hom a =
      (Scheme.Modules.pullback (U.f a)).map φ := rfl

private theorem composeDescentComponents {X : Scheme.{u}} (U : X.OpenCover.{u})
    {M₁ M₂ M₃ M₄ : X.Modules} (κ : M₁ ⟶ M₂)
    (φ : (modulesPseudofunctor.toDescentData U.f).obj M₂ ⟶
      (modulesPseudofunctor.toDescentData U.f).obj M₃) (ρ : M₃ ⟶ M₄) (a : U.I₀) :
    (((modulesPseudofunctor.toDescentData U.f).map κ ≫ φ ≫
      (modulesPseudofunctor.toDescentData U.f).map ρ).hom a) =
        (Scheme.Modules.pullback (U.f a)).map κ ≫ φ.hom a ≫
          (Scheme.Modules.pullback (U.f a)).map ρ := by
  rw [Pseudofunctor.DescentData.comp_hom, Pseudofunctor.DescentData.comp_hom]
  rw [restrictionComponent U κ a, restrictionComponent U ρ a]

private theorem assocFive {D : Type*} [Category* D] {A B C E F G : D}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ E) (d : E ⟶ F) (e : F ⟶ G) :
    a ≫ (b ≫ c ≫ d) ≫ e = a ≫ b ≫ c ≫ d ≫ e := by
  simp only [Category.assoc]

-- The preserved signature includes the unused let-bound pullback cover V₀.
set_option linter.unusedVariables false in
-- Extra fuel checks the dependent descent-data interfaces without raising the wall-clock limit.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The local family eventually descends, including after composition with global maps.
Source: Stacks Project, Limits, Tag 01ZR, first proof, agreement on overlaps;
Algebra, Tag 05N7 (3).
(blueprint: lem-pc-fp-local-map-overlap-equations).

Proof: First substitute the equality identifying A₀ with module base change.
At stage k take the difference of the two restrictions of r₀ on each pairwise
intersection of cover members. Their pullbacks to the limit agree, since both recover
the restriction of the same global map δ. Pullback composition identifies the two
restrictions, so their difference pulls back to zero. Quasi-separatedness makes each
intersection quasi-compact. Restricted tensor pullbacks of Fj and Gj remain finitely
presented and quasi-coherent. Apply finitePresentation_zero_map_descent to this
intersection over Spec R_k, using the pullback universal properties to identify its
identity-stage and later base changes. There are finitely many pairs. Directedness
gives one common later stage, and functors preserve zero maps, so all defects vanish
there. Every test scheme mapping to two cover members factors through their
intersection. Pullback of its equality is the universal-test compatibility equation
for the displayed family of pulled-back maps. Assemble its descent morphism with
those components. The transition q is affine, as a base change of a map between
affine schemes; hence the inverse images of the affine cover members are affine.
For arbitrary F', G', κ and ρ in the conclusion, compose this descent morphism on
the left with Q.map κ and on the right with Q.map ρ. The components of Q.map are
ordinary restriction of the maps; functoriality and associativity give exactly the
five displayed factors defining r. This uses no inverse or property of κ and ρ.
The component identities follow from the construction. Empty covers impose no
compatibility equations and use k itself. Empty intersections, zero modules and
identity transitions cause no exceptions. No new-stage recovery is asserted. -/
theorem finitePresentation_local_maps_eventual_overlap_equations
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f] :
    (∀ (j : I) (hij : i ≤ j) (Fj Gj : (pullback f (Spec.map (R.map (homOfLE hij)))).Modules),
      Fj.IsFinitePresentation → Fj.IsQuasicoherent →
      Gj.IsFinitePresentation → Gj.IsQuasicoherent →
      ∀ (k : I) (hjk : j ≤ k),
        ∀ (A₀ : (pullback f (Spec.map (R.map (homOfLE hij)))).Modules ⥤
            (pullback f (Spec.map (R.map (homOfLE (hij.trans hjk))))).Modules),
          A₀ = Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
            (Over.homMk (Spec.map (R.map (homOfLE hjk)))
              (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)) →
        let B₀ := Scheme.Modules.moduleBaseChange f
              (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
              (T' := Over.mk (c.π.app (op i)))
              (Over.homMk (c.π.app (op k)) (c.w (homOfLE (hij.trans hjk)).op))
        ∀ δ : B₀.obj (A₀.obj Fj) ⟶ B₀.obj (A₀.obj Gj),
        ∀ (U₀ : (pullback f (Spec.map (R.map (homOfLE (hij.trans hjk))))).OpenCover.{u}),
          Finite U₀.I₀ → (∀ a, IsAffine (U₀.X a)) →
          let Q₀ := modulesPseudofunctor.toDescentData U₀.f
          let p₀ := baseChangeMap f
            (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op k)) (c.w (homOfLE (hij.trans hjk)).op))
          let V₀ := U₀.pullback₁ p₀
          ∀ r₀ : ∀ a, (Q₀.obj (A₀.obj Fj)).obj a ⟶ (Q₀.obj (A₀.obj Gj)).obj a,
            localMapRecovery p₀ U₀ (A₀.obj Fj) (A₀.obj Gj) δ r₀ →
          ∃ (j' : I) (hkj' : k ≤ j'),
            let q := (baseChangeMap f
              (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
              (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans (hjk.trans hkj'))))))
              (Over.homMk (Spec.map (R.map (homOfLE hkj')))
                (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)));
            let U : (pullback f
              (Spec.map (R.map (homOfLE (hij.trans (hjk.trans hkj')))))).OpenCover.{u} :=
              U₀.pullback₁ q
            let Q := modulesPseudofunctor.toDescentData U.f
            let C := Scheme.Modules.tensorPullback q
            (∀ α, IsAffine (U.X α)) ∧
            (∀ (F' G' : (pullback f
                (Spec.map (R.map (homOfLE (hij.trans (hjk.trans hkj')))))).Modules)
              (κ : F' ⟶ C.obj (A₀.obj Fj)) (ρ : C.obj (A₀.obj Gj) ⟶ G'),
              let r : ∀ α, (Q.obj F').obj α ⟶ (Q.obj G').obj α :=
                localMapPullbackFamily q U₀ (A₀.obj Fj) (A₀.obj Gj) F' G' κ ρ r₀
              ∃ ψ : Q.obj F' ⟶ Q.obj G', ∀ α, ψ.hom α = r α))  := by
  classical
  intro j hij Fj Gj hF hFq hG hGq k hjk A₀ hA B₀ δ U₀ hfin haff Q₀ p₀ _V₀ r₀ hr₀
  subst A₀
  let h := baseChangeMap f
    (T := Over.mk (Spec.map (R.map (homOfLE hij))))
    (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
    (Over.homMk (Spec.map (R.map (homOfLE hjk)))
      (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
  let F := (Scheme.Modules.tensorPullback h).obj Fj
  let G := (Scheme.Modules.tensorPullback h).obj Gj
  obtain ⟨hFp, hFqc⟩ := tensorPullbackProperties h Fj hF hFq
  obtain ⟨hGp, hGqc⟩ := tensorPullbackProperties h Gj hG hGq
  have : Finite U₀.I₀ := hfin
  have : ∀ a, IsAffine (U₀.X a) := haff
  have one (ab : U₀.I₀ × U₀.I₀) := finitePresentation_local_map_pair_eventually
    R c hc i f k (hij.trans hjk) F G hFp hFqc hGp hGqc U₀ ab.1 ab.2 δ r₀ hr₀
  obtain ⟨l, hkl, hl⟩ := finiteCommonStage k one
  refine ⟨l, hkl, ?_⟩
  intro q U Q C
  have hq : baseChangeMap f
      (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
      (T' := Over.mk (Spec.map (R.map (homOfLE ((hij.trans hjk).trans hkl)))))
      (Over.homMk (Spec.map (R.map (homOfLE hkl)))
        (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)) = q := by rfl
  have : IsAffineHom q := MorphismProperty.of_isPullback
    (isPullback_baseChangeMap f _).flip (by
      change IsAffineHom (Spec.map (R.map (homOfLE hkl)))
      infer_instance)
  clear_value q
  rw [hq] at hl
  refine ⟨?_, ?_⟩
  · intro a
    have : IsAffine (U₀.X a) := haff a
    change IsAffine (pullback q (U₀.f a))
    infer_instance
  · let r : ∀ a, (Q.obj (C.obj F)).obj a ⟶ (Q.obj (C.obj G)).obj a := fun a ↦
      let e := Scheme.Modules.openCoverTensorPullbackComparison q U₀ a
      e.inv.app F ≫ (Scheme.Modules.pullback (U₀.pullbackHom q a)).map (r₀ a) ≫
        e.hom.app G
    let ψ₀ : Q.obj (C.obj F) ⟶ Q.obj (C.obj G) :=
      Pseudofunctor.DescentData.homOfPairCompatibility r (fun a b ↦ hl (a, b))
    intro F' G' κ ρ r'
    refine ⟨Q.map κ ≫ ψ₀ ≫ Q.map ρ, ?_⟩
    intro a
    refine (composeDescentComponents U κ ψ₀ ρ a).trans ?_
    dsimp only [ψ₀, Pseudofunctor.DescentData.homOfPairCompatibility, r, r']
    dsimp only [Scheme.Modules.moduleBaseChange, h, F, G, U]
    unfold localMapPullbackFamily
    exact assocFive (D := (U.X a).Modules)
      ((Scheme.Modules.pullback (U.f a)).map κ)
      ((Scheme.Modules.openCoverTensorPullbackComparison q U₀ a).inv.app F)
      ((Scheme.Modules.pullback (U₀.pullbackHom q a)).map (r₀ a))
      ((Scheme.Modules.openCoverTensorPullbackComparison q U₀ a).hom.app G)
      ((Scheme.Modules.pullback (U.f a)).map ρ)



end AlgebraicGeometry
