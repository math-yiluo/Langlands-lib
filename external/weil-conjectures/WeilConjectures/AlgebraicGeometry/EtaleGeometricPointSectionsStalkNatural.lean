/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageStalkGerm
import WeilConjectures.AlgebraicGeometry.SpecAlgClosedEtaleSheafConstant

/-! # Global sections of the inverse image at a geometric point

Source: Stacks Project, Tag 03Q1 (3), combined with Tag 03P5.
(blueprint: lem-weil-pbc-geometric-point-sections-stalk-natural).
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- The global-section comparison with the original geometric stalk is natural.
Source: Stacks Project, Tag 03Q1 (3), and the identity-point case of Tag 03P5.
(blueprint: lem-weil-pbc-geometric-point-sections-stalk-natural).

Proof:
1. For each F, apply the inverse-image stalk comparison to s and the identity point.
   Compose it with the germ of a global section at the identity neighbourhood.
   The latter is bijective by `Scheme.spec_algClosed_etale_sheaf_constant`, so
   their composite is bijective. Transport along identity composition to use
   `Scheme.etaleSetPullback (𝟙 _ ≫ s)` and the stalk at s.
2. Restrict a unit-pulled section along a. Its germ at the identity neighbourhood
   equals the germ at the pulled-back pointed neighbourhood, by the stalk colimit
   relations. The equation on the first projection identifies that lift with
   the canonical pullback lift; the second projection is identity by the over
   condition. The stalk comparison's germ formula gives the displayed equation.
3. Every original stalk element is represented by a section at a pointed
   neighbourhood. The germ formula and injectivity of the stalk comparison imply
   that every inverse-image stalk element is a unit-pulled germ. For a sheaf
   morphism, naturality of the inverse-image unit and of the stalk coprojections
   therefore proves naturality of the stalk comparison on all elements. The
   identity-neighbourhood germ is natural as well, so the composite bijections
   assemble to a natural isomorphism. -/
theorem etaleGeometricPointSectionsStalkNatural
    (S : Scheme.{u}) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :
    ∃ c : Scheme.etaleSetPullback (𝟙 (Spec (.of Ω)) ≫ s) ⋙
        (sheafSections (Spec (.of Ω)).smallEtaleTopology (Type (u + 1))).obj
          (op (Scheme.Etale.mk (𝟙 (Spec (.of Ω))))) ≅
        (Scheme.pointSmallEtale s).sheafFiber,
      ∀ (F : Sheaf S.smallEtaleTopology (Type (u + 1))) (W : S.Etale)
        (t : (Scheme.pointSmallEtale s).fiber.obj W)
        (a : Scheme.Etale.mk (𝟙 (Spec (.of Ω))) ⟶
          (MorphismProperty.Over.pullback @Etale ⊤ (𝟙 (Spec (.of Ω)) ≫ s)).obj W)
        (σ : F.obj.obj (op W)),
        a.left ≫ CategoryTheory.Limits.pullback.fst W.hom (𝟙 (Spec (.of Ω)) ≫ s) =
          t.left →
        (c.hom.app F) (((Scheme.etaleSetPullback (𝟙 (Spec (.of Ω)) ≫ s)).obj F).obj.map a.op
            (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (MorphismProperty.Over.pullback @Etale ⊤ (𝟙 (Spec (.of Ω)) ≫ s))
              (Type (u + 1)) (S.smallGrothendieckTopology @Etale)
              ((Spec (.of Ω)).smallGrothendieckTopology @Etale)).unit.app F).hom.app
                (op W) σ)) =
          (Scheme.pointSmallEtale s).toPresheafFiber W t F.obj σ := by
  classical
  let P := Spec (.of Ω)
  let L := Scheme.etaleSetPullback s
  let p := Scheme.pointSmallEtale (𝟙 P)
  let q := Scheme.pointSmallEtale s
  let T := Scheme.Etale.mk (𝟙 P)
  let t₀ : p.fiber.obj T := Over.homMk (𝟙 P) (Category.comp_id (𝟙 P))
  have stalkCompare (F : Sheaf S.smallEtaleTopology (Type (u + 1))) :
      ∃ d : p.sheafFiber.obj (L.obj F) → q.sheafFiber.obj F,
        Function.Bijective d ∧
        (∀ (W : S.Etale) (t : q.fiber.obj W) (σ : F.obj.obj (op W)),
          d (p.toPresheafFiber
            ((MorphismProperty.Over.pullback @Etale ⊤ s).obj W)
            (Over.homMk (CategoryTheory.Limits.pullback.lift t.left (𝟙 P) (Over.w t))
              (CategoryTheory.Limits.pullback.lift_snd t.left (𝟙 P) (Over.w t)))
            (L.obj F).obj
            (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (MorphismProperty.Over.pullback @Etale ⊤ s) (Type (u + 1))
              (S.smallGrothendieckTopology @Etale)
              (P.smallGrothendieckTopology @Etale)).unit.app F).hom.app (op W) σ)) =
                q.toPresheafFiber W t F.obj σ) := by
    obtain ⟨d, hd, hg, _⟩ := etaleSetInverseImageStalkGerm S P s F Ω (𝟙 P)
    simp only at d hd hg
    exact ⟨d, hd, hg⟩
  let d := fun F ↦ Classical.choose (stalkCompare F)
  have hd := fun F ↦ (Classical.choose_spec (stalkCompare F)).1
  have hg := fun F ↦ (Classical.choose_spec (stalkCompare F)).2
  let g := fun F ↦ p.toPresheafFiber T t₀ (L.obj F).obj
  have hb (F : Sheaf S.smallEtaleTopology (Type (u + 1))) : Function.Bijective (g F) :=
    (Scheme.spec_algClosed_etale_sheaf_constant Ω (L.obj F)).2
  have hdn (F F' : Sheaf S.smallEtaleTopology (Type (u + 1))) (ψ : F ⟶ F')
      (z : p.sheafFiber.obj (L.obj F)) :
      q.sheafFiber.map ψ (d F z) = d F' (p.sheafFiber.map (L.map ψ) z) := by
    obtain ⟨W, t, σ, hσ⟩ := q.toPresheafFiber_jointly_surjective (P := F.obj) (d F z)
    let B := (MorphismProperty.Over.pullback @Etale ⊤ s).obj W
    let r : p.fiber.obj B :=
      Over.homMk (CategoryTheory.Limits.pullback.lift t.left (𝟙 P) (Over.w t))
        (CategoryTheory.Limits.pullback.lift_snd t.left (𝟙 P) (Over.w t))
    let η := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ s) (Type (u + 1))
      (S.smallGrothendieckTopology @Etale) (P.smallGrothendieckTopology @Etale)
    let y := p.toPresheafFiber B r (L.obj F).obj ((η.unit.app F).hom.app (op W) σ)
    have hy : z = y := (hd F).1 (hσ.symm.trans (hg F W t σ).symm)
    subst z
    have hq := q.toPresheafFiber_naturality_apply ψ.hom W t σ
    have hp := p.toPresheafFiber_naturality_apply (L.map ψ).hom B r
      ((η.unit.app F).hom.app (op W) σ)
    have hη := etaleSetInverseImageCompositionUnits.2.1 S P s F F' ψ W σ
    have hpy : p.sheafFiber.map (L.map ψ) y =
        p.toPresheafFiber B r (L.obj F').obj
          ((η.unit.app F').hom.app (op W) (ψ.hom.app (op W) σ)) :=
      hp.trans (congrArg (p.toPresheafFiber B r (L.obj F').obj) hη.symm)
    exact (congrArg (q.sheafFiber.map ψ) (hg F W t σ)).trans
      (hq.trans ((hg F' W t (ψ.hom.app (op W) σ)).symm.trans
        (congrArg (d F') hpy.symm)))
  let c : L ⋙ (sheafSections P.smallEtaleTopology (Type (u + 1))).obj (op T) ≅
      q.sheafFiber := NatIso.ofComponents
        (fun F ↦ (Equiv.ofBijective (d F ∘ g F) ((hd F).comp (hb F))).toIso)
        (by
          intro F F' ψ
          apply ConcreteCategory.hom_ext
          intro z
          change d F' (g F' ((L.map ψ).hom.app (op T) z)) =
            q.sheafFiber.map ψ (d F (g F z))
          have hp := p.toPresheafFiber_naturality_apply (L.map ψ).hom T t₀ z
          exact (congrArg (d F') hp.symm).trans (hdn F F' ψ (g F z)).symm)
  refine ⟨c, ?_⟩
  intro F W t a σ ha
  change d F (p.toPresheafFiber T t₀ (L.obj F).obj
    ((L.obj F).obj.map a.op _)) = _
  have ht : p.fiber.map a t₀ =
      Over.homMk (CategoryTheory.Limits.pullback.lift t.left (𝟙 P) (Over.w t))
        (CategoryTheory.Limits.pullback.lift_snd t.left (𝟙 P) (Over.w t)) := by
    apply Over.OverMorphism.ext
    change 𝟙 P ≫ a.left = _
    refine (Category.id_comp a.left).trans ?_
    apply CategoryTheory.Limits.pullback.hom_ext
    · exact ha.trans (CategoryTheory.Limits.pullback.lift_fst _ _ _).symm
    · exact a.w.trans (CategoryTheory.Limits.pullback.lift_snd _ _ _).symm
  have hw := p.toPresheafFiber_w_apply a t₀ (L.obj F).obj
    (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ s) (Type (u + 1))
      (S.smallGrothendieckTopology @Etale)
      (P.smallGrothendieckTopology @Etale)).unit.app F).hom.app (op W) σ)
  rw [ht] at hw
  exact (congrArg (d F) hw).trans (hg F W t σ)

end AlgebraicGeometry
