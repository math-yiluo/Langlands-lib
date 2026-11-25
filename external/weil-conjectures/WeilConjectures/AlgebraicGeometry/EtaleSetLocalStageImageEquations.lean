/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSetSheafComparison

/-! # Preservation of local image equations under stage transport

Source: Stacks Project, Sites Tags 03CB and 03CC, composition of inverse images.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

local notation "setPull" => Scheme.etaleSetPullback
local notation "baseChange" => MorphismProperty.Over.pullback @Etale ⊤
local notation "η[" S "," T "]" e =>
  Adjunction.unit
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (baseChange e) _
      (Scheme.smallGrothendieckTopology @Etale S) (Scheme.smallGrothendieckTopology @Etale T))

-- Expanding units and composition comparisons requires extra elaboration fuel.
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The image equations of a local family are preserved by every stage refinement.
The cone need not be limiting; affineness, directedness and covering are unnecessary.

Source: Stacks Project, Sites Tags 03CB and 03CC; unit-compatible composition
in lem-weil-pbc-sets-etale-inverse-image-composition-units.
(blueprint: lem-weil-pbc-sets-local-stage-image-equations).

Proof: Write h = D(r.left), f = D(j.hom), g = c.π.app j'.left.
The over-category equation gives h ≫ f = D(j'.hom); the cone equation gives
g ≫ h = c.π.app j.left. Expand each sheaf comparison as its adjunction unit
followed by the chosen unit-compatible inverse-image composition isomorphism.
Naturality of the g-unit in the sheaf morphism for (f,h), associativity of these
composition isomorphisms, and the composition-unit equation for (h,g) show
that applying β_j' to the transported s_q equals applying β_j to s_q, followed
by restriction along the canonical isomorphism between g^*h^*V_q and p_j^*V_q.
Substitute the original equation with t. Combine restrictions using the
presheaf composition law. Naturality and associativity of the canonical
iterated-base-change isomorphisms identify the resulting arrow to p_i₀^*W
with B_j'(a'_q) ≫ e_j'⁻¹: both have the same projections to V_q, W, and c.pt.
This yields exactly the displayed equation. Equality elimination handles the
non-definitional commuting triangles; proof irrelevance removes dependence on
their witnesses. This calculation is pointwise in q, so also covers an empty
family, and uses neither existence of a global section at a stage nor gluing. -/
theorem etaleSet_localStageImageEquations
    {I : Type u} [Category I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    (c : Cone D) (i₀ : I)
    (G : Sheaf (D.obj (op i₀)).smallEtaleTopology (Type (u + 1)))
    (W : (D.obj (op i₀)).Etale)
    (t : ((Scheme.etaleSetPullback (c.π.app (op i₀))).obj G).obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj W))) :
    let H := fun j : Over (op i₀) ↦ (Scheme.etaleSetPullback (D.map j.hom)).obj G
    let L := (Scheme.etaleSetPullback (c.π.app (op i₀))).obj G
    let B := fun j : Over (op i₀) ↦ MorphismProperty.Over.pullback @Etale ⊤ (c.π.app j.left)
    let Y := fun j : Over (op i₀) ↦
      (MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).obj W
    let e := fun j : Over (op i₀) ↦
      (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
        (c.π.app j.left) (D.map j.hom) (c.π.app (op i₀)) (c.w j.hom).symm).app W
    let β := fun j : Over (op i₀) ↦
      etaleSetSheafComparison (c.π.app j.left) (D.map j.hom)
        (c.π.app (op i₀)) (c.w j.hom) G
    ∀ (j : Over (op i₀)) (n : ℕ) (V : Fin n → (D.obj j.left).Etale)
      (a : ∀ q, V q ⟶ Y j) (s : ∀ q, (H j).obj.obj (op (V q))),
      (∀ q, (β j).hom.app (op (V q)) (s q) =
        L.obj.map ((B j).map (a q) ≫ (e j).inv).op t) →
    ∀ (j' : Over (op i₀)) (r : j' ⟶ j),
      let b := MorphismProperty.Over.pullback @Etale ⊤ (D.map r.left)
      let hr := (D.map_comp r.left j.hom).symm.trans
        (congrArg (fun z : j'.left ⟶ op i₀ ↦ D.map z) r.w)
      let d := (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
        (D.map r.left) (D.map j.hom) (D.map j'.hom) hr.symm).app W
      let V' := fun q ↦ b.obj (V q)
      let a' := fun q ↦ b.map (a q) ≫ d.inv
      let s' := fun q ↦ (etaleSetSheafComparison (D.map r.left) (D.map j.hom)
        (D.map j'.hom) hr G).hom.app (op (V q)) (s q)
      ∀ q, (β j').hom.app (op (V' q)) (s' q) =
        L.obj.map ((B j').map (a' q) ≫ (e j').inv).op t := by
  have hcomp {R S T X : Scheme.{u}} (f : S ⟶ R) (h : T ⟶ S) (g : X ⟶ T)
      (k : T ⟶ R) (l : X ⟶ R) (p : X ⟶ S)
      (hk : h ≫ f = k) (hl : g ≫ k = l) (hp : g ≫ h = p)
      (G : Sheaf R.smallEtaleTopology (Type (u + 1))) (U : S.Etale) :
      (etaleSetSheafComparison h f k hk G).hom.app (op U) ≫
        (etaleSetSheafComparison g k l hl G).hom.app (op ((baseChange h).obj U)) =
      (etaleSetSheafComparison p f l
        (by rw [← hp, Category.assoc, hk, hl]) G).hom.app (op U) ≫
        ((setPull l).obj G).obj.map
          ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
            g h p hp.symm).inv.app U).op := by
    subst k
    subst l
    subst p
    let α := (Classical.choose etaleSetInverseImageCompositionUnits.2.2 R S T f h).hom.app G
    let β := (Classical.choose etaleSetInverseImageCompositionUnits.2.2 R T X (h ≫ f) g).hom.app G
    let γ := (Classical.choose etaleSetInverseImageCompositionUnits.2.2 R S X f (g ≫ h)).hom.app G
    let δ := (Classical.choose etaleSetInverseImageCompositionUnits.2.2 S T X h g).hom.app
      ((setPull f).obj G)
    have hs := NatTrans.congr_app
      (congrArg (fun e ↦ e.hom) ((η[T, X] g).naturality α)) (op ((baseChange h).obj U))
    have hc := NatTrans.congr_app
      (congrArg (fun e ↦ e.hom)
        ((Classical.choose_spec etaleSetInverseImageCompositionUnits.2.2).2.2
          R S T X f h g G)) (op ((baseChange g).obj ((baseChange h).obj U)))
    change α.hom.app (op ((baseChange h).obj U)) ≫
        ((η[T, X] g).app ((setPull (h ≫ f)).obj G)).hom.app (op ((baseChange h).obj U)) =
      ((η[T, X] g).app ((setPull h).obj ((setPull f).obj G))).hom.app (op ((baseChange h).obj U)) ≫
        ((setPull g).map α).hom.app (op ((baseChange g).obj ((baseChange h).obj U))) at hs
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      eqToHom_refl, Category.comp_id] at hc
    change ((η[S, T] h).app ((setPull f).obj G)).hom.app (op U) ≫
        α.hom.app (op ((baseChange h).obj U)) ≫
        ((η[T, X] g).app ((setPull (h ≫ f)).obj G)).hom.app (op ((baseChange h).obj U)) ≫
        β.hom.app (op ((baseChange g).obj ((baseChange h).obj U))) =
      ((η[S, X] (g ≫ h)).app ((setPull f).obj G)).hom.app (op U) ≫
        γ.hom.app (op ((baseChange (g ≫ h)).obj U)) ≫
        ((setPull (g ≫ h ≫ f)).obj G).obj.map
          ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) g h).inv.app U).op
    change ((setPull g).map α).hom.app (op ((baseChange g).obj ((baseChange h).obj U))) ≫
        β.hom.app (op ((baseChange g).obj ((baseChange h).obj U))) =
      δ.hom.app (op ((baseChange g).obj ((baseChange h).obj U))) ≫
        γ.hom.app (op ((baseChange g).obj ((baseChange h).obj U))) at hc
    rw [reassoc_of% hs, hc]
    have hu : ((η[S, T] h).app ((setPull f).obj G)).hom.app (op U) ≫
        ((η[T, X] g).app ((setPull h).obj ((setPull f).obj G))).hom.app
          (op ((baseChange h).obj U)) ≫
        δ.hom.app (op ((baseChange g).obj ((baseChange h).obj U))) =
      ((η[S, X] (g ≫ h)).app ((setPull f).obj G)).hom.app (op U) ≫
        ((setPull (g ≫ h)).obj ((setPull f).obj G)).obj.map
          ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) g h).inv.app U).op := by
      apply ConcreteCategory.hom_ext
      intro x
      simp only [comp_apply]
      exact (Classical.choose_spec etaleSetInverseImageCompositionUnits.2.2).1
        S T X h g ((setPull f).obj G) U x
    rw [reassoc_of% hu]
    exact congrArg (fun k ↦ ((η[S, X] (g ≫ h)).app ((setPull f).obj G)).hom.app (op U) ≫ k)
      (γ.hom.naturality
        ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) g h).inv.app U).op)
  dsimp only
  intro j n V a s hs j' r q
  let hr := (D.map_comp r.left j.hom).symm.trans
    (congrArg (fun z : j'.left ⟶ op i₀ ↦ D.map z) r.w)
  have hb := hcomp (D.map j.hom) (D.map r.left) (c.π.app j'.left)
    (D.map j'.hom) (c.π.app (op i₀)) (c.π.app j.left) hr (c.w j'.hom)
    (c.w r.left) G (V q)
  have hb' := ConcreteCategory.congr_hom hb (s q)
  simp only [comp_apply] at hb'
  erw [hs q] at hb'
  erw [hb']
  erw [← Functor.map_comp_apply, ← op_comp]
  congr 2
  apply congrArg (((Scheme.etaleSetPullback (c.π.app (op i₀))).obj G).obj.map)
  apply congrArg Quiver.Hom.op
  -- Naturality and associativity of the canonical pullback pasting maps.
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · simp [MorphismProperty.Over.pullback, MorphismProperty.Over.pullbackComp,
      Category.assoc]
  · simp [MorphismProperty.Over.pullback, MorphismProperty.Over.pullbackComp,
      Category.assoc]

end AlgebraicGeometry
