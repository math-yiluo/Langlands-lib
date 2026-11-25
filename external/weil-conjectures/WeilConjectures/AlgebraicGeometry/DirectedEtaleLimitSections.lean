/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import WeilConjectures.AlgebraicGeometry.EtaleSetSectionContinuity
import WeilConjectures.AlgebraicGeometry.DirectedEtaleSectionIdentifications
import Mathlib.CategoryTheory.Filtered.Final

/-! # The directed continuity step for the explicit étale section cocone

Source: Stacks Project, Tags 09YQ and 03S2, as used in Tag 03Q9 in degree zero.
(blueprint: lem-weil-pbc-directed-etale-limit-sections).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Continuity for a directed inverse system of qcqs étale schemes over a fixed base.
The cocone is supplied by its natural transformation `ν`; `hν` fixes every component
as the inverse-image unit followed by restriction along the diagonal limit section.
This statement does not include the reduction from an arbitrary cofiltered category.

Source: Stacks Project, Theorem Tag 09YQ, degree zero, and Tag 03S2, used in Tag 03Q9.
(blueprint: lem-weil-pbc-directed-etale-limit-sections).

Proof:
Choose `i₀` using nonemptiness of the directed preorder and restrict to its upper tail.
The upper tail is cofinal: any index has a common upper bound with `i₀`, and any two
such upper bounds have a further common upper bound. Thus it preserves the scheme
limit and the section colimit. On stage `i₀`, pull back `H` along its étale structure
map to `R` and take the terminal étale object. Apply `etaleSetSectionContinuity` to
this sheaf and object. The identity morphism is quasi-compact and quasi-separated;
the stages are qcqs and their transition maps are affine, exactly as required there.
Its bijective colimit comparison gives a colimit cocone of the displayed section sets.
Use `etaleSetInverseImageCompositionUnits` to identify these inverse images with the
inverse images of `H` along each stage's map to `R` and along `p`. The cone equations
`h` identify the composites at the limit. `etaleSetInverseImageRestriction`, evaluated
at the terminal étale object of each stage, identifies its sections with `H(Bᵢ)`.
The restriction unit equation and the composition unit equation identify each
transition with `H` on the opposite stage morphism. At the limit they identify the
component with the unit for `p` followed by restriction along the map whose pullback
projections are the cone leg and the identity. The two projection equations determine
this map uniquely. These are exactly the components prescribed by `hν`, so natural
isomorphism transport and cofinality of the tail yield `IsColimit (Cocone.mk _ ν)`.
For a singleton index this is étale restriction; for an empty stage the empty-cover
sheaf axiom gives a singleton section set. Nonemptiness excludes an empty index. -/
theorem directedEtaleLimitSections
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    {R : Scheme.{u}} (B : Iᵒᵖ ⥤ R.Etale)
    (c : Cone (B ⋙ Scheme.Etale.forget R ⋙ Over.forget R))
    (p : c.pt ⟶ R) (h : ∀ i, c.π.app i ≫ (B.obj i).hom = p)
    (H : Sheaf R.smallEtaleTopology (Type (u + 1)))
    [∀ i : Iᵒᵖ, CompactSpace (B.obj i).left]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (B.obj i).left]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (B.map a).left]
    (_hc : IsLimit c)
    (ν : B.op ⋙ H.obj ⟶ (Functor.const Iᵒᵖᵒᵖ).obj
      (((Scheme.etaleSetPullback p).obj H).obj.obj (op (Scheme.Etale.mk (𝟙 c.pt)))))
    (_hν : ∀ i, ν.app i =
      (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (MorphismProperty.Over.pullback @Etale ⊤ p) (Type (u + 1))
        (R.smallGrothendieckTopology @Etale)
        (c.pt.smallGrothendieckTopology @Etale)).unit.app H).hom.app
          (op (B.obj i.unop))) ≫
        ((Scheme.etaleSetPullback p).obj H).obj.map
          (MorphismProperty.Over.homMk
            (B := (MorphismProperty.Over.pullback @Etale ⊤ p).obj (B.obj i.unop))
            (pullback.lift (c.π.app i.unop) (𝟙 _) (by simpa using h i.unop))
            (pullback.lift_snd _ _ _)).op) :
    Nonempty (IsColimit (Cocone.mk _ ν)) := by
  classical
  let i₀ : I := Classical.arbitrary I
  let D := B ⋙ Scheme.Etale.forget R ⋙ Over.forget R
  let G := (Scheme.etaleSetPullback (B.obj (op i₀)).hom).obj H
  let W₀ : (D.obj (op i₀)).Etale := Scheme.Etale.mk (𝟙 _)
  have : ∀ i : Iᵒᵖ, CompactSpace (D.obj i) :=
    fun i ↦ inferInstanceAs (CompactSpace (B.obj i).left)
  have : ∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i) :=
    fun i ↦ inferInstanceAs (QuasiSeparatedSpace (B.obj i).left)
  have : ∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f) :=
    fun f ↦ inferInstanceAs (IsAffineHom (B.map f).left)
  have : QuasiCompact W₀.hom := inferInstanceAs (QuasiCompact (𝟙 (D.obj (op i₀))))
  have : QuasiSeparated W₀.hom := inferInstanceAs (QuasiSeparated (𝟙 (D.obj (op i₀))))
  obtain ⟨E, e, μ, hE, hμ, hbij, _⟩ :=
    etaleSetSectionContinuity D c _hc i₀ G W₀
  obtain ⟨a, l, ha, hl⟩ :=
    directedEtaleSectionIdentifications B c p h H i₀ ν _hν
  let T := (Over.forget (op i₀)).op
  let κ := (Cocone.mk _ ν).whisker T
  let α : E ≅ T ⋙ (B.op ⋙ H.obj) :=
    NatIso.ofComponents (fun j ↦ e j.unop ≪≫ (a j.unop).symm) (by
      intro j k f
      dsimp only [Iso.trans_hom, Iso.symm_hom]
      apply (cancel_mono (a k.unop).hom).1
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      change E.map f ≫ (e k.unop).hom =
        (e j.unop).hom ≫ (a j.unop).inv ≫
          H.obj.map (B.map f.unop.left).op ≫ (a k.unop).hom
      rw [ha j.unop k.unop f.unop]
      simp only [Iso.inv_hom_id_assoc]
      have he := hE j.unop k.unop f.unop
      rw [← he]
      simp only [Iso.hom_inv_id_assoc, Quiver.Hom.op_unop])
  have : IsIso ((colimit.isColimit E).desc (Cocone.mk _ μ)) :=
    (isIso_iff_bijective _).2 hbij
  have hcE : IsColimit (Cocone.mk _ μ) := (colimit.isColimit E).ofPointIso
  let χ : (Cocone.precompose α.hom).obj κ ≅ Cocone.mk _ μ :=
    Cocone.ext l (by
      intro j
      change (e j.unop).hom ≫ (a j.unop).inv ≫ ν.app (op j.unop.left) ≫ l.hom =
        μ.app j
      rw [hl j.unop, Iso.inv_hom_id_assoc]
      have hm := hμ j.unop
      rw [← hm]
      simp only [Iso.hom_inv_id_assoc])
  have hcκ : IsColimit κ :=
    (IsColimit.precomposeHomEquiv α κ) (hcE.ofIsoColimit χ.symm)
  exact ⟨Functor.Final.isColimitWhiskerEquiv T (Cocone.mk _ ν) hcκ⟩

end AlgebraicGeometry
