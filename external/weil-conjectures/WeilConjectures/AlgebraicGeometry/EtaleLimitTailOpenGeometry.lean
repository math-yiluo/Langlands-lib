/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleLimitOpenRestrictedSystem
import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-! # The explicit inverse diagram of tail opens

Source: Stacks Project, Tag 09YQ, restriction to inverse-image opens.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false

private def overTailFunctor {I : Type u} [Preorder I] (i₀ : I) :
    Over (op i₀) ⥤ (Set.Ici i₀)ᵒᵖ where
  obj j := op ⟨j.left.unop, j.hom.unop.le⟩
  map f := (homOfLE f.left.unop.le).op

private def tailOverEquivalence {I : Type u} [Preorder I] (i₀ : I) :
    (Set.Ici i₀)ᵒᵖ ≌ Over (op i₀) where
  functor := tailOpenIndexFunctor i₀
  inverse := overTailFunctor i₀
  unitIso := NatIso.ofComponents (fun j ↦ eqToIso (by rfl))
  counitIso := NatIso.ofComponents (fun j ↦ Over.isoMk (Iso.refl _))

/-- The explicit tail-open cone is limiting.
Source: Mathlib `isLimitOpensCone`; Stacks Project, Tag 09YQ.
(blueprint: lem-weil-pbc-etale-limit-tail-open-geometry).

Proof: The opposite of the tail is equivalent to Over(op i₀). Under this
 equivalence, pull back Mathlib's opens diagram and its limiting cone for
 g₀⁻¹(W). The preimage-of-composition equality identifies every object with
 the displayed tail open. The restrictions have the same composites with
 their open inclusions, so these identifications intertwine the arrows and
 projections. Transport the limit along the diagram and cone isomorphisms. -/
private theorem tailOpenCone_isLimit {I : Type u} [Preorder I]
    [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    {X : Scheme.{u}} {i₀ : I} (g₀ : D.obj (op i₀) ⟶ X) (W : X.Opens) :
    Nonempty (IsLimit (tailOpenCone D c g₀ W)) := by
  let E := tailOverEquivalence i₀
  let U := g₀ ⁻¹ᵁ W
  let h := (isLimitOpensCone D c hc (op i₀) U).whiskerEquivalence E
  let q : E.functor ⋙ opensDiagram D (op i₀) U ≅ tailOpenDiagram D g₀ W :=
    NatIso.ofComponents (fun j ↦ (D.obj (op j.unop.val)).isoOfEq
      (Scheme.Hom.comp_preimage _ _ _).symm) (by
        intro j k f
        apply (cancel_mono (tailStageOpen D g₀ W k.unop).ι).1
        dsimp only [Functor.comp_map, E, tailOverEquivalence, tailOpenIndexFunctor,
          opensDiagram, tailOpenDiagram]
        simp only [Category.assoc, Scheme.isoOfEq_hom_ι, tailStageOpenMap,
          Scheme.Hom.resLE_comp_ι]
        rw [← Category.assoc, Scheme.isoOfEq_hom_ι]
        rfl)
  let t := (Cone.postcompose q.hom).obj
    ((opensCone D c (op i₀) U).whisker E.functor)
  let r : t ≅ tailOpenCone D c g₀ W := Cone.ext
    (c.pt.isoOfEq (Scheme.Hom.comp_preimage _ _ _).symm) (by
      intro j
      apply (cancel_mono (tailStageOpen D g₀ W j.unop).ι).1
      dsimp only [t, q, E, tailOverEquivalence, tailOpenIndexFunctor, Cone.postcompose,
        Cone.whisker, opensCone, tailOpenCone, NatIso.ofComponents, Functor.whiskerLeft]
      simp only [NatTrans.comp_app, Category.assoc, Scheme.isoOfEq_hom_ι,
        tailLimitOpenMap, Scheme.Hom.resLE_comp_ι]
      rw [← Category.assoc]
      have hi := Scheme.isoOfEq_hom_ι c.pt
        ((Scheme.Hom.comp_preimage (c.π.app (op i₀)) g₀ W).symm)
      exact congrArg (fun f ↦ f ≫ c.π.app (op j.unop.val)) hi.symm)
  exact ⟨((IsLimit.postcomposeHomEquiv q _).symm h).ofIsoLimit r⟩

/-- Restricted transition maps are affine base changes of the original transitions.
Source: Stacks Project, Tag 09YQ; Mathlib stability of affine maps under base change.
(blueprint: lem-weil-pbc-etale-limit-tail-open-geometry). -/
private theorem tailOpenDiagram_affine {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]
    {X : Scheme.{u}} {i₀ : I} (g₀ : D.obj (op i₀) ⟶ X) (W : X.Opens)
    {j k : (Set.Ici i₀)ᵒᵖ} (f : j ⟶ k) :
    IsAffineHom ((tailOpenDiagram D g₀ W).map f) := by
  let a := D.map (homOfLE (show k.unop.val ≤ j.unop.val from f.unop.le)).op
  have hp : IsPullback (tailStageOpenMap D g₀ W f.unop)
      (tailStageOpen D g₀ W j.unop).ι (tailStageOpen D g₀ W k.unop).ι a := by
    apply IsOpenImmersion.isPullback
    · simp [a, tailStageOpenMap]
    · simp only [a, Scheme.Opens.opensRange_ι, tailStageOpen,
        ← Scheme.Hom.comp_preimage, ← Category.assoc, ← D.map_comp]
      rfl
  exact MorphismProperty.of_isPullback hp.flip (inferInstance : IsAffineHom a)

/-- Every stage open is quasi-compact and quasi-separated, and the least is W.
Source: Stacks Project, Tag 09YQ; affine preimages preserve quasi-compactness.
(blueprint: lem-weil-pbc-etale-limit-tail-open-geometry).

Proof: The open O⁻¹(W) is isomorphic to W since W ≤ O. Pull it back along e
 and then along each affine transition. Compactness is preserved in each
 step. Quasi-separatedness is inherited by open subspaces. At the least
 index the transition is the identity, so restriction of e followed by
 the preceding open isomorphism identifies the stage with W. -/
private theorem tailOpenDiagram_geometry
    (X : Scheme.{u}) (O W : X.Opens) (hW : IsCompact (W : Set X)) (hWO : W ≤ O)
    {I : Type u} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]
    (i₀ : I) (e : D.obj (op i₀) ≅ O.toScheme) :
    (∀ j : (Set.Ici i₀)ᵒᵖ,
      CompactSpace ((tailOpenDiagram D (e.hom ≫ O.ι) W).obj j)) ∧
    (∀ j : (Set.Ici i₀)ᵒᵖ,
      QuasiSeparatedSpace ((tailOpenDiagram D (e.hom ≫ O.ι) W).obj j)) ∧
    Nonempty ((tailOpenDiagram D (e.hom ≫ O.ι) W).obj (op ⟨i₀, le_rfl⟩) ≅
      W.toScheme) := by
  let : CompactSpace W.toScheme := isCompact_iff_compactSpace.mp hW
  let : CompactSpace (O.ι ⁻¹ᵁ W).toScheme :=
    (Scheme.Opens.isoOfLE hWO).inv.homeomorph.compactSpace
  have hU : IsCompact (e.hom ⁻¹ᵁ O.ι ⁻¹ᵁ W : Set (D.obj (op i₀))) :=
    e.hom.isCompact_preimage (isCompact_iff_compactSpace.mpr
      (show CompactSpace ↥(O.ι ⁻¹ᵁ W) from ‹CompactSpace (O.ι ⁻¹ᵁ W).toScheme›))
  refine ⟨?_, ?_, ?_⟩
  · intro j
    apply isCompact_iff_compactSpace.mp
    change IsCompact (tailStageOpen D (e.hom ≫ O.ι) W j.unop : Set (D.obj (op j.unop.val)))
    dsimp only [tailStageOpen]
    rw [Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage]
    exact (D.map (homOfLE j.unop.property).op).isCompact_preimage hU
  · intro j
    exact (isQuasiSeparated_iff_quasiSeparatedSpace _
      (tailStageOpen D (e.hom ≫ O.ι) W j.unop).2).mp
        (.of_quasiSeparatedSpace _)
  · change Nonempty ((tailStageOpen D (e.hom ≫ O.ι) W ⟨i₀, le_rfl⟩).toScheme ≅ _)
    have heq : tailStageOpen D (e.hom ≫ O.ι) W ⟨i₀, le_rfl⟩ =
        e.hom ⁻¹ᵁ O.ι ⁻¹ᵁ W := by
      simp only [tailStageOpen, homOfLE_refl, op_id, D.map_id, Category.id_comp,
        Scheme.Hom.comp_preimage]
    exact ⟨(D.obj (op i₀)).isoOfEq heq ≪≫ e.hom.preimageIso _ ≪≫
      Scheme.Opens.isoOfLE hWO⟩

/-- The explicit tail-open diagram retains the geometric hypotheses of a system.
Source: Stacks Project, Tag 09YQ, restriction to opens; Mathlib `isLimitOpensCone`.
(blueprint: lem-weil-pbc-etale-limit-tail-open-geometry).

Proof: Identify the opposite tail with Over(op i₀), restrict Mathlib's opens
cone for (e;O.ι)⁻¹W, and transport across preimage-of-composition isomorphisms.
This proves the limit assertion. Each transition is a pullback of an affine
transition of D, hence affine. The open O⁻¹W is isomorphic to W because
W ≤ O. Its pullback along e is compact, and affine preimages preserve
compactness at every later stage. Open subspaces of quasi-separated spaces
are quasi-separated. At the least index the transition is the identity;
restricting e and using O⁻¹W ≅ W gives the final isomorphism. The empty-open
and singleton cases satisfy all these constructions without extra hypotheses. -/
theorem etale_limit_tail_open_geometry
    (X : Scheme.{u}) (O W : X.Opens) (hW : IsCompact (W : Set X)) (hWO : W ≤ O)
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]
    (i₀ : I) (e : D.obj (op i₀) ≅ O.toScheme) :
    let DW := tailOpenDiagram D (e.hom ≫ O.ι) W
    Nonempty (IsLimit (tailOpenCone D c (e.hom ≫ O.ι) W)) ∧
    (∀ j : (Set.Ici i₀)ᵒᵖ, CompactSpace (DW.obj j)) ∧
    (∀ j : (Set.Ici i₀)ᵒᵖ, QuasiSeparatedSpace (DW.obj j)) ∧
    (∀ (j k : (Set.Ici i₀)ᵒᵖ) (f : j ⟶ k), IsAffineHom (DW.map f)) ∧
    Nonempty (DW.obj (op ⟨i₀, le_rfl⟩) ≅ W.toScheme) := by
  obtain ⟨hcompact, hqs, hWiso⟩ := tailOpenDiagram_geometry X O W hW hWO D i₀ e
  exact ⟨tailOpenCone_isLimit D c hc _ W, hcompact, hqs,
    fun _ _ f ↦ tailOpenDiagram_affine D _ W f, hWiso⟩

end AlgebraicGeometry.Etale
