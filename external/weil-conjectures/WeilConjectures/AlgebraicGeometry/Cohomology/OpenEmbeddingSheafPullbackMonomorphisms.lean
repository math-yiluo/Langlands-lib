/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Topology.Sheaves.Abelian

/-! Monomorphism preservation for extension by zero along an open embedding. -/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory TopologicalSpace

private theorem colim_preservesMonomorphisms_of_terminal
    {J : Type u} [SmallCategory J] (j : J) (hj : Limits.IsTerminal j) :
    (Limits.colim : (J ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).PreservesMonomorphisms := by
  have : ∀ F : J ⥤ AddCommGrpCat.{u}, IsIso ((Limits.colim.ι j).app F) :=
    fun F => Limits.isIso_ι_of_isTerminal hj F
  have : IsIso (Limits.colim.ι (C := AddCommGrpCat.{u}) j) := NatIso.isIso_of_isIso_app _
  exact Functor.PreservesMonomorphisms.of_iso
    (asIso (Limits.colim.ι (C := AddCommGrpCat.{u}) j))

private theorem colim_preservesMonomorphisms_of_empty
    {J : Type u} [SmallCategory J] [IsEmpty J] :
    (Limits.colim : (J ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).PreservesMonomorphisms := by
  constructor
  intro F G α hα
  have hF : Limits.IsInitial (Limits.colimit F) :=
    (Limits.isColimitEquivIsInitialOfIsEmpty AddCommGrpCat.{u} _) (Limits.colimit.isColimit F)
  exact hF.mono_from _

private theorem openEmbedding_comma_hasTerminal
    {X Y : TopCat.{u}} (f : X ⟶ Y) (hf : Topology.IsOpenEmbedding f)
    (V : (Opens Y)ᵒᵖ) (c : CostructuredArrow hf.functor.op V) :
    ∃ t : CostructuredArrow hf.functor.op V, Nonempty (Limits.IsTerminal t) := by
  let W : Opens X := (Opens.map f).obj V.unop
  have hV : V.unop ≤ hf.functor.obj W := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := c.hom.unop.le hy
    exact ⟨x, hy, rfl⟩
  let t : CostructuredArrow hf.functor.op V :=
    CostructuredArrow.mk (homOfLE hV).op
  refine ⟨t, ⟨Limits.IsTerminal.ofUniqueHom (fun a => ?_) (fun a m => ?_)⟩⟩
  · refine CostructuredArrow.homMk
      (homOfLE (show W ≤ a.left.unop from ?_)).op ?_
    · intro x hx
      obtain ⟨z, hz, he⟩ := a.hom.unop.le hx
      exact hf.injective he ▸ hz
    · apply Subsingleton.elim
  · apply CostructuredArrow.hom_ext
    apply Subsingleton.elim

private theorem openEmbedding_lan_preservesMonomorphisms
    {X Y : TopCat.{u}} (f : X ⟶ Y) (hf : Topology.IsOpenEmbedding f) :
    (hf.functor.op.lan : ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
      (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{u}).PreservesMonomorphisms := by
  constructor
  intro F G α hα
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro V
  have hc : (Limits.colim : (CostructuredArrow hf.functor.op V ⥤ AddCommGrpCat.{u}) ⥤
      AddCommGrpCat.{u}).PreservesMonomorphisms := by
    cases isEmpty_or_nonempty (CostructuredArrow hf.functor.op V) with
    | inl h => exact colim_preservesMonomorphisms_of_empty
    | inr h =>
      obtain ⟨t, ⟨ht⟩⟩ := openEmbedding_comma_hasTerminal f hf V h.some
      exact colim_preservesMonomorphisms_of_terminal t ht
  have : (hf.functor.op.lan ⋙
      (evaluation (Opens Y)ᵒᵖ AddCommGrpCat.{u}).obj V).PreservesMonomorphisms :=
    Functor.PreservesMonomorphisms.of_iso
      (lanEvaluationIsoColim AddCommGrpCat.{u} hf.functor.op V).symm
  exact inferInstanceAs (Mono ((hf.functor.op.lan ⋙
    (evaluation (Opens Y)ᵒᵖ AddCommGrpCat.{u}).obj V).map α))

/-- The sheaf pullback along the open-subspace functor preserves monomorphisms.
Source: Stacks Project, Tags 03DI and 03DJ.

Proof: let U be the open image of f. For an open V of Y, the pointwise left Kan
extension along hf.functor.op is the colimit over opens W of X with V contained in f(W).
If V is not contained in U, this category is empty, so the colimit is the zero group.
If V is contained in U, the object W = f⁻¹(V) is terminal in this indexing category:
every other W contains f⁻¹(V), and arrows in the opposite category are reversed inclusions.
Thus the colimit is F(f⁻¹(V)), naturally in the abelian presheaf F. Consequently the
left Kan extension of a sectionwise monomorphism is a sectionwise monomorphism, including
the empty-index case where its component is the identity of the zero group.
The inclusion of sheaves into presheaves preserves monomorphisms, and abelian
sheafification preserves finite limits, hence monomorphisms. Their composite with this
left Kan extension therefore preserves monomorphisms. Finally transport along
Functor.sheafPullbackConstruction.sheafPullbackIso, which identifies this composite
with the chosen left adjoint in the statement.
(blueprint: new-open-embedding-sheaf-pullback-preserves-monomorphisms) -/
theorem Topology.isOpenEmbedding_sheafPullback_preservesMonomorphisms
    {X Y : TopCat.{u}} (f : X ⟶ Y) (hf : Topology.IsOpenEmbedding f) :
    (let G := hf.functor
     haveI := hf.functor_isContinuous
     G.sheafPullback AddCommGrpCat.{u} (Opens.grothendieckTopology X)
       (Opens.grothendieckTopology Y)).PreservesMonomorphisms := by
  let G := hf.functor
  have := hf.functor_isContinuous
  have : (G.op.lan : ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
      (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{u}).PreservesMonomorphisms :=
    openEmbedding_lan_preservesMonomorphisms f hf
  have : (Functor.sheafPullbackConstruction.sheafPullback G AddCommGrpCat.{u}
      (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology Y)).PreservesMonomorphisms := by
    change (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
      G.op.lan ⋙ presheafToSheaf (Opens.grothendieckTopology Y)
        AddCommGrpCat.{u}).PreservesMonomorphisms
    have h1 : (sheafToPresheaf (Opens.grothendieckTopology X)
        AddCommGrpCat.{u}).PreservesMonomorphisms := by infer_instance
    have h2 : (presheafToSheaf (Opens.grothendieckTopology Y)
        AddCommGrpCat.{u}).PreservesMonomorphisms := by infer_instance
    infer_instance
  exact Functor.PreservesMonomorphisms.of_iso
    (Functor.sheafPullbackConstruction.sheafPullbackIso G AddCommGrpCat.{u}
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).symm
