/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.GrothendieckHypercoverBaseChange
import WeilConjectures.AlgebraicGeometry.FiniteSplitHypercoverTruncation
import WeilConjectures.AlgebraicGeometry.FiniteSplitHypercoverExtension
import WeilConjectures.AlgebraicGeometry.FiniteHypercoverDescentParts
import WeilConjectures.AlgebraicGeometry.FiniteHypercoverDescentParts
/-! # Descent of a finite hypercover skeleton to a full stage hypercover -/
@[expose] public section
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.FiniteSplitEtaleHypercover

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A fixed finite skeleton of a limit hypercover is a base change from a full
finite split hypercover at a stage. Source: blueprint finite hypercover descent,
followed by the split extension construction of Stacks 0DAV. Truncate the given
hypercover, descend that finite data, and extend the descended skeleton. Forgetting
matching and splitting choices gives the asserted isomorphism of simplicial diagrams.
(auxiliary; not a blueprint node) -/
theorem exists_stage_hypercover_truncation
    {I : Type u} [SmallCategory I] [IsFiltered I] (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) [CompactSpace c.pt] [QuasiSeparatedSpace c.pt] (hc : IsLimit c)
    (r : ℕ) (U : FiniteSplitEtaleHypercover c.pt) :
    ∃ (i : Iᵒᵖ) (V : FiniteSplitEtaleHypercover (D.obj i)),
      Nonempty ((SimplicialObject.truncation r).obj
        (V.baseChange (show c.pt ⟶ D.obj i from c.π.app i)).simplicial ≅
        (SimplicialObject.truncation r).obj U.simplicial) := by
  obtain ⟨i, Ui, hUi, _⟩ :=
    finite_hypercover_descent_objects D c hc r (U.finiteTruncation r)
  obtain ⟨V, ⟨hV⟩⟩ := exists_extension_of_finite_skeleton r Ui
  obtain ⟨e, _⟩ := hUi
  let e' : ((SimplicialObject.truncation r).obj
      (V.baseChange (show c.pt ⟶ D.obj i from c.π.app i)).simplicial ⋙
      Scheme.Etale.forget c.pt) ≅
      ((SimplicialObject.truncation r).obj U.simplicial ⋙ Scheme.Etale.forget c.pt) :=
    Functor.isoWhiskerRight hV
      (Scheme.Etale.forget (D.obj i) ⋙ Over.pullback (c.π.app i)) ≪≫ e
  refine ⟨i, V, ⟨NatIso.ofComponents
    (fun Δ ↦ (Scheme.Etale.forget c.pt).preimageIso (e'.app Δ)) ?_⟩⟩
  intro Δ Δ' α
  apply (Scheme.Etale.forget c.pt).map_injective
  simpa using e'.hom.naturality α

end AlgebraicGeometry.FiniteSplitEtaleHypercover
