/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GrothendieckHypercoverCohomology
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.AlgebraicGeometry.GrothendieckHypercoverBottomColimit
import WeilConjectures.AlgebraicGeometry.GrothendieckHypercoverZero
import Mathlib.CategoryTheory.Sites.GlobalSections

/-! # Hypercover comparison for Grothendieck abelian coefficients -/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.FiniteSplitEtaleHypercover

attribute [local instance] instHasColimitsOfSize

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]

/-- Finite split hypercovers compute the classical derived terminal-section functor.
Source: Stacks Project, Hypercoverings, Tag 01H0, first proof, with the same
argument in a Grothendieck abelian coefficient category.
(auxiliary; not a blueprint node).

Proof: use the explicit comparison cocone from the section bicomplex of an
injective resolution. Its injective-row acyclicity is proved by Gabriel--Popescu
and the existing arbitrary-ring module result. The bottom-row colimit theorem
makes the canonical colimit map an isomorphism. Transfer the colimit universal
property across that isomorphism. The canonical isomorphism between evaluation
at the chosen terminal object and evaluation at the identity object induces an
isomorphism of right-derived functors. Transport the cocone along this latter
isomorphism to obtain exactly the terminal-section functor in the statement. -/
theorem isCohomologyColimit_rightDerived_sections
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] (q : ℕ) :
    IsCohomologyColimit A q
      ((sheafToPresheaf X.smallEtaleTopology A ⋙
        (evaluation X.Etaleᵒᵖ A).obj
          (op (MorphismProperty.Over.mk ⊤ (𝟙 X)
            (MorphismProperty.id_mem _ X)))).rightDerived q) := by
  classical
  let T : X.Etale := MorphismProperty.Over.mk ⊤ (𝟙 X)
    (MorphismProperty.id_mem _ X)
  let E := sheafToPresheaf X.smallEtaleTopology A ⋙
    (evaluation X.Etaleᵒᵖ A).obj (op T)
  let e₀ : Grothendieck.terminalSections (X := X) A ≅ E :=
    (Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).symm ≪≫
      Sheaf.ΓNatIsoSheafSections _ _
        (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X)
  let e : (Grothendieck.terminalSections (X := X) A).rightDerived q ≅ E.rightDerived q :=
    { hom := NatTrans.rightDerived e₀.hom q
      inv := NatTrans.rightDerived e₀.inv q
      hom_inv_id := by
        rw [← NatTrans.rightDerived_comp, e₀.hom_inv_id, NatTrans.rightDerived_id]
      inv_hom_id := by
        rw [← NatTrans.rightDerived_comp, e₀.inv_hom_id, NatTrans.rightDerived_id] }
  let cc (U : FiniteSplitEtaleHypercover X) :=
    Grothendieck.canonicalComparison A U q ≫ e.hom
  refine ⟨fun U V f g h ↦ cohomologyRefinement_homotopy_invariant A q f g h,
    cc, ?_, ?_⟩
  · intro U V f
    dsimp [cc]
    rw [← Category.assoc, Grothendieck.canonicalComparison_refinement A f q]
  · intro F B d hd
    let C := Grothendieck.comparisonCocone A F q
    have : IsIso (colimit.desc (homotopyCohomologyDiagram A F q) C) := by
      cases q with
      | zero => exact Grothendieck.isIso_colimit_comparison_zero A F
      | succ q => exact Grothendieck.isIso_colimit_comparison_positive A F q
    have hC : IsColimit C :=
      IsColimit.ofIsoColimit (colimit.isColimit _)
        (Cocone.ext (asIso (colimit.desc _ C)) (fun U ↦ colimit.ι_desc C U))
    let C' := C.extend (e.hom.app F)
    have hC' : IsColimit C' :=
      IsColimit.ofIsoColimit hC (Cocone.ext (e.app F) (fun _ ↦ rfl))
    let s : Cocone (homotopyCohomologyDiagram A F q) :=
      { pt := B
        ι :=
          { app := fun U ↦ d U.as.unop
            naturality := by
              rintro ⟨U⟩ ⟨V⟩ f
              refine Quot.inductionOn f ?_
              intro f
              change (cohomologyRefinement A f.unop.hom q).app F ≫ d V.unop =
                d U.unop ≫ 𝟙 _
              simpa only [Category.comp_id] using hd V.unop U.unop f.unop.hom } }
    refine ⟨hC'.desc s, fun U ↦ hC'.fac s ⟨op U⟩, ?_⟩
    intro e he
    apply hC'.uniq s e
    intro U
    exact he U.as.unop

end AlgebraicGeometry.FiniteSplitEtaleHypercover
