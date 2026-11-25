/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Triangulated.Yoneda
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
import WeilConjectures.CategoryTheory.BrownCohomologicalRepresentabilityUniverseTransfer
import WeilConjectures.CategoryTheory.GrothendieckDerivedCompactLocalizationModel

/-! # Localization data preceding the Grothendieck Brown retract

Source: Stacks Project, Tag 0F5X, first paragraph.
-/

@[expose] public section

universe w uA vA vH

open CategoryTheory.Limits
open CategoryTheory.Pretriangulated.Opposite

namespace CategoryTheory

/-- Gabriel-Popescu localization followed by Brown representability on the module
category supplies a representation of the pullback of H.  Source: Stacks Project,
Tag 0F5X, `injectives-lemma-brown`, first paragraph, and Tag 0F5V.
(auxiliary; not a blueprint node)

Proof in words: choose a Gabriel-Popescu presentation by modules over the endomorphism
ring of a generator. Its exact localization induces L on derived categories, with
fully faithful derived right adjoint R and invertible counit. L is exact and preserves
coproducts, so H composed with L is cohomological and sends coproducts to products.
The free rank-one module is a compact generator of the module derived category.
Apply compact-generator Brown representability to obtain E and its natural Hom
bijections. Lift both sets to max(w,vH), obtaining the displayed isomorphism.
Use module complexes in the universe max(w,vH), so their Hom types and the
lifted H values share a universe. Lift the object universe, if necessary, to
max(uA,vA,max(w,vH)+1). The explicit larger coproduct hypothesis covers the
universe used in Brown's construction. No splitting of the unit
or retract in the target category is included in this assertion. -/
theorem grothendieckDerived_localization_brown_data
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{w} A]
    [HasCoproducts.{max w vA vH} (DerivedCategory A)]
    (H : (DerivedCategory A)ᵒᵖ ⥤ AddCommGrpCat.{vH}) [H.IsHomological]
    (hH : ∀ I : Type (max w vA vH), PreservesLimitsOfShape (Discrete I) H) :
    ∃ (B : Type (max uA vA ((max w vH) + 1))) (cB : Category.{max w vH} B),
      letI := cB
      ∃ (L : B ⥤ DerivedCategory A) (R : DerivedCategory A ⥤ B)
        (adj : L ⊣ R), IsIso adj.counit ∧
        ∃ E : B, Nonempty (uliftYoneda.{vH}.obj E ≅
          L.op ⋙ H ⋙ forget AddCommGrpCat ⋙ uliftFunctor.{w}) := by
  obtain ⟨B, cB, zB, sB, pB, aB, tB, iB, sumsB, hB, L, R, adj, sL, hL, hc⟩ :=
    grothendieckDerived_compact_localization_model.{w, uA, vA, vH} (A := A)
  let := cB
  let := zB
  let := sB
  let := pB
  let := aB
  let := tB
  let := iB
  let := sumsB
  let := sL
  have := hL
  let K := L.op ⋙ H
  have : K.IsHomological := by dsimp [K]; infer_instance
  have : L.IsLeftAdjoint := adj.isLeftAdjoint
  have hK : ∀ I : Type (max w vH), PreservesLimitsOfShape (Discrete I) K := by
    intro I
    have := hH (ULift.{max w vA vH} I)
    have : PreservesLimitsOfShape (Discrete I) H :=
      preservesLimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) H
    dsimp [K]
    infer_instance
  have hrep := brownCohomologicalRepresentabilityUniverseTransfer.{0} B hB K hK
  obtain ⟨E, ⟨rE⟩⟩ := hrep
  refine ⟨B, cB, L, R, adj, hc, E, ⟨?_⟩⟩
  exact (Functor.RepresentableBy.equivUliftYonedaIso _ E)
    (Functor.representableByUliftFunctorEquiv.symm rE)

end CategoryTheory
