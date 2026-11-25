/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonData
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonModuleCriteria
import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleConstructibleIso
import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonClassical

/-! Constructible pro-etale comparison: module equivalence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
/-- Restrict canonical inverse image to the constructible module subcategories.
Source: blueprint constructible-comparison-equivalence, part (1), Stacks Tag 09AK
(auxiliary; not a blueprint node).

Proof: the constructibility test lifts the canonical inverse image to the two full
subcategories. Ambient full faithfulness gives fullness and faithfulness there.
A constructible target is continuous by the finite-cover classicality argument;
classical descent supplies an etale antecedent and an isomorphism of its image
with the target. Constructibility is invariant under that isomorphism and reflected
by inverse image, so this antecedent belongs to the source full subcategory.
This proves essential surjectivity. The resulting equivalence uses this lifted
functor itself, so its forward-functor identification is reflexive. -/
theorem constructibleComparison_moduleEquivalence (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] [IsNoetherianRing A] :
    ∀ [CompactSpace X] [QuasiSeparatedSpace X],
      ∃ e : Scheme.CoefficientConstructibleEtaleModuleCategory.{u, v} X A ≌
          ObjectProperty.FullSubcategory
            (Scheme.IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf X A),
        Nonempty (e.functor ⋙
          ObjectProperty.ι
            (Scheme.IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf X A) ≅
            ObjectProperty.ι (Scheme.IsCoefficientConstructibleEtaleModule X A) ⋙
              constructibleComparisonPullback X A) := by
  intro _ _
  obtain ⟨hfull, hfaithful, horigin, htest⟩ := coefficientComparison_moduleCriteria X A
  have := hfull
  have := hfaithful
  let L := constructibleComparisonPullback X A
  let P : ObjectProperty (ConstantCompletion.Mod (ConstantCompletion.constant
      (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A)) :=
    Scheme.IsCoefficientConstructibleEtaleModule X A
  let Q : ObjectProperty (ConstantCompletion.Mod (ConstantCompletion.constant
      (Scheme.coefficientProEtaleModelTopology.{u, v} X) A)) :=
    Scheme.IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf X A
  let T : P.FullSubcategory ⥤ Q.FullSubcategory :=
    Q.lift (P.ι ⋙ L) (fun G ↦ (htest G.obj).mp G.property)
  have : T.Full := by dsimp [T]; infer_instance
  have : T.Faithful := by dsimp [T]; infer_instance
  have : T.EssSurj := by
    constructor
    intro F
    obtain ⟨G, ⟨e⟩⟩ := horigin F.obj (constructibleComparison_classical X A F.obj F.property)
    have hG : P G := (htest G).mpr (coefficientProEtale_constructible_of_iso X A e.symm F.property)
    exact ⟨⟨G, hG⟩, ⟨Q.isoMk e⟩⟩
  have : T.IsEquivalence := ⟨inferInstance, inferInstance, inferInstance⟩
  exact ⟨T.asEquivalence, ⟨Iso.refl _⟩⟩

end AlgebraicGeometry.ProEtale
