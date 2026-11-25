/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageClassCompatibility
import all WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImagePresheaf

/-! # Local derived representatives of homology sections

Source: Stacks Project, Tags 072W and 03Q8.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Every homology section locally comes from a derived section of the free
abelian sheaf. The comparison is specified by homology and the identity generator.
Source: Stacks Project, Tags 072W and 03Q8.
(blueprint: lem-sc-abelian-derived-homology-sections).

Proof: Shift K by q and use a bounded-below injective representative. Its zeroth
homology is the sheaf cokernel of boundaries in cycles. Locally a homology section
lifts to a cycle. The free abelian sheaf of that neighborhood corepresents its
sections, so the cycle gives a chain map from its degree-zero single complex.
The image of this map in the derived category induces the original homology
section. The canonical shift comparison identifies that zeroth homology with
H^q(K). Thus the derived-section map is locally surjective. This includes the
zero object, empty test schemes, and all integer degrees. -/
theorem exists_abelianDerivedHomology_sections_comparison (S : Scheme.{u}) (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    ∃ τ : (abelianComparisonFree S ⋙ DerivedCategory.Plus.singleFunctor _ 0).op ⋙
        preadditiveYoneda.obj (K⟦q⟧) ⟶
          ((DerivedCategory.Plus.homologyFunctor _ q).obj K).obj,
      Presheaf.IsLocallySurjective S.smallEtaleTopology τ ∧
      ∀ (U : S.Etale) (z : (DerivedCategory.Plus.singleFunctor _ 0).obj
          ((abelianComparisonFree S).obj U) ⟶ K⟦q⟧),
        τ.app (op U) z =
          (((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app _ ≫
            (DerivedCategory.Plus.homologyFunctor _ 0).map z ≫
            ((DerivedCategory.Plus.homologyFunctor _ 0).shiftIso q 0 q
              (add_zero q)).hom.app K).hom.app (op U))
            (((toSheafify S.smallEtaleTopology
              (uliftYoneda.{u + 1}.obj U ⋙ AddCommGrpCat.free)).app (op U))
                (FreeAbelianGroup.of (ULift.up (𝟙 U)))) := by
  have : PreservesLimitsOfSize.{u, u + 1} (forget AddCommGrpCat.{u + 1}) :=
    preservesLimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
  have := (AbelianComparison.isLocallyBijective_derivedHomToHomology
    (J := S.smallEtaleTopology) (K⟦q⟧)).2
  let e := ((DerivedCategory.Plus.homologyFunctor
    (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).shiftIso q 0 q
      (add_zero q)).app K
  have : IsIso e.hom.hom :=
    (sheafToPresheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).map_isIso e.hom
  let τ := (AbelianComparison.derivedHomToHomology (K⟦q⟧) ≫
    AbelianComparison.freeSheafSections _) ≫ e.hom.hom
  refine ⟨τ, ?_, ?_⟩
  · dsimp only [τ]
    infer_instance
  · intro U z
    rfl

end AlgebraicGeometry.Etale
