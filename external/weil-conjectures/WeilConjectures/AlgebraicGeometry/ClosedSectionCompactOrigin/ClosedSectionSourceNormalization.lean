/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClosedSectionCompactOrigin.ClosedSectionCompactOriginData

/-! # Source normalization for a closed section

Source: current blueprint rank-one Thom proof, Step 1, induced global morphism;
Stacks Tags 0F7B and 0F7J (blueprint: lem-pur-closed-section-source-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.ClosedSectionCompactOrigin

/-- The canonical compact-support comparison commutes with the prescribed source
identification for a closed section. This is only the source equation: it has no
class maps, target complexes, retained target comparison or bounded-below conclusion.

Source: blueprint thm-pur-rank-one-thom.proof.md, Step 1, induced global morphism;
Stacks Tags 0F7B and 0F7J
(blueprint: lem-pur-closed-section-source-normalization).

Proof: the section is proper and its direct images are exact on both sites, on the
pro-etale site using the quasi-compact complementary open. The proper and exact
single-complex identifications identify its compact-support comparison with the
ordinary direct-image counit mate. The constant-sheaf comparison and this mate give
the specified supported-constant gamma by adjunction naturality. Thus beta_s followed
by proClosedIso equals C(etaleClosedIso) followed by supportedComparison. Invert the
closed identifications in this square. Naturality of beta at the inverse etale
closed identification moves it past compact support along f. Change the retained
compactification c to the standing one by the canonical candidate comparison; its
naturality at beta_s and its defining fully faithful preimage square match the two
sites. The origin compositor is transported from the etale compositor through the
same beta, so its defining preimage equation pastes these two comparisons into the
comparison for s followed by f. Transport along hs identifies this with the comparison
for the identity; the specified identity comparison is transported through that same
beta and cancels it. What remains is C(etaleSigma) followed by chi_B, as asserted.
All comparisons are the specified maps: the standing compactification is not assumed
to be (id,s). B is separated of finite type over the base field through b, as in the
item, so B, X and the compactification ambient are Noetherian of finite type over k,
the setting of the cited identity-open and site-coherence comparisons. Empty schemes and
the identity section obey the same argument. -/
theorem closedSectionSourceNormalization
    (P : WeilConjectures.PurityFiniteSetting.{u}) {B X : Scheme.{u}}
    (b : B ⟶ Spec (.of P.field.k))
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    (f : X ⟶ B) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (s : B ⟶ X) [IsClosedImmersion s]
    [QuasiCompact s.openComplement.ι] (hs : s ≫ f = 𝟙 B) :
    (compactComparison P c (etaleSource P s)).hom ≫
        (ProEtale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} P.Coefficient) c).map (supportedComparison P s).hom ≫
        (proSigma P f c s hs).hom =
      (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory.map
          (DerivedCategory.Plus.ι.map (etaleSigma P f c s hs).hom) ≫
        (constantComparison P B).hom := by sorry

end AlgebraicGeometry.ClosedSectionCompactOrigin
