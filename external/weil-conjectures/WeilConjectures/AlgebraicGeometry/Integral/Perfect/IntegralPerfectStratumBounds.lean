/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.Perfect.IntegralPerfectStratumPieces
public import WeilConjectures.CategoryTheory.RingedHomUniverses.RingedInternalHomShiftOfUniversesSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleInternalHomLowerBound
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleIdentifiedOpenClosed
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

/-! # Upper bounds for one locally perfect support piece

## References

* Bhatt--Scholze, Lemma 6.3.14, exact open and closed extensions
* Bhatt--Scholze, Lemma 6.3.14 and Lemma 6.5.8
* Bhatt--Scholze, Lemma 6.3.14
* Stacks Tag 08JA
-/

@[expose] public noncomputable section
set_option autoImplicit false

attribute [-instance] CategoryTheory.flatConstantModulesAbelian
  AlgebraicGeometry.ProEtale.surjectiveTower_wEqualsLocallyBijective

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A support piece is bounded above. -/
theorem integralPerfectStratumPiece_boundedAbove
    (T : Scheme.{u}) [IsNoetherian T]
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K : DerivedCategory (pbcModules T (pbcAdicCompletion T d)))
    (hK : IsIntegralPerfectStratumPiece T d K) : ∃ b : ℤ, K.IsLE b := by
  obtain ⟨U, Z, j, hj, i, hi, L, hL, ⟨e⟩⟩ := hK
  have := hj
  have := hi
  let : TopologicalSpace.NoetherianSpace U := j.isEmbedding.isInducing.noetherianSpace
  let W : U.ProEt := ProEt.mk i.openComplement.ι
  have : IsOpenImmersion W.hom := inferInstanceAs (IsOpenImmersion i.openComplement.ι)
  let : TopologicalSpace.NoetherianSpace W.left :=
    inferInstanceAs (TopologicalSpace.NoetherianSpace (i.openComplement : Set U))
  have : QuasiCompact W.hom :=
    ⟨fun V _ _ ↦ @TopologicalSpace.NoetherianSpace.isCompact W.left _
      (inferInstance : TopologicalSpace.NoetherianSpace W.left) (W.hom ⁻¹' V)⟩
  have hW : Set.range W.hom = (Set.range i)ᶜ := by
    change Set.range i.openComplement.ι = (Set.range i)ᶜ
    rw [Scheme.Opens.range_ι, Scheme.Hom.coe_openComplement]
  obtain ⟨hlim, hcol, _⟩ := proEtaleIdentifiedOpenClosed i W hW
    (d.completedRing U) (d.completedRing Z) (d.completedRing W.left)
    (d.integralRingIso i) (d.integralRingIso W.hom)
  let F := proEtaleRingModuleDirectImage i (d.completedRing U) (d.completedRing Z)
    (d.integralRingIso i)
  have : PreservesFiniteLimits F := hlim
  have : PreservesFiniteColimits F := hcol
  obtain ⟨b, hb⟩ := hL.1
  have := hb
  have : (F.mapDerivedCategory.obj L).IsLE b := F.isLE_mapDerivedCategory_obj L b
  have : ((d.push i).obj L).IsLE b :=
    DerivedCategory.TStructure.t.isLE_of_iso
      (F.rightDerivedFunctorIsoMapDerivedCategory.app L).symm b
  have : ((cbcDerivedOpenShriek d j hj).obj ((d.push i).obj L)).IsLE b :=
    (cbcOpenShriek d j hj).isLE_mapDerivedCategory_obj _ b
  exact ⟨b, DerivedCategory.TStructure.t.isLE_of_iso e.symm b⟩

/-- One support piece supplies the uniform target-variable lower-bound offset. -/
theorem integralPerfectStratumPiece_hom_lowerBound
    (T : Scheme.{u}) [IsNoetherian T]
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K : DerivedCategory (pbcModules T (pbcAdicCompletion T d)))
    (hK : IsIntegralPerfectStratumPiece T d K) :
    ∃ c : ℤ, ∀ (b : ℤ)
      (N : DerivedCategory (pbcModules T (pbcAdicCompletion T d))),
      N.IsGE b → ((CategoryTheory.RingedHomUniverses.hom.{u + 1, u, u + 1}
        (ProEt.topology T) (pbcAdicCompletion T d) K).obj N).IsGE (b + c) := by
  obtain ⟨c, hc⟩ := integralPerfectStratumPiece_boundedAbove T d K hK
  have := hc
  refine ⟨-c, fun b N hN ↦ ?_⟩
  have := hN
  simpa only [CategoryTheory.RingedHomUniverses.hom, Functor.curry_obj_obj_obj,
    sub_eq_add_neg] using
    proEtale_internalHom_isGE T (pbcAdicCompletion T d) K N c b

end AlgebraicGeometry.Scheme
