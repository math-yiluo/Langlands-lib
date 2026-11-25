/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.Perfect.IntegralPerfectStratumPieces
public import WeilConjectures.CategoryTheory.RingedHomUniverses.RingedInternalHomShiftOfUniversesSupplement
import all WeilConjectures.CategoryTheory.Ringed.Site.RingedSitePerfectDuality
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.AlgebraicGeometry.Integral.IntegralLocallyPerfectDuality
import WeilConjectures.AlgebraicGeometry.Integral.IntegralClosedHomCoproducts
import WeilConjectures.AlgebraicGeometry.Integral.IntegralOpenHomPushforward
import WeilConjectures.AlgebraicGeometry.Integral.Perfect.IntegralPerfectStratumBounds
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleIntegralDirectImageCoproducts
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleInternalHomLowerBound
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Coproduct continuity for one locally perfect support piece

## References

* Bhatt--Scholze, Lemma 6.3.14(1)--(4), including its closed-stratum argument
* Bhatt--Scholze, Lemma 6.3.14(1)--(4), final paragraph
-/

@[expose] public noncomputable section
set_option autoImplicit false

attribute [-instance] CategoryTheory.flatConstantModulesAbelian
  AlgebraicGeometry.ProEtale.surjectiveTower_wEqualsLocallyBijective

set_option synthInstance.maxSize 4096
universe u c v r w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace CategoryTheory

-- The duality comparison elaborates the chosen closed and symmetric tensor structures.
private theorem perfectHom_preservesColimits
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r})
    [HasDerivedCategory.{w} (RingedHomUniverses.Modules.{c, v, r} J R)]
    (P : RingedHomUniverses.D.{c, v, r, w} J R)
    (hP : SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{c, v, r, w} R P) :
    PreservesColimitsOfSize.{max c v r, max c v r}
      (RingedHomUniverses.hom.{c, v, r, w} J R P) := by
  obtain ⟨M, _, _, h⟩ := ringedSitePerfectDuality.{c, v, r, w} J R P hP
  let D := (derivedInternalHomOfUniverses.{c, v, r, w} J R).obj
    (op P, ringedSiteDualityUnit.{c, v, r, w} J R)
  let := M.closed.monoidal
  let := M.symmetric
  have : PreservesColimitsOfSize.{max c v r, max c v r}
      (MonoidalCategory.tensorRight D) :=
    (M.closed.adjunction D).leftAdjoint_preservesColimits
  let e : MonoidalCategory.tensorRight D ≅ MonoidalCategory.tensorLeft D :=
    (BraidedCategory.tensorLeftIsoTensorRight D).symm
  have : PreservesColimitsOfSize.{max c v r, max c v r}
      (MonoidalCategory.tensorLeft D) := preservesColimits_of_natIso e
  let e' : MonoidalCategory.tensorLeft D ≅ Prod.sectR D _ ⋙ M.closed.tensor :=
    NatIso.ofComponents (fun N ↦ Iso.refl _) (by
      intro N N' f
      change D ◁ f ≫ 𝟙 _ = 𝟙 _ ≫ (𝟙 D ⊗ₘ f)
      simp only [Category.comp_id, Category.id_comp]
      exact (MonoidalCategory.id_tensorHom D f).symm)
  have : PreservesColimitsOfSize.{max c v r, max c v r}
      (Prod.sectR D _ ⋙ M.closed.tensor) := preservesColimits_of_natIso e'
  have := h
  exact preservesColimits_of_natIso
    (asIso (ringedSiteDualEvaluationLeftNatTrans M.closed M.symmetric
      (ringedSiteDualityUnit.{c, v, r, w} J R) M.unitIso P))

end CategoryTheory

namespace AlgebraicGeometry.Scheme

-- The unbounded derived comparisons require elaborating several functor structures.
/-- Internal Hom from one locally perfect support piece commutes with uniformly
bounded-below derived coproducts. The support is one closed subscheme of one open subscheme. -/
theorem integralPerfectStratumPiece_coproductContinuous
    (T : Scheme.{u}) [IsNoetherian T]
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K : DerivedCategory (pbcModules T (pbcAdicCompletion T d)))
    (hK : IsIntegralPerfectStratumPiece T d K) :
    ∀ (I : Type (u + 1))
      (M : I → DerivedCategory (pbcModules T (pbcAdicCompletion T d))) (b : ℤ),
      (∀ i, (M i).IsGE b) → PreservesColimit (Discrete.functor M)
        (CategoryTheory.RingedHomUniverses.hom.{u + 1, u, u + 1}
          (ProEt.topology T) (pbcAdicCompletion T d) K) := by
  classical
  obtain ⟨c, hc⟩ := integralPerfectStratumPiece_boundedAbove T d K hK
  have := hc
  obtain ⟨U, Z, j, hj, i, hi, L, hL, ⟨e⟩⟩ := hK
  have := hj
  have := hi
  let : TopologicalSpace.NoetherianSpace U := j.isEmbedding.isInducing.noetherianSpace
  have : QuasiCompact j :=
    ⟨fun V _ _ ↦ @TopologicalSpace.NoetherianSpace.isCompact U _
      (inferInstance : TopologicalSpace.NoetherianSpace U) (j ⁻¹' V)⟩
  let P := (d.push i).obj L
  let F := proEtaleRingModulePullback j (d.completedRing T) (d.completedRing U)
    (d.integralRingIso j)
  let H := RingedHomUniverses.hom.{u + 1, u, u + 1}
    (ProEt.topology U) (pbcAdicCompletion U d) P
  have hp : SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u + 1, u, u + 1}
      (pbcAdicCompletion Z d) L := integralLocallyPerfect_sitePerfect Z d L hL
  have hH : PreservesColimitsOfSize.{u + 1, u + 1}
      (RingedHomUniverses.hom.{u + 1, u, u + 1}
        (ProEt.topology Z) (pbcAdicCompletion Z d) L) :=
    CategoryTheory.perfectHom_preservesColimits (ProEt.topology Z)
      (pbcAdicCompletion Z d) L hp
  have : (F.mapDerivedCategory.obj K).IsLE c := F.isLE_mapDerivedCategory_obj K c
  have := cbcOpenUnit_isIso d j
  let q : (d.pull j).obj K ≅ P :=
    (d.pull j).mapIso e ≪≫ (asIso ((cbcDerivedOpenAdjunction d j).unit.app P)).symm
  have : P.IsLE c := DerivedCategory.TStructure.t.isLE_of_iso q c
  intro I M b hM
  let N : I → DerivedCategory (pbcModules U (pbcAdicCompletion U d)) :=
    fun s ↦ (d.pull j).obj (M s)
  have hN (s : I) : (N s).IsGE b := by
    have := hM s
    exact F.isGE_mapDerivedCategory_obj (M s) b
  have : PreservesColimit (Discrete.functor N) H :=
    integralClosed_homPreservesCoproduct d i L hH I N b hN
  let qN : Discrete.functor N ≅ Discrete.functor M ⋙ d.pull j :=
    (Discrete.compNatIsoDiscrete M (d.pull j)).symm
  have : PreservesColimit (Discrete.functor M ⋙ d.pull j) H :=
    preservesColimit_of_iso_diagram H qN
  have : PreservesColimitsOfSize.{u + 1, u + 1} (d.pull j) :=
    (cbcPullPushAdjunction d j).leftAdjoint_preservesColimits
  let B : I → DerivedCategory (pbcModules U (pbcAdicCompletion U d)) :=
    fun s ↦ H.obj (N s)
  have hB (s : I) : (B s).IsGE (b - c) := by
    have := hN s
    exact proEtale_internalHom_isGE U (pbcAdicCompletion U d) P (N s) c b
  have : PreservesColimit (Discrete.functor B) (d.push j) :=
    proEtaleIntegralDirectImage_preservesCoproduct j (d.completedRing T)
      (d.completedRing U) (d.integralRingIso j) I B (b - c) hB
  let qB : (Discrete.functor M ⋙ d.pull j) ⋙ H ≅ Discrete.functor B :=
    Functor.isoWhiskerRight (Discrete.compNatIsoDiscrete M (d.pull j)) H ≪≫
      Discrete.compNatIsoDiscrete N H
  have : PreservesColimit ((Discrete.functor M ⋙ d.pull j) ⋙ H) (d.push j) :=
    preservesColimit_of_iso_diagram (d.push j) qB.symm
  have : PreservesColimit (Discrete.functor M) (d.pull j ⋙ H ⋙ d.push j) :=
    inferInstance
  obtain ⟨a⟩ := integralOpen_homPushforward d j P
  have : PreservesColimit (Discrete.functor M)
      (RingedHomUniverses.hom.{u + 1, u, u + 1}
        (ProEt.topology T) (pbcAdicCompletion T d) ((cbcJ d j).obj P)) :=
    preservesColimit_of_natIso (Discrete.functor M) a.symm
  exact preservesColimit_of_natIso (Discrete.functor M)
    ((Functor.curry.obj (derivedInternalHomOfUniverses.{u + 1, u, u + 1}
      (ProEt.topology T) (pbcAdicCompletion T d))).mapIso e.op)

end AlgebraicGeometry.Scheme
