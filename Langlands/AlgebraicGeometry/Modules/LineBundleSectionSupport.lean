import Langlands.AlgebraicGeometry.Modules.LineBundleSectionNilpotence
import Langlands.AlgebraicGeometry.Modules.PullbackTensorUnitProofs
import Langlands.AlgebraicGeometry.Modules.PositiveSectionPowerGenerationLocusProof
import Langlands.AlgebraicGeometry.Picard.ClosedImmersionPullbackAmpleProof
import Langlands.AlgebraicGeometry.Picard.LineBundleSectionVanishingProof
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Positive powers supported away from a closed complement -/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Langlands.Scheme.Modules Langlands.AlgebraicGeometry.Picard

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.SchemeModule

variable {X Y : Scheme.{u}}

/-- The tensor comparison carries the pulled-back product section to the product
of the two pulled-back sections. -/
lemma pullback_tensorSection (f : Y ⟶ X) (M N : X.Modules)
    (s : GlobalSections M) (t : GlobalSections N) :
    (pullbackTensorComparisonApp f M N).app ⊤
        (pullbackSection f (tensorObj M N) (tensorSection M N s t)) =
      tensorSection ((Scheme.Modules.pullback f).obj M)
        ((Scheme.Modules.pullback f).obj N)
        (pullbackSection f M s) (pullbackSection f N t) := by
  let P := Scheme.Modules.pullback f
  let e := pullbackUnitIso f
  have hunit : e.inv ≫ P.map (tensorLeftUnitor (structureSheaf X)).inv ≫
        pullbackTensorComparisonApp f (structureSheaf X) (structureSheaf X) =
      (tensorLeftUnitor (structureSheaf Y)).inv ≫ tensorMap e.inv e.inv := by
    have : IsIso (tensorMap e.hom e.hom) :=
      inferInstanceAs (IsIso ((tensorFunctor Y).mapIso (e.prod e)).hom)
    apply (cancel_mono (tensorMap e.hom e.hom ≫
      (tensorLeftUnitor (structureSheaf Y)).hom)).mp
    have hfactor : tensorMap e.hom e.hom =
        tensorMap e.hom (𝟙 _) ≫ tensorMap (𝟙 _) e.hom := by
      rw [tensorMap_comp, Category.comp_id, Category.id_comp]
    have hu := pullbackTensorLeftUnitor Y X f (structureSheaf X)
    change pullbackTensorComparisonApp f (structureSheaf X) (structureSheaf X) ≫
      tensorMap e.hom (𝟙 _) ≫ (tensorLeftUnitor (P.obj (structureSheaf X))).hom =
        P.map (tensorLeftUnitor (structureSheaf X)).hom at hu
    have hl : (e.inv ≫ P.map (tensorLeftUnitor (structureSheaf X)).inv ≫
          pullbackTensorComparisonApp f (structureSheaf X) (structureSheaf X)) ≫
        (tensorMap e.hom e.hom ≫ (tensorLeftUnitor (structureSheaf Y)).hom) = 𝟙 _ := by
      calc
        _ = e.inv ≫ P.map (tensorLeftUnitor (structureSheaf X)).inv ≫
            (pullbackTensorComparisonApp f (structureSheaf X) (structureSheaf X) ≫
              tensorMap e.hom (𝟙 _) ≫
                (tensorLeftUnitor (P.obj (structureSheaf X))).hom) ≫ e.hom := by
          rw [hfactor]
          simp only [Category.assoc]
          erw [tensorLeftUnitor_naturality (X := Y) e.hom]
          rfl
        _ = e.inv ≫ P.map (tensorLeftUnitor (structureSheaf X)).inv ≫
            P.map (tensorLeftUnitor (structureSheaf X)).hom ≫ e.hom := by rw [hu]
        _ = 𝟙 _ := by
          rw [← Functor.map_comp_assoc]
          simp
    rw [hl]
    symm
    calc
      _ = (tensorLeftUnitor (structureSheaf Y)).inv ≫
          (tensorMap e.inv e.inv ≫ tensorMap e.hom e.hom) ≫
            (tensorLeftUnitor (structureSheaf Y)).hom := by simp only [Category.assoc]
      _ = 𝟙 _ := by rw [tensorMap_comp]; simp
  apply sectionHom_injective
  rw [sectionHom_naturality, sectionHom_tensorSection, sectionHom_pullbackSection,
    sectionHom_pullbackSection, sectionHom_pullbackSection]
  simp only [pullbackSectionHom, Category.assoc]
  rw [sectionHom_tensorSection, Functor.map_comp]
  simp only [Category.assoc]
  have hnat := (pullbackTensorComparison f).naturality
    (X := (structureSheaf X, structureSheaf X)) (Y := (M, N))
    (sectionHom M s, sectionHom N t)
  change P.map (tensorMap (sectionHom M s) (sectionHom N t)) ≫
      pullbackTensorComparisonApp f M N =
    pullbackTensorComparisonApp f (structureSheaf X) (structureSheaf X) ≫
      tensorMap (P.map (sectionHom M s)) (P.map (sectionHom N t)) at hnat
  rw [hnat]
  have h := congrArg (fun k => k ≫
    tensorMap (P.map (sectionHom M s)) (P.map (sectionHom N t))) hunit
  simpa only [Category.assoc, tensorMap_comp] using h

/-- The canonical power comparison respects the actual power of a section. -/
lemma actualPullbackTensorPowIso_sectionPow (f : Y ⟶ X) (M : X.Modules)
    (s : GlobalSections M) (n : ℕ) :
    (actualPullbackTensorPowIso f M n).hom.app ⊤
        (pullbackSection f (tensorPow M n) (sectionPow M s n)) =
      sectionPow ((Scheme.Modules.pullback f).obj M) (pullbackSection f M s) n := by
  induction n with
  | zero =>
    apply sectionHom_injective
    rw [sectionHom_naturality, sectionHom_pullbackSection]
    simp only [pullbackSectionHom, sectionHom_sectionPow_zero, actualPullbackTensorPowIso]
    change ((pullbackUnitIso f).inv ≫
      (Scheme.Modules.pullback f).map (𝟙 (structureSheaf X))) ≫
        (pullbackUnitIso f).hom = 𝟙 (structureSheaf Y)
    erw [(Scheme.Modules.pullback f).map_id (structureSheaf X)]
    erw [Category.comp_id, Iso.inv_hom_id]
    rfl
  | succ n ih =>
    change (tensorMap (𝟙 _) (actualPullbackTensorPowIso f M n).hom).app ⊤
      ((pullbackTensorComparisonApp f M (tensorPow M n)).app ⊤
        (pullbackSection f (tensorObj M (tensorPow M n))
          (tensorSection M (tensorPow M n) s (sectionPow M s n)))) = _
    rw [pullback_tensorSection, tensorSection_naturality, ih]
    rfl

/-- An empty pulled-back generation open gives a positive power vanishing after
pullback, including over nonreduced source schemes. -/
theorem exists_pos_pullback_sectionPow_eq_zero (f : Y ⟶ X) [CompactSpace Y]
    (L : LineBundle X) (s : GlobalSections L.obj)
    (hs : f ⁻¹ᵁ trivializationOpen L.obj s = ⊥) :
    ∃ n : ℕ, 1 ≤ n ∧
      pullbackSection f (tensorPow L.obj n) (sectionPow L.obj s n) = 0 := by
  let L' := (LineBundle.pullback f).obj L
  have hs' : trivializationOpen L'.obj (pullbackSection f L.obj s) = ⊥ :=
    (lineBundlePullbackSectionOpen X Y f L s).trans hs
  obtain ⟨n, hn, hz⟩ :=
    exists_pos_sectionPow_eq_zero_of_trivializationOpen_eq_bot Y L' _ hs'
  refine ⟨n, hn, ?_⟩
  have h0 := (actualPullbackTensorPowIso_sectionPow f L.obj s n).trans hz
  rw [← sectionHom_eq_zero_iff, sectionHom_naturality, comp_eq_zero_iff_of_mono,
    sectionHom_eq_zero_iff] at h0
  exact h0

/-- The reduced closed subscheme complementary to an open subscheme. -/
def closedComplement (U : X.Opens) : Scheme.{u} :=
  (Scheme.IdealSheafData.vanishingIdeal U.compl).subscheme

/-- The canonical closed immersion of the complement. -/
def closedComplementι (U : X.Opens) : closedComplement U ⟶ X :=
  (Scheme.IdealSheafData.vanishingIdeal U.compl).subschemeι

instance (U : X.Opens) : IsClosedImmersion (closedComplementι U) :=
  inferInstanceAs (IsClosedImmersion
    (Scheme.IdealSheafData.vanishingIdeal U.compl).subschemeι)

instance (U : X.Opens) [CompactSpace X] : CompactSpace (closedComplement U) :=
  QuasiCompact.compactSpace_of_compactSpace (closedComplementι U)

/-- The complement's underlying set is the actual set-theoretic complement. -/
lemma range_closedComplementι (U : X.Opens) :
    Set.range (closedComplementι U) = (U : Set X)ᶜ := by
  change Set.range (Scheme.IdealSheafData.vanishingIdeal U.compl).subschemeι = _
  rw [Scheme.IdealSheafData.range_subschemeι,
    Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

/-- Vanishing on the closed complement forces the whole generation open inside U. -/
lemma trivializationOpen_le_of_closedComplement_vanishing (U : X.Opens)
    (L : LineBundle X) (s : GlobalSections L.obj)
    (hs : pullbackSection (closedComplementι U) L.obj s = 0) :
    trivializationOpen L.obj s ≤ U := by
  intro x hx
  by_contra hxU
  have hxZ : x ∈ Set.range (closedComplementι U) := by
    rw [range_closedComplementι]
    exact hxU
  obtain ⟨z, rfl⟩ := hxZ
  exact not_mem_of_vanishesAlong (L := L) hs z hx

/-- A section supported in U has empty generation open on its closed complement. -/
lemma closedComplement_preimage_trivializationOpen_eq_bot (U : X.Opens)
    (L : LineBundle X) (s : GlobalSections L.obj)
    (hs : trivializationOpen L.obj s ≤ U) :
    (closedComplementι U) ⁻¹ᵁ trivializationOpen L.obj s = ⊥ := by
  apply bot_unique
  intro z hz
  have hzZ : closedComplementι U z ∈ (U : Set X)ᶜ := by
    rw [← range_closedComplementι]
    exact ⟨z, rfl⟩
  exact (hzZ (hs hz)).elim

/-- On a quasi-compact scheme, a section supported in U has a positive power
vanishing along the reduced closed complement of U. -/
theorem exists_pos_sectionPow_closedComplement_eq_zero [CompactSpace X]
    (U : X.Opens) (L : LineBundle X) (s : GlobalSections L.obj)
    (hs : trivializationOpen L.obj s ≤ U) :
    ∃ n : ℕ, 1 ≤ n ∧ pullbackSection (closedComplementι U) (tensorPow L.obj n)
      (sectionPow L.obj s n) = 0 :=
  exists_pos_pullback_sectionPow_eq_zero (closedComplementι U) L s
    (closedComplement_preimage_trivializationOpen_eq_bot U L s hs)

end Langlands.SchemeModule
