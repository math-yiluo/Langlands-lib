import Langlands.GroupScheme.Rational.LeviRadicalCentrality
import Langlands.GroupScheme.Rational.SplitTorusImageDominant
import Langlands.GroupScheme.Rational.MaximalTorusFiniteType
import Langlands.GroupScheme.Rational.TorusCentralizerFactorization
import Langlands.GroupScheme.Rational.ParabolicRadicalTorusCentralizerLeviReduction

/-! # An initial radical torus from the dynamic rational Levi -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section InitialTorus

variable {k : Type u} [Field k]
  {G P L R : GroupScheme (Spec (CommRingCat.of k))}
  {j : P ⟶ G} {l : L ⟶ P} {r : R ⟶ P}

/-- A rational Levi that represents a cocharacter centralizer is the whole
ambient centralizer of some maximal torus of the specified solvable radical. -/
theorem IsRationalLeviSubgroup.exists_maximalTorus_radical_centralizer
    (hl : IsRationalLeviSubgroup l) (hj : IsClosedSubgroup j)
    (hr : IsSolvableRadical r)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hZ : (Dynamic.centralizer χ).IsRepresentedBy (l ≫ j)) :
    ∃ (S : CommGroupScheme (Spec (CommRingCat.of k))) (s : S.toGrp ⟶ R),
      IsMaximalTorus s ∧
      (torusCentralizer (s ≫ r ≫ j)).IsRepresentedBy (l ≫ j) := by
  let : IsAffineHom P.X.hom := hl.isAffineHom
  let : IsAffineHom L.X.hom := hl.isConnectedReductive.isAffineHom
  let : IsClosedImmersion r.hom.hom.left := hr.isClosedSubgroup
  let : IsAffineHom R.X.hom := by
    rw [← Over.w r.hom.hom]
    infer_instance
  let : Smooth R.X.hom := hr.smooth
  let : IsClosedImmersion j.hom.hom.left := hj
  have hjrep : (SubgroupFunctor.range j).IsRepresentedBy j :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  have hZtor : (torusCentralizer χ).IsRepresentedBy (l ≫ j) := by
    rwa [torusCentralizer_gm_eq_dynamicCentralizer]
  let χL := torusCentralizerFactor χ hZtor
  have hχL : χL ≫ (l ≫ j) = χ := torusCentralizerFactor_comp χ hZtor
  have hcχL : IsCentral χL := isCentral_torusCentralizerFactor χ hZtor
  let d := isSplitTorus_gm.dominantFactorization χL
  have hdc : IsCentral d.inclusion := d.central hcχL
  let aR := hl.centralTorusRadicalFactor d.inclusion hr d.isSplitSubtorus.1.isTorus
    d.isSplitSubtorus.2 hdc
  have haR : aR ≫ r = d.inclusion ≫ l :=
    hl.centralTorusRadicalFactor_comp d.inclusion hr d.isSplitSubtorus.1.isTorus
      d.isSplitSubtorus.2 hdc
  have haRc : IsClosedSubgroup aR :=
    hl.isClosedSubgroup_centralTorusRadicalFactor d.inclusion hr d.isSplitSubtorus.1.isTorus
      d.isSplitSubtorus.2 hdc
  obtain ⟨S, s, hs, f, hf⟩ := exists_maximalTorus_extension_of_finiteType R aR
    d.isSplitSubtorus.1.isTorus haRc
  let ν := d.factor ≫ f
  let sG := s ≫ r ≫ j
  have hν : ν ≫ sG = χ := by
    calc
      ν ≫ sG = d.factor ≫ ((f ≫ s) ≫ r) ≫ j := by
        simp only [ν, sG, Category.assoc]
      _ = d.factor ≫ (aR ≫ r) ≫ j := by rw [hf]
      _ = d.factor ≫ (d.inclusion ≫ l) ≫ j := by rw [haR]
      _ = (d.factor ≫ d.inclusion) ≫ (l ≫ j) := by simp only [Category.assoc]
      _ = χ := by rw [d.factor_comp, hχL]
  have hZS : (Dynamic.centralizer (ν ≫ sG)).IsRepresentedBy (l ≫ j) := by
    rwa [hν]
  let sL := Dynamic.torusFactor sG ν hZS
  have hsLg : sL ≫ (l ≫ j) = sG := Dynamic.torusFactor_comp sG ν hZS
  have hsL : sL ≫ l = s ≫ r := by
    apply hjrep.hom_ext
    simpa only [sG, Category.assoc] using hsLg
  have hcsL : IsCentral sL := hl.isCentral_of_factor_solvableRadical hr s sL hsL
  refine ⟨S, s, hs, hZ.1, le_antisymm ?_ ?_⟩
  · intro U x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    intro V a t
    have hc := (commute_of_mem_center (hcsL V t) (a ≫ y)).symm
    have he := congrArg (fun w : V ⟶ L.X => w ≫ (l ≫ j).hom.hom) hc.eq
    change Commute (a ≫ (y ≫ (l ≫ j).hom.hom)) (t ≫ sG.hom.hom)
    rw [← hsLg]
    apply (commute_iff_eq _ _).mpr
    simpa only [Grp.comp_hom_hom, MonObj.mul_comp, Category.assoc] using he
  · have hle := torusCentralizer_le_dynamicCentralizer sG ν
    rw [hν] at hle
    exact hle.trans hZ.2.ge

end InitialTorus

/-- The two exact dynamic structural statements construct one suitable maximal
torus of each supplied geometric solvable radical. -/
def ParabolicRadicalTorusInitialLeviFromDynamicStatement : Prop :=
  ParabolicDynamicStatement.{u} → DynamicCentralizerReductiveStatement.{u} →
    ParabolicRadicalTorusInitialCentralizerLeviStatement.{u}

theorem parabolicRadicalTorusInitialLevi_of_dynamic :
    ParabolicRadicalTorusInitialLeviFromDynamicStatement.{u} := by
  intro hPD hCR k _ G hG P j hj R r hr
  obtain ⟨χ, hχ⟩ := (hPD k G hG P j hj.isClosedSubgroup).mp hj
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsClosedImmersion j.hom.hom.left := hj.isClosedSubgroup
  have hP : (Dynamic.parabolic χ).IsRepresentedBy j := ⟨Over.mono_of_mono_left _, hχ⟩
  have hZ := Dynamic.Affine.isRepresentedBy_centralizerHom χ
  have hU := Dynamic.Affine.isRepresentedBy_unipotentHom χ
  let l := hP.factorHom (Dynamic.Affine.centralizerHom χ)
    (by rw [hZ.2]; exact Dynamic.centralizer_le_parabolic χ)
  let u := hP.factorHom (Dynamic.Affine.unipotentHom χ)
    (by rw [hU.2]; exact Dynamic.unipotent_le_parabolic χ)
  have hl : l ≫ j = Dynamic.Affine.centralizerHom χ := hP.factorHom_comp _ _
  have hu : u ≫ j = Dynamic.Affine.unipotentHom χ := hP.factorHom_comp _ _
  have hZred := hCR k G hG χ _ (Dynamic.Affine.centralizerHom χ)
    (Dynamic.Affine.isClosedSubgroup_centralizerHom χ) hZ
  have hrad := Dynamic.isGeometricUnipotentRadical_of_centralizer χ
    (Dynamic.Affine.centralizerHom χ) j u hP (by rw [hu]; exact hU) hZ hZred
  have hlevi := Dynamic.isRationalLeviSubgroup_of_geometricUnipotentRadical hP hZ hU l u hl hu
    hZred hrad
  obtain ⟨S, s, hs, hcentralizer⟩ := hlevi.exists_maximalTorus_radical_centralizer
    hj.isClosedSubgroup hr.1 χ (by rwa [hl])
  exact ⟨S, s, hs, _, l, hlevi, hcentralizer⟩

/-- The exact supplied-torus target reduces to three separately owned exact
structural statements, without changing that target or its hypotheses. -/
def ParabolicRadicalTorusCentralizerLeviFromDynamicStatement : Prop :=
  ParabolicDynamicStatement.{u} → DynamicCentralizerReductiveStatement.{u} →
    SolvableMaximalTorusConjugacyStatement.{u} →
      ParabolicRadicalTorusCentralizerLeviStatement.{u}

theorem parabolicRadicalTorusCentralizerLevi_of_dynamic :
    ParabolicRadicalTorusCentralizerLeviFromDynamicStatement.{u} := by
  intro hPD hCR hconj
  exact parabolicRadicalTorusCentralizerLevi_of_initial_torus hconj
    (parabolicRadicalTorusInitialLevi_of_dynamic hPD hCR)

end Langlands.GroupScheme
