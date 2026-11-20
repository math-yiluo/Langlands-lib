import Langlands.GroupScheme.HomScheme.AdicClosedSubgroupInheritance
import Langlands.GroupScheme.HomScheme.AffineFiberTorusCentralizer
import Langlands.GroupScheme.HomScheme.CentralAdmissibleArtinian
import Langlands.GroupScheme.HomScheme.CentralTorusSubgroupRepresentability
import Langlands.GroupScheme.HomScheme.ChartCoverTransport
import Langlands.GroupScheme.HomScheme.SmoothSubgroupEqualityOpen
import Langlands.GroupScheme.Rational.TorusCentralizerFactorization
import Langlands.GroupScheme.SubgroupFunctor.CentralizerBaseChange

/-! # Étale moduli of closed tori with a fixed centralizer -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.TorusSubgroupModuli

open SubgroupFunctor Langlands.AlgebraicGeometry.UnramifiedFunctor

variable {S : Scheme.{u}} {H G : GroupScheme S}

/-- A family is universal among actual closed tori whose centralizer is the
pullback of a given subgroup. -/
def IsUniversalWithFixedCentralizer (c : H ⟶ G) {M : Over S} {T : GroupScheme M.left}
    (j : T ⟶ (baseChange M.hom).obj G) : Prop :=
  ∀ (U : Over S) (F : SubgroupFunctor ((baseChange U.hom).obj G)), IsAdmissible F →
    F.centralizer = range ((baseChange U.hom).map c) →
      ∃! a : U ⟶ M, evaluate j a = F

private theorem range_le_centralizer_of_central {B : Scheme.{u}} {T C D : GroupScheme B}
    (j : T ⟶ C) (c : C ⟶ D) (hj : IsCentral j) : range c ≤ (range (j ≫ c)).centralizer := by
  intro U g hg
  obtain ⟨x, rfl⟩ := mem_range.mp hg
  apply mem_centralizer.mpr
  intro V a y hy
  obtain ⟨z, rfl⟩ := mem_range.mp hy
  have h := (commute_of_mem_center (hj V z) (a ≫ x)).symm.eq
  apply (commute_iff_eq _ _).mpr
  simpa only [Grp.comp_hom_hom, Category.assoc, MonObj.mul_comp] using
    congrArg (fun p => p ≫ c.hom.hom) h

private theorem centralizer_evaluate {M U : Over S} {T C : GroupScheme M.left}
    (j : T ⟶ (baseChange M.hom).obj G) (c : C ⟶ (baseChange M.hom).obj G)
    (hc : (range j).centralizer = range c) (a : U ⟶ M) :
    (evaluate j a).centralizer = range (familyHom c a) := by
  let B := baseChange a.left
  let e := Descent.pullbackComparison M.hom a.left U.hom a.w G
  have hr : (range (B.map j)).centralizer = range (B.map c) := by
    rw [range_baseChangeHom a.left j, range_baseChangeHom a.left c, ← centralizer_baseChange, hc]
  have he := congrArg (comap e.inv) (centralizer_range_eq_comap_of_iso (B.map j) e)
  rw [← comap_comp, Iso.inv_hom_id, comap_id, hr] at he
  change (range (B.map j ≫ e.hom)).centralizer = range (B.map c ≫ e.hom)
  exact he.symm.trans (range_comp_iso (B.map c) e).symm

set_option maxHeartbeats 1400000 in
/-- Restrict a central torus parametrization to the open on which the ambient
centralizer equals the prescribed subgroup, and recover every such torus. -/
theorem exists_etale_fixedCentralizerFamily_of_centralFamily
    {M : Over S} {T C : GroupScheme M.left}
    (c : H ⟶ G) (hc : IsClosedSubgroup c)
    (j : T ⟶ (baseChange M.hom).obj H) (hj : IsClosedSubgroup j)
    (hT : RelativeTorus.IsTorus T) (hcj : IsCentral j) (hu : IsCentralUniversal j) [Etale M.hom]
    (k : C ⟶ (baseChange M.hom).obj G) (hk : IsClosedSubgroup k)
    (hkr : (range (j ≫ (baseChange M.hom).map c)).centralizer = range k)
    [Smooth H.X.hom] [Smooth C.X.hom] [GeometricallyConnected C.X.hom] :
    ∃ (N : Over S) (L : GroupScheme N.left) (l : L ⟶ (baseChange N.hom).obj G),
      Etale N.hom ∧ IsClosedSubgroup l ∧ RelativeTorus.IsTorus L ∧
        (range l).centralizer = range ((baseChange N.hom).map c) ∧ IsUniversalWithFixedCentralizer c l := by
  let cM := (baseChange M.hom).map c
  let jG := j ≫ cM
  have hle : range cM ≤ range k := hkr ▸ range_le_centralizer_of_central j cM hcj
  have : Smooth ((baseChange M.hom).obj H).X.hom :=
    MorphismProperty.pullback_snd (P := @Smooth) _ _ inferInstance
  have hcm : IsClosedImmersion cM.hom.hom.left := hc.baseChange M.hom
  have hkm : IsClosedImmersion k.hom.hom.left := hk
  let W := rangeEqualityOpen cM k hle
  have hgood {U : Over S} (a : U ⟶ M) :
      (evaluate jG a).centralizer = range ((baseChange U.hom).map c) ↔
        Set.range a.left ⊆ (W : Set M.left) := by
    let B := baseChange a.left
    let e := Descent.pullbackComparison M.hom a.left U.hom a.w G
    have hr : range (B.map cM ≫ e.hom) = range ((baseChange U.hom).map c) := by
      rw [Descent.pullbackComparison_naturality M.hom a.left U.hom a.w c, range_iso_comp]
    rw [centralizer_evaluate jG k hkr a, ← hr]
    change range (B.map k ≫ e.hom) = range (B.map cM ≫ e.hom) ↔ _
    rw [range_comp_iso_eq_iff, eq_comm]
    exact range_eq_iff_range_subset_rangeEqualityOpen cM k hle a.left
  let N : Over S := Over.mk (W.ι ≫ M.hom)
  let d : N ⟶ M := Over.homMk W.ι rfl
  let l := familyHom jG d
  have hcl : IsClosedSubgroup l := isClosedSubgroup_familyHom _ (hj.comp hcm) d
  refine ⟨N, _, l, ?_, hcl, hT.baseChange d.left, (hgood d).mpr ?_, ?_⟩
  · change Etale (W.ι ≫ M.hom)
    infer_instance
  · exact (Scheme.Opens.range_ι W).le
  · intro U F hF hCF
    let r := admissibleRepresentative ⟨F, hF⟩
    let D := (baseChange U.hom).obj G
    let cU := (baseChange U.hom).map c
    have hcc : IsClosedImmersion cU.hom.hom.left := hc.baseChange U.hom
    let B := r.torus.commGroupScheme
    let t : B.toGrp ⟶ D := r.hom
    have hrep : (torusCentralizer t).IsRepresentedBy cU := by
      rw [torusCentralizer_eq_centralizer_range]
      change (range r.hom).centralizer.IsRepresentedBy cU
      rw [r.represents.2]
      exact ⟨Over.mono_of_mono_left _, hCF.symm⟩
    let p := torusCentralizerFactor t hrep
    have hp : p ≫ cU = r.hom := torusCentralizerFactor_comp t hrep
    obtain ⟨a, ha, hau⟩ := hu U (range p)
      (isAdmissible_range p (isClosedSubgroup_torusCentralizerFactor t hrep hcc r.closed) r.torus)
      ((isCentral_iff_range_le_center p).mp (isCentral_torusCentralizerFactor t hrep))
    have hcomp (b : U ⟶ M) : evaluate jG b = range (familyHom j b ≫ cU) := by
      change range (familyHom (j ≫ (baseChange M.hom).map c) b) = _
      rw [familyHom_postcomp]
    have haG : evaluate jG a = F := by
      rw [hcomp a]
      exact (range_postcomp_congr _ p cU ha).trans ((congrArg range hp).trans r.represents.2)
    have haW : Set.range a.left ⊆ Set.range W.ι := by
      rw [Scheme.Opens.range_ι]
      apply (hgood a).mp
      rw [haG, hCF]
    let aW := IsOpenImmersion.lift W.ι a.left haW
    have haWfac : aW ≫ W.ι = a.left := IsOpenImmersion.lift_fac _ _ _
    let e : U ⟶ N := Over.homMk aW (by
      change aW ≫ (W.ι ≫ M.hom) = U.hom
      rw [← Category.assoc, haWfac, a.w])
    have hde : e ≫ d = a := Over.OverMorphism.ext haWfac
    refine ⟨e, ?_, fun b hb => ?_⟩
    · change evaluate l e = F
      rw [evaluate_comp, hde, haG]
    · change evaluate l b = F at hb
      rw [evaluate_comp, hcomp (b ≫ d)] at hb
      have hb' : range (familyHom j (b ≫ d) ≫ cU) = range (p ≫ cU) := by
        rw [hb, hp, r.represents.2]
      have hm : Mono cU.hom.hom := hrep.1
      have heq : evaluate j (b ≫ d) = range p :=
        le_antisymm ((range_comp_le_iff_of_mono _ _ cU hm).mp hb'.le)
          ((range_comp_le_iff_of_mono _ _ cU hm).mp hb'.ge)
      have hbM : b ≫ d = a := hau _ heq
      have : Mono d.left := inferInstanceAs (Mono W.ι)
      have : Mono d := Over.mono_of_mono_left _
      exact (cancel_mono d).mp (hbM.trans hde.symm)

/-- A fixed smooth closed subgroup with geometrically connected fibres cuts
out an étale torus-subgroup parameter over the original base. -/
def EtaleFixedCentralizerTorusRepresentabilityStatement : Prop :=
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] (G H : GroupScheme S) [Smooth G.X.hom]
    [IsSeparated G.X.hom] [QuasiCompact G.X.hom] [GeometricallyConnected G.X.hom]
    [Smooth H.X.hom] [GeometricallyConnected H.X.hom],
    HasAffineResidueFibers G →
    (∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A]
      (a : Spec (CommRingCat.of A) ⟶ S), IsAffineHom ((baseChange a).obj G).X.hom) →
    AdicLimits (smallAdmissiblePresheaf G) →
    ∀ (c : H ⟶ G), IsClosedSubgroup c →
      ∃ (N : Over S) (L : GroupScheme N.left) (l : L ⟶ (baseChange N.hom).obj G),
        Etale N.hom ∧ IsClosedSubgroup l ∧ RelativeTorus.IsTorus L ∧
          (range l).centralizer = range ((baseChange N.hom).map c) ∧ IsUniversalWithFixedCentralizer c l

set_option maxHeartbeats 1400000 in
theorem etaleFixedCentralizerTorusRepresentability :
    EtaleFixedCentralizerTorusRepresentabilityStatement.{u} := by
  intro S _ G H _ _ _ _ _ _ hG hA hadic c hc
  have : IsClosedImmersion c.hom.hom.left := hc
  have : IsSeparated H.X.hom := by rw [← c.hom.hom.w]; infer_instance
  have : QuasiCompact H.X.hom := by rw [← c.hom.hom.w]; infer_instance
  have hArt : ArtinianNilpotentBijective (smallCentralAdmissiblePresheaf H) := by
    apply smallCentralAdmissiblePresheaf_artinianNilpotentBijective S H
    intro A _ _ _ f
    let c' := (baseChange f).map c
    have : IsClosedImmersion c'.hom.hom.left := hc.baseChange f
    have : IsAffineHom ((baseChange f).obj G).X.hom := hA A f
    rw [← c'.hom.hom.w]
    infer_instance
  obtain ⟨Y, q, T, j, _, het, hj, hT, hcent, hu⟩ := etaleCentralTorusSubgroupRepresentability
    S H (adicLimits_of_closedSubgroup c hc hadic) hArt
  let G' := (baseChange q).obj G
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian q
  have : IsSeparated G'.X.hom := MorphismProperty.pullback_snd (P := @IsSeparated) _ _ inferInstance
  have : QuasiCompact G'.X.hom := MorphismProperty.pullback_snd (P := @QuasiCompact) _ _ inferInstance
  have : Smooth G'.X.hom := MorphismProperty.pullback_snd (P := @Smooth) _ _ inferInstance
  have : GeometricallyConnected G'.X.hom :=
    MorphismProperty.pullback_snd (P := @GeometricallyConnected) _ _ inferInstance
  let B := hT.commGroupScheme
  let jG : B.toGrp ⟶ G' := j ≫ (baseChange q).map c
  let K := separatedRelativeTorusCentralizerModel jG hT
  have hA' (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A]
      (f : Spec (CommRingCat.of A) ⟶ Y) : IsAffineHom ((baseChange f).obj G').X.hom := by
    let e := (Grp.forget _).mapIso (Descent.pullbackComparison q f (f ≫ q) rfl G)
    have : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
    have : IsAffineHom ((baseChange (f ≫ q)).obj G).X.hom := hA A (f ≫ q)
    have he : e.hom.left ≫ ((baseChange (f ≫ q)).obj G).X.hom =
        ((baseChange f).obj G').X.hom := e.hom.w
    rw [← he]
    infer_instance
  have hGeom := affineFiberTorusCentralizerGeometry Y G'
    (HasAffineResidueFibers.baseChange hG q) hA' B jG hT
  have : Smooth K.group.X.hom := hGeom.1
  have : GeometricallyConnected K.group.X.hom := hGeom.2.2.2.2
  have hkr : (range jG).centralizer = range K.hom :=
    (torusCentralizer_eq_centralizer_range jG).symm.trans K.represents.2.symm
  have : Etale (Over.mk q).hom := het
  exact exists_etale_fixedCentralizerFamily_of_centralFamily c hc (M := Over.mk q)
    j hj hT hcent hu K.hom K.closed hkr

end Langlands.GroupScheme.TorusSubgroupModuli
