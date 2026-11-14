import Langlands.GroupScheme.RelativeLevi.TorusLeviOverlap
import Langlands.GroupScheme.RelativeLevi.UnipotentRadicalUniqueness
import Langlands.GroupScheme.RelativeLevi.DynamicProof

/-! # Prescribed-torus local Levi data from the proved dynamic theorem -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeLevi

/-- The dynamic Levi containing a commutative subgroup is unique, using
radical comparison only for this represented dynamic parabolic. -/
def torusDynamicLeviWitnessFromDynamic
    {S : Scheme.{u}} {G P : GroupScheme S} {T : CommGroupScheme S}
    (i : P ⟶ G) (t : T.toGrp ⟶ P) (nu : (Gm S).toGrp ⟶ T.toGrp)
    (hG : IsReductive G)
    (hP : (Dynamic.parabolic (nu ≫ t ≫ i)).IsRepresentedBy i) :
    TorusLeviWitness t := by
  apply Classical.choice
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : LocallyOfFinitePresentation G.X.hom := inferInstance
  let chi := nu ≫ t ≫ i
  obtain ⟨U, iU, _, _, hU⟩ := (dynamicBaseRepresentability S G chi).2.1
  obtain ⟨Z, iZ, _, _, hZ⟩ := (dynamicBaseRepresentability S G chi).2.2
  let l := Dynamic.centralizerToParabolic hP hZ
  have hlcomp : l ≫ i = iZ := Dynamic.centralizerToParabolic_comp hP hZ
  let r := hP.factorHom iU (hU.2.le.trans (Dynamic.unipotent_le_parabolic chi))
  have hrcomp : r ≫ i = iU := hP.factorHom_comp _ _
  have hd := dynamicRelativeLevi S G P U Z chi i iU iZ hG hP hU hZ
  have hr : IsRelativeUnipotentRadical r := hd.2.1 r hrcomp
  have hl : IsRelativeLeviSubgroup l := hd.2.2 l hlcomp
  let tau := Dynamic.torusFactor (t ≫ i) nu hZ
  have htau : tau ≫ l = t := hP.hom_ext (by
    rw [Category.assoc, hlcomp]
    exact Dynamic.torusFactor_comp (t ≫ i) nu hZ)
  refine ⟨⟨Z, l, hl, ?_, ?_⟩⟩
  · intro V x hx
    obtain ⟨a, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    refine SubgroupFunctor.mem_range.mpr ⟨a ≫ tau.hom.hom, ?_⟩
    rw [Category.assoc, ← Grp.comp_hom_hom, htau]
  · intro L' l' hl' hcontains
    let hrep : (SubgroupFunctor.range l').IsRepresentedBy l' :=
      ⟨hl'.isClosedSubgroup.mono_overHom, rfl⟩
    let tau' := hrep.factorHom t hcontains
    have htau' : tau' ≫ l' = t := hrep.factorHom_comp _ _
    obtain ⟨U', r', hr', hmul⟩ := hl'.exists_unipotentRadical
    let : IsIso (subgroupMultiplication l' r') := hmul
    let q := leviRetraction l' r' hr'.isNormal
    have hlq : l' ≫ q = 𝟙 L' := levi_comp_leviRetraction l' r' hr'.isNormal
    have hrr : SubgroupFunctor.range r' = SubgroupFunctor.range r :=
      radical_range_eq_of_dynamic_parabolic dynamicRelativeLevi hG chi hP r' r hr' hr
    have hker : ∀ (V : Over S) (x : V ⟶ P.X),
        x ≫ q.hom.hom = 1 ↔ x ≫ i.hom.hom ∈ (Dynamic.unipotent chi).carrier V := by
      intro V x
      rw [comp_leviRetraction_eq_one_iff, hrr, ← hU.2, ← hrcomp]
      constructor
      · intro hx
        obtain ⟨a, rfl⟩ := SubgroupFunctor.mem_range.mp hx
        exact SubgroupFunctor.mem_range.mpr
          ⟨a, by rw [Grp.comp_hom_hom, Category.assoc]⟩
      · intro hx
        obtain ⟨a, ha⟩ := SubgroupFunctor.mem_range.mp hx
        exact SubgroupFunctor.mem_range.mpr ⟨a, hP.1.right_cancellation _ _ (by
          simpa only [Grp.comp_hom_hom, Category.assoc] using ha)⟩
    have hmu : (nu ≫ tau') ≫ l' ≫ i = chi := by
      change (nu ≫ tau') ≫ l' ≫ i = nu ≫ t ≫ i
      simp only [Category.assoc]
      rw [← Category.assoc tau' l' i, htau']
    have heq := DynamicLeviConjugacy.range_eq_centralizer_of_cocharacter_factors
      chi hP l' q hlq hker (nu ≫ tau') hmu
    have hzl : SubgroupFunctor.range (l ≫ i) = Dynamic.centralizer chi := by
      rw [hlcomp]
      exact hZ.2
    have hamb := heq.trans hzl.symm
    exact le_antisymm
      ((SubgroupFunctor.range_comp_le_iff_of_mono l' l i hP.1).mp hamb.le)
      ((SubgroupFunctor.range_comp_le_iff_of_mono l l' i hP.1).mp hamb.ge)


namespace TorusDynamicPresentation

variable {S : Scheme.{u}} {G P : GroupScheme S} {T : CommGroupScheme S}
    {i : P ⟶ G} {t : T.toGrp ⟶ P}

/-- Construct the actual unique local Levi directly from the proved dynamics. -/
def witnessFromDynamic (d : TorusDynamicPresentation i t) (hG : IsReductive G) :
    TorusLeviWitness t :=
  torusDynamicLeviWitnessFromDynamic i t d.cocharacter hG d.represents

end TorusDynamicPresentation

namespace TorusLeviWitness

variable {S S' : Scheme.{u}} {G P : GroupScheme S} {T : CommGroupScheme S}
    {i : P ⟶ G} {t : T.toGrp ⟶ P}

/-- Pull back the actual chosen witness using local dynamic uniqueness alone. -/
def baseChangeFromDynamic (w : TorusLeviWitness t) (d : TorusDynamicPresentation i t)
    (hG : IsReductive G) (b : S' ⟶ S) :
    TorusLeviWitness (T := (CommGroupScheme.baseChange b).obj T)
      ((GroupScheme.baseChange b).map t) := by
  have hl := w.isLevi_baseChange d dynamicRelativeLevi hG b
  have ht : SubgroupFunctor.range ((GroupScheme.baseChange b).map t) ≤
      SubgroupFunctor.range ((GroupScheme.baseChange b).map w.inclusion) := by
    rw [SubgroupFunctor.range_baseChangeHom, SubgroupFunctor.range_baseChangeHom]
    intro V x hx
    exact w.contains _ hx
  let v := (d.baseChange b).witnessFromDynamic (hG.baseChange b)
  refine ⟨(GroupScheme.baseChange b).obj w.group, (GroupScheme.baseChange b).map w.inclusion,
    hl, ht, ?_⟩
  intro L' l' hl' ht'
  exact (v.unique L' l' hl' ht').trans
    (v.unique _ ((GroupScheme.baseChange b).map w.inclusion) hl ht).symm

end TorusLeviWitness

namespace EtaleTorusLeviData

variable {S : Scheme.{u}} {G P : GroupScheme S} {T : CommGroupScheme S}
    {i : P ⟶ G} {t : T.toGrp ⟶ P}

/-- Pairwise agreement of the local witnesses without a universal radical theorem. -/
theorem overlap_range_eq_fromDynamic (D : EtaleTorusLeviData i t)
    (hG : IsReductive G) (a b : D.cover.I₀) :
    SubgroupFunctor.range ((GroupScheme.baseChange (pullback.fst (D.cover.f a) (D.cover.f b))).map
      (D.witness a).inclusion) =
    SubgroupFunctor.range ((GroupScheme.baseChange (pullback.snd (D.cover.f a) (D.cover.f b))).map
      (D.witness b).inclusion ≫
        (Descent.squareComparison (D.cover.f a) (pullback.fst (D.cover.f a) (D.cover.f b))
          (D.cover.f b) (pullback.snd (D.cover.f a) (D.cover.f b)) pullback.condition P).inv) := by
  let e := Descent.squareComparison (D.cover.f a) (pullback.fst (D.cover.f a) (D.cover.f b))
    (D.cover.f b) (pullback.snd (D.cover.f a) (D.cover.f b)) pullback.condition P
  let v : TorusLeviWitness
      (T := (CommGroupScheme.baseChange (pullback.snd (D.cover.f a) (D.cover.f b))).obj
        ((CommGroupScheme.baseChange (D.cover.f b)).obj T))
      ((GroupScheme.baseChange (pullback.snd (D.cover.f a) (D.cover.f b))).map
        ((GroupScheme.baseChange (D.cover.f b)).map t)) :=
    ((D.witness a).baseChangeFromDynamic (D.presentation a)
    (hG.baseChange (D.cover.f a)) (pullback.fst (D.cover.f a) (D.cover.f b))).transport e
      (Descent.squareComparison (D.cover.f a) (pullback.fst (D.cover.f a) (D.cover.f b))
        (D.cover.f b) (pullback.snd (D.cover.f a) (D.cover.f b)) pullback.condition T.toGrp)
      (Descent.squareComparison_naturality (D.cover.f a) (pullback.fst (D.cover.f a) (D.cover.f b))
        (D.cover.f b) (pullback.snd (D.cover.f a) (D.cover.f b)) pullback.condition t).symm
  let v' := (D.witness b).baseChangeFromDynamic (D.presentation b)
    (hG.baseChange (D.cover.f b)) (pullback.snd (D.cover.f a) (D.cover.f b))
  have heq := v.unique v'.group v'.inclusion v'.isLevi v'.contains
  change SubgroupFunctor.range ((GroupScheme.baseChange (pullback.snd (D.cover.f a) (D.cover.f b))).map
    (D.witness b).inclusion) =
    SubgroupFunctor.range ((GroupScheme.baseChange (pullback.fst (D.cover.f a) (D.cover.f b))).map
      (D.witness a).inclusion ≫ e.hom) at heq
  have hback := (SubgroupFunctor.range_comp_iso_eq_iff
    ((GroupScheme.baseChange (pullback.snd (D.cover.f a) (D.cover.f b))).map (D.witness b).inclusion)
    ((GroupScheme.baseChange (pullback.fst (D.cover.f a) (D.cover.f b))).map (D.witness a).inclusion ≫ e.hom)
    e.symm).mpr heq
  simpa only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id] using
    hback.symm

/-- Local dynamic uniqueness gives matching on every relative test scheme. -/
theorem isMatchingFromDynamic (D : EtaleTorusLeviData i t) (hG : IsReductive G) :
    SubgroupFunctor.CoverDescent.IsMatching D.cover
      (fun a => SubgroupFunctor.range (D.witness a).inclusion) :=
  SubgroupFunctor.CoverDescent.isMatching_of_overlap_range_eq D.cover
    (fun a => (D.witness a).group) (fun a => (D.witness a).inclusion)
    (fun a b => D.overlap_range_eq_fromDynamic hG a b)

end EtaleTorusLeviData

end Langlands.GroupScheme.RelativeLevi
