import Langlands.GroupScheme.Rational.NestedParabolicContainment
import Langlands.GroupScheme.Rational.LeviRetraction
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Dynamic.Functoriality
import Langlands.GroupScheme.Reductive.UnipotentRadicalQuotientReduction
import Langlands.GroupScheme.RepresentedSubgroup

/-! # A nested parabolic as an actual inverse image under a Levi retraction -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Base

variable {S : Scheme.{u}} {P Q L U PL : GroupScheme S}
  (a : P ⟶ Q) (l : L ⟶ Q) (r : U ⟶ Q) (s : PL ⟶ L)
  [IsIso (subgroupMultiplication l r)]

/-- Containment of both factors and containment of the projected range identify
an actual subgroup with the inverse image of a subgroup of the Levi. -/
theorem range_eq_comap_leviRetraction
    (hr : (SubgroupFunctor.range r).IsNormal)
    (hL : SubgroupFunctor.range (s ≫ l) ≤ SubgroupFunctor.range a)
    (hU : SubgroupFunctor.range r ≤ SubgroupFunctor.range a)
    (ht : SubgroupFunctor.range (a ≫ leviRetraction l r hr) ≤
      SubgroupFunctor.range s) :
    SubgroupFunctor.range a =
      (SubgroupFunctor.range s).comap (leviRetraction l r hr) := by
  apply le_antisymm
  · intro T x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    change (y ≫ a.hom.hom) ≫ (leviRetraction l r hr).hom.hom ∈
      (SubgroupFunctor.range s).carrier T
    exact ht T ⟨y, by
      change y ≫ (a ≫ leviRetraction l r hr).hom.hom = _
      rw [Grp.comp_hom_hom, Category.assoc]⟩
  · intro T x hx
    rw [SubgroupFunctor.mem_comap] at hx
    obtain ⟨b, hb⟩ := SubgroupFunctor.mem_range.mp hx
    have hz : leviComponent l r x = b ≫ s.hom.hom := by
      rw [← comp_leviRetraction]
      exact hb.symm
    have hdec := leviComponent_mul_radicalComponent l r x
    rw [hz] at hdec
    rw [← hdec]
    apply (SubgroupFunctor.range a).carrier T |>.mul_mem
    · apply hL T
      refine ⟨b, ?_⟩
      change b ≫ (s ≫ l).hom.hom = _
      rw [Grp.comp_hom_hom, Category.assoc]
    · exact hU T ⟨radicalComponent l r x, rfl⟩

/-- The range comparison identifies the original subgroup scheme with the
actual inverse image under the Levi retraction. -/
def leviPreimageIsoOfRange [Mono a.hom.hom]
    (hr : (SubgroupFunctor.range r).IsNormal) (hs : IsClosedSubgroup s)
    (h : SubgroupFunctor.range a =
      (SubgroupFunctor.range s).comap (leviRetraction l r hr)) :
    P ≅ SubgroupPreimage.groupScheme (leviRetraction l r hr) s :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy
    (F := (SubgroupFunctor.range s).comap (leviRetraction l r hr))
    (i := a) ⟨inferInstance, h⟩
    (i₂ := SubgroupPreimage.inclusion (leviRetraction l r hr) s)
    ⟨(SubgroupPreimage.isClosedSubgroup _ _ hs).mono_overHom,
      SubgroupPreimage.range_inclusion _ _⟩

/-- The inverse-image comparison preserves the supplied inclusion into the
outer parabolic. -/
@[reassoc]
theorem leviPreimageIsoOfRange_hom_comp [Mono a.hom.hom]
    (hr : (SubgroupFunctor.range r).IsNormal) (hs : IsClosedSubgroup s)
    (h : SubgroupFunctor.range a =
      (SubgroupFunctor.range s).comap (leviRetraction l r hr)) :
    (leviPreimageIsoOfRange a l r s hr hs h).hom ≫
      SubgroupPreimage.inclusion (leviRetraction l r hr) s = a :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

end Base

section LocalField

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {G P Q L U PL : GroupScheme (Spec (CommRingCat.of k))}
  (p : P ⟶ G) (q : Q ⟶ G) (l : L ⟶ Q) (r : U ⟶ Q) (s : PL ⟶ L)
  [Smooth P.X.hom] [IsAffineHom P.X.hom] [ConnectedSpace P.X.left]
  [Smooth Q.X.hom] [IsAffineHom Q.X.hom] [ConnectedSpace Q.X.left]
  [Smooth PL.X.hom] [IsAffineHom PL.X.hom] [ConnectedSpace PL.X.left]
  [IsIso (subgroupMultiplication l r)]

/-- Over a nonarchimedean local field, the supplied rational-point nesting and
intersection identify the actual nested parabolic with the inverse image of
the supplied subgroup of the outer Levi. -/
theorem exists_range_eq_comap_leviRetraction_of_nested_points
    (hp : IsParabolicSubgroup p) (hq : IsClosedSubgroup q)
    (hl : IsClosedSubgroup l) (hs : IsClosedSubgroup s)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hPQ : (rationalPoints.map p).range ≤ (rationalPoints.map q).range)
    (hPL : (rationalPoints.map (s ≫ l ≫ q)).range =
      (rationalPoints.map (l ≫ q)).range ⊓ (rationalPoints.map p).range) :
    ∃ a : P ⟶ Q, a ≫ q = p ∧
      SubgroupFunctor.range a =
        (SubgroupFunctor.range s).comap (leviRetraction l r hr.1.isNormal) := by
  have hPQ' : SubgroupFunctor.range p ≤ SubgroupFunctor.range q :=
    SubgroupFunctor.range_le_of_localField_points hq hPQ
  let hQ : (SubgroupFunctor.range q).IsRepresentedBy q :=
    ⟨hq.mono_overHom, rfl⟩
  let a : P ⟶ Q := hQ.factorHom p hPQ'
  have ha : a ≫ q = p := hQ.factorHom_comp p hPQ'
  have ha' : a.hom.hom ≫ q.hom.hom = p.hom.hom :=
    congrArg (fun f => f.hom.hom) ha
  have : Mono q.hom.hom := hq.mono_overHom
  have : Mono l.hom.hom := hl.mono_overHom
  have hU : SubgroupFunctor.range r ≤ SubgroupFunctor.range a :=
    range_normalUnipotent_le_nestedParabolic p q a r hp hq ha hr
  have hSLP : SubgroupFunctor.range (s ≫ l ≫ q) ≤ SubgroupFunctor.range p := by
    apply SubgroupFunctor.range_le_of_localField_points hp.isClosedSubgroup
    intro x hx
    have hx' : x ∈ (rationalPoints.map (s ≫ l ≫ q)).range := hx
    rw [hPL] at hx'
    exact hx'.2
  have hL : SubgroupFunctor.range (s ≫ l) ≤ SubgroupFunctor.range a := by
    intro T x hx
    obtain ⟨b, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp (hSLP T ⟨b, rfl⟩)
    change y ≫ p.hom.hom = b ≫ (s ≫ l ≫ q).hom.hom at hy
    refine ⟨y, ?_⟩
    change y ≫ a.hom.hom = b ≫ (s ≫ l).hom.hom
    apply (cancel_mono q.hom.hom).mp
    rw [Category.assoc, ha']
    simpa only [Grp.comp_hom_hom, Category.assoc] using hy
  have ht : SubgroupFunctor.range (a ≫ leviRetraction l r hr.1.isNormal) ≤
      SubgroupFunctor.range s := by
    apply SubgroupFunctor.range_le_of_localField_points hs
    intro x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    let z := leviComponent l r (y ≫ a.hom.hom)
    let v := radicalComponent l r (y ≫ a.hom.hom)
    have hdec : (z ≫ l.hom.hom) * (v ≫ r.hom.hom) = y ≫ a.hom.hom :=
      leviComponent_mul_radicalComponent l r _
    have hz : z ≫ l.hom.hom = (y ≫ a.hom.hom) * (v ≫ r.hom.hom)⁻¹ :=
      (eq_mul_inv_iff_mul_eq).mpr hdec
    have hyP : (y ≫ a.hom.hom) ≫ q.hom.hom ∈
        (SubgroupFunctor.range p).carrier _ :=
      ⟨y, by
        change y ≫ p.hom.hom = _
        rw [Category.assoc, ha']⟩
    obtain ⟨vP, hvP⟩ := SubgroupFunctor.mem_range.mp (hU _ ⟨v, rfl⟩)
    change vP ≫ a.hom.hom = v ≫ r.hom.hom at hvP
    have hvP' : (v ≫ r.hom.hom) ≫ q.hom.hom ∈
        (SubgroupFunctor.range p).carrier _ := by
      refine ⟨vP, ?_⟩
      change vP ≫ p.hom.hom = _
      rw [← ha', ← Category.assoc, hvP]
    have hzP : (z ≫ l.hom.hom) ≫ q.hom.hom ∈
        (SubgroupFunctor.range p).carrier _ := by
      rw [hz, MonObj.mul_comp, GrpObj.inv_comp]
      exact (SubgroupFunctor.range p).carrier _ |>.mul_mem hyP
        ((SubgroupFunctor.range p).carrier _ |>.inv_mem hvP')
    have hzPL : (z ≫ l.hom.hom) ≫ q.hom.hom ∈
        (rationalPoints.map (s ≫ l ≫ q)).range := by
      rw [hPL]
      refine ⟨⟨z, ?_⟩, hzP⟩
      change z ≫ (l ≫ q).hom.hom = _
      rw [Grp.comp_hom_hom, Category.assoc]
    obtain ⟨b, hb⟩ := hzPL
    change b ≫ (s ≫ l ≫ q).hom.hom = (z ≫ l.hom.hom) ≫ q.hom.hom at hb
    refine ⟨b, ?_⟩
    change b ≫ s.hom.hom = y ≫ (a ≫ leviRetraction l r hr.1.isNormal).hom.hom
    rw [Grp.comp_hom_hom, ← Category.assoc, comp_leviRetraction]
    change b ≫ s.hom.hom = z
    apply (cancel_mono l.hom.hom).mp
    apply (cancel_mono q.hom.hom).mp
    simpa only [rationalPoints.map, Grp.comp_hom_hom, Category.assoc] using hb
  exact ⟨a, ha, range_eq_comap_leviRetraction a l r s hr.1.isNormal hL hU ht⟩

end LocalField

end Langlands.GroupScheme
