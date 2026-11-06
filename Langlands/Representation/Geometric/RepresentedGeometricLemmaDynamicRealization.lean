import Langlands.Representation.Geometric.RepresentedGeometricLemmaCommonTorus
import Langlands.GroupScheme.Rational.ParabolicLeviRealization
import Langlands.GroupScheme.Rational.ParabolicAmbientTransport
import Langlands.GroupScheme.Dynamic.GeometricUnipotentRadicalProof

/-! # Simultaneous dynamic realization in the original common torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

section Realization

variable {k : Type u} [Field k]
  {G P M N : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (hG : IsConnectedReductive G)
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P}
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)

include hG hp hr

/-- A specified radical agrees on every test scheme with the dynamic
unipotent subgroup once the original parabolic is dynamically realized. -/
theorem radical_range_eq_dynamic_unipotent
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hP : SubgroupFunctor.range p = Dynamic.parabolic χ) :
    SubgroupFunctor.range (r ≫ p) = Dynamic.unipotent χ := by
  have hc := hp.isClosedSubgroup
  have : IsClosedImmersion p.hom.hom.left := hc
  have : Mono p.hom.hom := Over.mono_of_mono_left _
  have hrep : (Dynamic.parabolic χ).IsRepresentedBy p := ⟨inferInstance, hP⟩
  apply SubgroupFunctor.ext
  intro W
  apply Subgroup.ext
  intro x
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    rw [Grp.comp_hom_hom, ← Category.assoc]
    exact (DynamicLeviConjugacy.mem_range_radical_iff
      dynamicGeometricUnipotentRadical hG χ hc hrep hr (y ≫ r.hom.hom)).mp
        (SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩)
  · intro hx
    have hxP : x ∈ (SubgroupFunctor.range p).carrier W := by
      rw [hP]
      exact Dynamic.unipotent_le_parabolic χ W hx
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hxP
    have hyr : y ∈ (SubgroupFunctor.range r).carrier W :=
      (DynamicLeviConjugacy.mem_range_radical_iff
        dynamicGeometricUnipotentRadical hG χ hc hrep hr y).mpr (by rwa [hy])
    obtain ⟨w, hw⟩ := SubgroupFunctor.mem_range.mp hyr
    exact SubgroupFunctor.mem_range.mpr ⟨w, by
      rw [Grp.comp_hom_hom, ← Category.assoc, hw, hy]⟩

include hl

/-- The original parabolic, Levi and radical are realized by one cocharacter
of any displayed ambient maximal split torus already factoring through the
original Levi. Only the parabolic-dynamic statement remains explicit. -/
theorem exists_cocharacter_parabolic_triple_in_torus
    (hPD : ParabolicDynamicStatement.{u}) (j : T.toGrp ⟶ M)
    (hi : IsMaximalSplitTorus (j ≫ l ≫ p)) :
    let := hG.isAffineHom
    ∃ ξ : cocharacterLattice T,
      SubgroupFunctor.range p =
        Dynamic.parabolic (CommGroupScheme.groupHom ξ ≫ j ≫ l ≫ p) ∧
      SubgroupFunctor.range (l ≫ p) =
        Dynamic.centralizer (CommGroupScheme.groupHom ξ ≫ j ≫ l ≫ p) ∧
      SubgroupFunctor.range (r ≫ p) =
        Dynamic.unipotent (CommGroupScheme.groupHom ξ ≫ j ≫ l ≫ p) := by
  have := hG.isAffineHom
  obtain ⟨χ, hP, hM⟩ := DynamicLeviConjugacy.exists_cocharacter_parabolic_levi
    hPD dynamicGeometricUnipotentRadical hG hp hl
  have hχ : SubgroupFunctor.range (j ≫ l ≫ p) ≤ Dynamic.centralizer χ := by
    rw [← hM]
    intro W x hx
    obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    exact SubgroupFunctor.mem_range.mpr ⟨t ≫ j.hom.hom, by
      simp only [Grp.comp_hom_hom, Category.assoc]⟩
  obtain ⟨ξ, hξ⟩ := hi.exists_cocharacter_factor_of_centralizing χ hχ
  have hξ' : CommGroupScheme.groupHom ξ ≫ j ≫ l ≫ p = χ := by
    simpa only [Category.assoc] using hξ
  refine ⟨ξ, ?_, ?_, ?_⟩
  · rwa [hξ']
  · rwa [hξ']
  · rw [hξ']
    exact radical_range_eq_dynamic_unipotent hG hp hr χ hP

end Realization

end Langlands.GroupScheme

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [TopologicalSpace k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P}
  {hp : IsParabolicSubgroup p} {hr : LeviSubgroup.IsGeometricUnipotentRadical r}
  {hl : IsRationalLeviSubgroup l} {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {rQ : U ⟶ Q}
  {hq : IsParabolicSubgroup q} {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ}
  {hlQ : IsRationalLeviSubgroup lQ} {hmulQ : IsIso (subgroupMultiplication lQ rQ)}
  {z : rationalPoints G}

namespace GeometricLemmaIntersectionDatum

variable (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul
  q lQ rQ hq hrQ hlQ hmulQ z)

local notation "iT" => D.targetCommonTorusHom ≫ D.lQ' ≫ D.q' ≫ lQ ≫ q

/-- A simultaneous realization of the original target triple and the original
source triple conjugated by z⁻¹, in the datum's fixed common torus. -/
structure DynamicRealization where
  targetCocharacter : cocharacterLattice D.torus
  sourceCocharacter : cocharacterLattice D.torus
  targetParabolic : SubgroupFunctor.range q =
    Dynamic.parabolic (CommGroupScheme.groupHom targetCocharacter ≫ iT)
  targetLevi : SubgroupFunctor.range (lQ ≫ q) =
    Dynamic.centralizer (CommGroupScheme.groupHom targetCocharacter ≫ iT)
  targetRadical : SubgroupFunctor.range (rQ ≫ q) =
    Dynamic.unipotent (CommGroupScheme.groupHom targetCocharacter ≫ iT)
  sourceParabolic : SubgroupFunctor.range (p ≫ (G.innerIso z⁻¹).hom) =
    Dynamic.parabolic (CommGroupScheme.groupHom sourceCocharacter ≫ iT)
  sourceLevi : SubgroupFunctor.range (l ≫ p ≫ (G.innerIso z⁻¹).hom) =
    Dynamic.centralizer (CommGroupScheme.groupHom sourceCocharacter ≫ iT)
  sourceRadical : SubgroupFunctor.range (r ≫ p ≫ (G.innerIso z⁻¹).hom) =
    Dynamic.unipotent (CommGroupScheme.groupHom sourceCocharacter ≫ iT)

/-- Construct the simultaneous realization from the explicit universal
parabolic-dynamic statement and ambient connected reductivity. -/
def dynamicRealizationOfParabolicDynamic
    (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G) :
    D.DynamicRealization := by
  apply Classical.choice
  let := hG.isAffineHom
  obtain ⟨ξ, hQ, hL, hU⟩ := exists_cocharacter_parabolic_triple_in_torus
    hG hq hlQ hrQ hPD (D.targetCommonTorusHom ≫ D.lQ' ≫ D.q')
      (by simpa only [Category.assoc] using
        D.targetCommonTorus_isMaximalSplitTorus_ambient)
  have hpz : IsParabolicSubgroup (p ≫ (G.innerIso z⁻¹).hom) :=
    hp.comp_iso (G.innerIso z⁻¹)
  have his : IsMaximalSplitTorus
      ((D.t ≫ D.l' ≫ D.p') ≫ l ≫ (p ≫ (G.innerIso z⁻¹).hom)) := by
    simpa only [Category.assoc] using D.isMaximalSplitTorus.comp_iso (G.innerIso z⁻¹)
  obtain ⟨eta, hP, hM, hN⟩ := exists_cocharacter_parabolic_triple_in_torus
    hG hpz hl hr hPD (D.t ≫ D.l' ≫ D.p') his
  have hsame : (D.t ≫ D.l' ≫ D.p') ≫ l ≫ (p ≫ (G.innerIso z⁻¹).hom) = iT := by
    rw [D.targetCommonTorusHom_comp]
    simp only [Category.assoc, G.innerIso_inv_hom]
  refine ⟨⟨ξ, eta, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · simpa only [Category.assoc] using hQ
  · simpa only [Category.assoc] using hL
  · simpa only [Category.assoc] using hU
  · simpa only [hsame, Category.assoc] using hP
  · simpa only [hsame, Category.assoc] using hM
  · simpa only [hsame, Category.assoc] using hN

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic
