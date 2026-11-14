import Langlands.GroupScheme.RelativeLevi.DynamicTorusUniqueness
import Langlands.GroupScheme.RelativeLevi.DynamicStatement
import Langlands.GroupScheme.RelativeLevi.UnipotentRadicalStatement
import Langlands.GroupScheme.Dynamic.BaseRepresentabilityProof
import Langlands.GroupScheme.Dynamic.SchemeDecomposition
import Langlands.GroupScheme.Rational.LeviCentralizerExtension
import Langlands.GroupScheme.ClosedSubgroupMonomorphism

/-! # The unique Levi containing a torus in a dynamic presentation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeLevi

/-- An actual Levi subgroup containing a prescribed commutative subgroup,
with uniqueness of its all-test range among such Levi subgroups. -/
structure TorusLeviWitness {S : Scheme.{u}} {P : GroupScheme S}
    {T : CommGroupScheme S} (t : T.toGrp ⟶ P) where
  group : GroupScheme S
  inclusion : group ⟶ P
  isLevi : IsRelativeLeviSubgroup inclusion
  contains : SubgroupFunctor.range t ≤ SubgroupFunctor.range inclusion
  unique : ∀ (L' : GroupScheme S) (l' : L' ⟶ P), IsRelativeLeviSubgroup l' →
    SubgroupFunctor.range t ≤ SubgroupFunctor.range l' →
      SubgroupFunctor.range l' = SubgroupFunctor.range inclusion

/-- Construct the unique Levi containing the commutative subgroup whenever
its cocharacter dynamically presents the parabolic. The two relative
structure statements are explicit inputs. -/
def torusDynamicLeviWitness
    (hDynamic : DynamicRelativeLeviStatement.{u})
    (hRadical : RelativeUnipotentRadicalStatement.{u})
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
  have hd := hDynamic S G P U Z chi i iU iZ hG hP hU hZ
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
    obtain ⟨U0, r0, _, huniq⟩ := hRadical S G P i hG hd.1
    have hrr : SubgroupFunctor.range r' = SubgroupFunctor.range r :=
      (huniq U' r' hr').trans (huniq U r hr).symm
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

end Langlands.GroupScheme.RelativeLevi
