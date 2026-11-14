import Langlands.GroupScheme.RelativeLevi.ConjugatorBaseChange
import Langlands.GroupScheme.RelativeLevi.ConjugatorUniquenessBaseChange
import Langlands.GroupScheme.IntegralModel

/-! # Relative Levi conjugacy from etale-local radical conjugators -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeLevi

variable {S : Scheme.{u}} {P L L' U V : GroupScheme S}

/-- Existence of actual radical conjugators on an etale cover of a test scheme. -/
def EtaleLocallyRadicalConjugate (l : L ⟶ P) (l' : L' ⟶ P) (r : U ⟶ P)
    (T : Over S) : Prop :=
  ∃ 𝒰 : T.left.Cover.{v} (Scheme.precoverage @Etale),
    ∀ k, ∃ n : SubgroupFunctor.etaleCoverObj 𝒰 k ⟶ U.X,
      IsRadicalConjugator l l' r n

/-- Lifting a radical point and then applying its inclusion agrees with
lifting its image in the ambient group. -/
theorem rangeConjugateAt_radical_image_eq (l : L ⟶ P) (r : U ⟶ P)
    (T : Over S) (n : T ⟶ U.X) :
    rangeConjugateAt l T (n ≫ r.hom.hom) = radicalConjugateAt l r T n := by
  have hn : (baseChangeBasePointsEquiv T.hom P).symm (n ≫ r.hom.hom) =
      (baseChangeBasePointsEquiv T.hom U).symm n ≫
        ((GroupScheme.baseChange T.hom).map r).hom.hom := by
    apply (baseChangeBasePointsEquiv T.hom P).injective
    rw [MulEquiv.apply_symm_apply, baseChangeBasePointsEquiv_comp,
      MulEquiv.apply_symm_apply]
  unfold rangeConjugateAt radicalConjugateAt radicalConjugate
  rw [hn]

/-- The radical conjugator predicate is equality with its conjugated range
over the point's actual domain. -/
theorem isRadicalConjugator_iff_range_baseChange_eq (l : L ⟶ P) (l' : L' ⟶ P)
    (r : U ⟶ P) (T : Over S) (n : T ⟶ U.X) :
    IsRadicalConjugator l l' r n ↔
      SubgroupFunctor.range ((GroupScheme.baseChange T.hom).map l') =
        radicalConjugateAt l r T n := by
  unfold IsRadicalConjugator
  rw [isRangeConjugator_iff_range_baseChange_eq, rangeConjugateAt_radical_image_eq]

/-- The algebraic uniqueness hypotheses imply equality of all-test radical
conjugators on every test scheme. -/
theorem eq_of_isRadicalConjugator_of_range_le
    (l : L ⟶ P) (l' : L' ⟶ P) (r : U ⟶ P) (s : V ⟶ P)
    [Mono l.hom.hom] [Mono r.hom.hom] [IsIso (subgroupMultiplication l s)]
    (hrs : SubgroupFunctor.range r ≤ SubgroupFunctor.range s)
    (hN : (SubgroupFunctor.range l).normalizer ≤ SubgroupFunctor.range l)
    (T : Over S) (a b : T ⟶ U.X)
    (ha : IsRadicalConjugator l l' r a) (hb : IsRadicalConjugator l l' r b) :
    a = b := by
  apply radicalConjugateAt_injective_of_range_le l r s hrs hN T
  exact ((isRadicalConjugator_iff_range_baseChange_eq l l' r T a).mp ha).symm.trans
    ((isRadicalConjugator_iff_range_baseChange_eq l l' r T b).mp hb)

/-- Supplied geometric radical uniqueness and Levi self-normalization yield
the all-test uniqueness needed for descent. -/
theorem relative_eq_of_isRadicalConjugator
    (hRadical : RelativeUnipotentRadicalStatement.{u})
    (hNormalizer : RelativeLeviSelfNormalizerStatement.{u})
    (G P U L L' : GroupScheme S) (i : P ⟶ G) (r : U ⟶ P)
    (l : L ⟶ P) (l' : L' ⟶ P)
    (hG : IsReductive G) (hi : IsRelativeParabolicSubgroup i)
    (hr : IsRelativeUnipotentRadical r) (hl : IsRelativeLeviSubgroup l)
    (T : Over S) (a b : T ⟶ U.X)
    (ha : IsRadicalConjugator l l' r a) (hb : IsRadicalConjugator l l' r b) :
    a = b := by
  apply relative_radicalConjugateAt_injective hRadical hNormalizer G P U L i r l
    hG hi hr hl T
  exact ((isRadicalConjugator_iff_range_baseChange_eq l l' r T a).mp ha).symm.trans
    ((isRadicalConjugator_iff_range_baseChange_eq l l' r T b).mp hb)

/-- Algebraic uniqueness turns etale-local radical conjugators into a unique
conjugator on the given test scheme. -/
theorem existsUnique_isRadicalConjugator_of_etaleLocal
    (l : L ⟶ P) (l' : L' ⟶ P) (r : U ⟶ P) (s : V ⟶ P)
    [Mono l.hom.hom] [Mono l'.hom.hom] [Mono r.hom.hom]
    [IsIso (subgroupMultiplication l s)]
    (hrs : SubgroupFunctor.range r ≤ SubgroupFunctor.range s)
    (hN : (SubgroupFunctor.range l).normalizer ≤ SubgroupFunctor.range l)
    (T : Over S) (hex : EtaleLocallyRadicalConjugate.{u, v} l l' r T) :
    ∃! n : T ⟶ U.X, IsRadicalConjugator l l' r n := by
  obtain ⟨𝒰, h𝒰⟩ := hex
  exact existsUnique_isRadicalConjugator_of_etaleCover l l' r
    (eq_of_isRadicalConjugator_of_range_le l l' r s hrs hN) 𝒰 h𝒰

/-- For relative Levi subgroups, the remaining inputs are the two supplied
geometric statements and actual etale-local radical conjugators. -/
theorem relative_existsUnique_conjugator_of_etaleLocal
    (hRadical : RelativeUnipotentRadicalStatement.{u})
    (hNormalizer : RelativeLeviSelfNormalizerStatement.{u})
    (G P U L L' : GroupScheme S) (i : P ⟶ G) (r : U ⟶ P)
    (l : L ⟶ P) (l' : L' ⟶ P)
    (hG : IsReductive G) (hi : IsRelativeParabolicSubgroup i)
    (hr : IsRelativeUnipotentRadical r) (hl : IsRelativeLeviSubgroup l)
    (hl' : IsRelativeLeviSubgroup l')
    (hex : EtaleLocallyRadicalConjugate.{u, v} l l' r (Over.mk (𝟙 S))) :
    ∃! n : Over.mk (𝟙 S) ⟶ U.X,
      SubgroupFunctor.range l' =
        SubgroupFunctor.range (l ≫ (P.innerIso (n ≫ r.hom.hom)).hom) := by
  let : IsClosedImmersion l.hom.hom.left := hl.isClosedSubgroup
  let : IsClosedImmersion l'.hom.hom.left := hl'.isClosedSubgroup
  let : Mono l.hom.hom := Over.mono_of_mono_left _
  let : Mono l'.hom.hom := Over.mono_of_mono_left _
  obtain ⟨𝒰, h𝒰⟩ := hex
  obtain ⟨n, hn, huniq⟩ :=
    existsUnique_isRadicalConjugator_of_etaleCover l l' r
      (relative_eq_of_isRadicalConjugator hRadical hNormalizer G P U L L'
        i r l l' hG hi hr hl) 𝒰 h𝒰
  refine ⟨n, (isRangeConjugator_iff_range_eq l l' _).mp hn, ?_⟩
  intro m hm
  exact huniq m ((isRangeConjugator_iff_range_eq l l' _).mpr hm)

end Langlands.GroupScheme.RelativeLevi
