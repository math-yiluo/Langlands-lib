import Langlands.GroupScheme.RelativeLevi.ConjugacyDescent

/-! # From etale-local ambient conjugators to radical conjugators -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeLevi

variable {S : Scheme.{u}} {P L L' U V : GroupScheme S}

/-- Existence of actual ambient-group conjugators on an etale cover. -/
def EtaleLocallyRangeConjugate (l : L ⟶ P) (l' : L' ⟶ P) (T : Over S) : Prop :=
  ∃ 𝒰 : T.left.Cover.{v} (Scheme.precoverage @Etale),
    ∀ k, ∃ g : SubgroupFunctor.etaleCoverObj 𝒰 k ⟶ P.X,
      IsRangeConjugator l l' g

/-- A complement to a normal factor has a radical conjugator wherever it has
an ambient conjugator. The specified radical may contain the normal factor. -/
theorem exists_isRadicalConjugator_of_isRangeConjugator
    (l : L ⟶ P) (l' : L' ⟶ P) (r : U ⟶ P) (s : V ⟶ P)
    [IsIso (subgroupMultiplication l s)] (hs : (SubgroupFunctor.range s).IsNormal)
    (hsr : SubgroupFunctor.range s ≤ SubgroupFunctor.range r)
    (T : Over S) (g : T ⟶ P.X) (hg : IsRangeConjugator l l' g) :
    ∃ n : T ⟶ U.X, IsRadicalConjugator l l' r n := by
  let : IsIso (subgroupMultiplication ((GroupScheme.baseChange T.hom).map l)
      ((GroupScheme.baseChange T.hom).map s)) :=
    isIso_subgroupMultiplication_baseChange T.hom l s
  have hs' : (SubgroupFunctor.range ((GroupScheme.baseChange T.hom).map s)).IsNormal := by
    simpa only [SubgroupFunctor.range_baseChangeHom] using hs.baseChange T.hom
  have hsr' : SubgroupFunctor.range ((GroupScheme.baseChange T.hom).map s) ≤
      SubgroupFunctor.range ((GroupScheme.baseChange T.hom).map r) := by
    simpa only [SubgroupFunctor.range_baseChangeHom] using
      SubgroupFunctor.baseChange_mono T.hom hsr
  have hg' := (isRangeConjugator_iff_range_baseChange_eq l l' T g).mp hg
  obtain ⟨a, ha⟩ := exists_radicalPoint_of_range_conjugate
    ((GroupScheme.baseChange T.hom).map l) ((GroupScheme.baseChange T.hom).map s)
    hs' ((GroupScheme.baseChange T.hom).map l')
    ((baseChangeBasePointsEquiv T.hom P).symm g) hg'
  have ha' : a ≫ ((GroupScheme.baseChange T.hom).map s).hom.hom ∈
      (SubgroupFunctor.range ((GroupScheme.baseChange T.hom).map s)).carrier
        (Over.mk (𝟙 T.left)) := SubgroupFunctor.mem_range.mpr ⟨a, rfl⟩
  obtain ⟨n, hn⟩ := SubgroupFunctor.mem_range.mp (hsr' _ ha')
  refine ⟨baseChangeBasePointsEquiv T.hom U n, ?_⟩
  apply (isRadicalConjugator_iff_range_baseChange_eq l l' r T _).mpr
  unfold radicalConjugateAt radicalConjugate
  rw [MulEquiv.symm_apply_apply, hn]
  exact ha

/-- Local ambient conjugators therefore give local radical conjugators under
the same original-base algebraic hypotheses. -/
theorem etaleLocallyRadicalConjugate_of_range
    (l : L ⟶ P) (l' : L' ⟶ P) (r : U ⟶ P) (s : V ⟶ P)
    [IsIso (subgroupMultiplication l s)] (hs : (SubgroupFunctor.range s).IsNormal)
    (hsr : SubgroupFunctor.range s ≤ SubgroupFunctor.range r)
    (T : Over S) (hex : EtaleLocallyRangeConjugate.{u, v} l l' T) :
    EtaleLocallyRadicalConjugate.{u, v} l l' r T := by
  obtain ⟨𝒰, h𝒰⟩ := hex
  refine ⟨𝒰, fun k => ?_⟩
  obtain ⟨g, hg⟩ := h𝒰 k
  exact exists_isRadicalConjugator_of_isRangeConjugator l l' r s hs hsr _ g hg

/-- Relative radical uniqueness identifies the specified radical with the
normal factor in a Levi decomposition, before any test-scheme base change. -/
theorem relative_etaleLocallyRadicalConjugate_of_range
    (hRadical : RelativeUnipotentRadicalStatement.{u})
    (G P U L L' : GroupScheme S) (i : P ⟶ G) (r : U ⟶ P)
    (l : L ⟶ P) (l' : L' ⟶ P)
    (hG : IsReductive G) (hi : IsRelativeParabolicSubgroup i)
    (hr : IsRelativeUnipotentRadical r) (hl : IsRelativeLeviSubgroup l)
    (T : Over S) (hex : EtaleLocallyRangeConjugate.{u, v} l l' T) :
    EtaleLocallyRadicalConjugate.{u, v} l l' r T := by
  obtain ⟨V, s, hs, hmul⟩ := hl.exists_unipotentRadical
  obtain ⟨W, t, _, ht⟩ := hRadical S G P i hG hi
  have hsr : SubgroupFunctor.range s ≤ SubgroupFunctor.range r :=
    ((ht V s hs).trans (ht U r hr).symm).le
  let : IsIso (subgroupMultiplication l s) := hmul
  exact etaleLocallyRadicalConjugate_of_range l l' r s hs.isNormal hsr T hex

/-- Supplied relative radical uniqueness, self-normalization and etale-local
ambient conjugacy imply the exact global relative Levi conjugacy conclusion. -/
theorem relative_existsUnique_conjugator_of_etaleLocal_range
    (hRadical : RelativeUnipotentRadicalStatement.{u})
    (hNormalizer : RelativeLeviSelfNormalizerStatement.{u})
    (G P U L L' : GroupScheme S) (i : P ⟶ G) (r : U ⟶ P)
    (l : L ⟶ P) (l' : L' ⟶ P)
    (hG : IsReductive G) (hi : IsRelativeParabolicSubgroup i)
    (hr : IsRelativeUnipotentRadical r) (hl : IsRelativeLeviSubgroup l)
    (hl' : IsRelativeLeviSubgroup l')
    (hex : EtaleLocallyRangeConjugate.{u, v} l l' (Over.mk (𝟙 S))) :
    ∃! n : Over.mk (𝟙 S) ⟶ U.X,
      SubgroupFunctor.range l' =
        SubgroupFunctor.range (l ≫ (P.innerIso (n ≫ r.hom.hom)).hom) :=
  relative_existsUnique_conjugator_of_etaleLocal hRadical hNormalizer
    G P U L L' i r l l' hG hi hr hl hl'
    (relative_etaleLocallyRadicalConjugate_of_range hRadical
      G P U L L' i r l l' hG hi hr hl _ hex)

end Langlands.GroupScheme.RelativeLevi
