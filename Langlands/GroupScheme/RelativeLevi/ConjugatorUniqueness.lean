import Langlands.GroupScheme.Rational.LeviRetraction
import Langlands.GroupScheme.Rational.ParabolicAmbientTransport
import Langlands.GroupScheme.Absolute.ParabolicNormalizerPointsReduction
import Langlands.GroupScheme.RelativeLevi.ConjugacyStatement
import Langlands.GroupScheme.RelativeLevi.SelfNormalizerStatement
import Langlands.GroupScheme.RelativeLevi.UnipotentRadicalStatement

/-! # Uniqueness of unipotent conjugators from self-normalization -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeLevi

variable {S : Scheme.{u}} {P L U V : GroupScheme S}

/-- The all-test image of `l`, conjugated by the image of a base point of `U`. -/
def radicalConjugate (l : L ⟶ P) (r : U ⟶ P)
    (u : Over.mk (𝟙 S) ⟶ U.X) : SubgroupFunctor P :=
  SubgroupFunctor.range (l ≫ (P.innerIso (u ≫ r.hom.hom)).hom)

/-- Equal conjugate images imply that the quotient of the conjugating points
normalizes the original subgroup on every test scheme. -/
theorem inv_mul_mem_normalizer_of_conjugate_range_eq (l : L ⟶ P)
    [Mono l.hom.hom] {g h : Over.mk (𝟙 S) ⟶ P.X}
    (heq : SubgroupFunctor.range (l ≫ (P.innerIso g).hom) =
      SubgroupFunctor.range (l ≫ (P.innerIso h).hom)) :
    h⁻¹ * g ∈ (SubgroupFunctor.range l).normalizer.carrier (Over.mk (𝟙 S)) := by
  have hstable : SubgroupFunctor.range (l ≫ (P.innerIso (h⁻¹ * g)).hom) =
      SubgroupFunctor.range l := by
    have ht := (SubgroupFunctor.range_comp_iso_eq_iff _ _ (P.innerIso h).symm).mpr heq
    simpa only [innerIso_mul_hom, innerIso_inv_hom, Iso.symm_hom, Category.assoc,
      Iso.hom_inv_id, Category.comp_id] using ht
  have : IsIso (P.innerIso (h⁻¹ * g)).hom.hom.hom :=
    inferInstanceAs (IsIso ((Grp.forget (Over S)).mapIso (P.innerIso (h⁻¹ * g))).hom)
  have hl : (SubgroupFunctor.range l).IsRepresentedBy l := ⟨inferInstance, rfl⟩
  have hc : (SubgroupFunctor.range l).IsRepresentedBy
      (l ≫ (P.innerIso (h⁻¹ * g)).hom) :=
    ⟨by rw [Grp.comp_hom_hom]; infer_instance, hstable⟩
  let e := hc.isoOfIsRepresentedBy hl
  exact SubgroupFunctor.mem_normalizer_range_of_innerIso e
    (SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp hc hl).symm

/-- The two factors of a subgroup multiplication isomorphism meet only at the
identity, on any test scheme. -/
theorem eq_one_of_mem_both_ranges (l : L ⟶ P) (s : V ⟶ P)
    [IsIso (subgroupMultiplication l s)] {T : Over S} {x : T ⟶ P.X}
    (hl : x ∈ (SubgroupFunctor.range l).carrier T)
    (hs : x ∈ (SubgroupFunctor.range s).carrier T) : x = 1 := by
  obtain ⟨a, ha⟩ := SubgroupFunctor.mem_range.mp hl
  obtain ⟨n, hn⟩ := SubgroupFunctor.mem_range.mp hs
  have haone : a = 1 := by
    calc
      a = leviComponent l s (a ≫ l.hom.hom) := (leviComponent_comp_levi l s a).symm
      _ = leviComponent l s (n ≫ s.hom.hom) := congrArg (leviComponent l s) (ha.trans hn.symm)
      _ = 1 := leviComponent_comp_radical l s n
  rw [← ha, haone, MonObj.one_comp]

/-- A multiplication decomposition and self-normalization make the radical
conjugation map injective. The acting subgroup may be any monic subgroup
contained in the supplied second factor. -/
theorem radicalConjugate_injective_of_range_le (l : L ⟶ P) (r : U ⟶ P) (s : V ⟶ P)
    [Mono l.hom.hom] [Mono r.hom.hom] [IsIso (subgroupMultiplication l s)]
    (hrs : SubgroupFunctor.range r ≤ SubgroupFunctor.range s)
    (hN : (SubgroupFunctor.range l).normalizer ≤ SubgroupFunctor.range l) :
    Function.Injective (radicalConjugate l r) := by
  intro u v heq
  have hn := inv_mul_mem_normalizer_of_conjugate_range_eq l heq
  have hnr : (v ≫ r.hom.hom)⁻¹ * (u ≫ r.hom.hom) ∈
      (SubgroupFunctor.range r).carrier (Over.mk (𝟙 S)) := by
    apply SubgroupFunctor.mem_range.mpr
    refine ⟨v⁻¹ * u, ?_⟩
    rw [MonObj.mul_comp, GrpObj.inv_comp]
  have he : (v ≫ r.hom.hom)⁻¹ * (u ≫ r.hom.hom) = 1 :=
    eq_one_of_mem_both_ranges l s (hN _ hn) (hrs _ hnr)
  apply (cancel_mono r.hom.hom).mp
  exact (inv_mul_eq_one.mp he).symm

/-- In particular the specified second factor acts with at most one conjugator. -/
theorem radicalConjugate_injective (l : L ⟶ P) (r : U ⟶ P)
    [Mono l.hom.hom] [Mono r.hom.hom] [IsIso (subgroupMultiplication l r)]
    (hN : (SubgroupFunctor.range l).normalizer = SubgroupFunctor.range l) :
    Function.Injective (radicalConjugate l r) :=
  radicalConjugate_injective_of_range_le l r r le_rfl hN.le

/-- Under relative radical uniqueness and relative Levi self-normalization,
the radical conjugation map for a given relative Levi is injective. These two
geometric statements remain explicit hypotheses. -/
theorem relative_radicalConjugate_injective
    (hRadical : RelativeUnipotentRadicalStatement.{u})
    (hNormalizer : RelativeLeviSelfNormalizerStatement.{u})
    (G P U L : GroupScheme S) (i : P ⟶ G) (r : U ⟶ P) (l : L ⟶ P)
    (hG : IsReductive G) (hi : IsRelativeParabolicSubgroup i)
    (hr : IsRelativeUnipotentRadical r) (hl : IsRelativeLeviSubgroup l) :
    Function.Injective (radicalConjugate l r) := by
  obtain ⟨V, s, hs, hmul⟩ := hl.exists_unipotentRadical
  obtain ⟨W, t, _, ht⟩ := hRadical S G P i hG hi
  have hrs : SubgroupFunctor.range r ≤ SubgroupFunctor.range s :=
    ((ht U r hr).trans (ht V s hs).symm).le
  let : IsClosedImmersion l.hom.hom.left := hl.isClosedSubgroup
  let : IsClosedImmersion r.hom.hom.left := hr.isClosedSubgroup
  let : Mono l.hom.hom := Over.mono_of_mono_left _
  let : Mono r.hom.hom := Over.mono_of_mono_left _
  let : IsIso (subgroupMultiplication l s) := hmul
  exact radicalConjugate_injective_of_range_le l r s hrs (hNormalizer S G P L i l hG hi hl).le

/-- The supplied geometric statements reduce unique relative Levi conjugacy
to existence of a conjugating point. -/
theorem existsUnique_conjugator_iff_exists
    (hRadical : RelativeUnipotentRadicalStatement.{u})
    (hNormalizer : RelativeLeviSelfNormalizerStatement.{u})
    (G P U L L' : GroupScheme S) (i : P ⟶ G) (r : U ⟶ P)
    (l : L ⟶ P) (l' : L' ⟶ P)
    (hG : IsReductive G) (hi : IsRelativeParabolicSubgroup i)
    (hr : IsRelativeUnipotentRadical r) (hl : IsRelativeLeviSubgroup l) :
    (∃! u : Over.mk (𝟙 S) ⟶ U.X,
      SubgroupFunctor.range l' = radicalConjugate l r u) ↔
    ∃ u : Over.mk (𝟙 S) ⟶ U.X,
      SubgroupFunctor.range l' = radicalConjugate l r u := by
  constructor
  · exact ExistsUnique.exists
  · rintro ⟨u, hu⟩
    refine ⟨u, hu, fun v hv => ?_⟩
    exact relative_radicalConjugate_injective hRadical hNormalizer G P U L i r l hG hi hr hl
      (hv.symm.trans hu)

end Langlands.GroupScheme.RelativeLevi
