import Mathlib.RingTheory.HopkinsLevitzki
import Langlands.GroupScheme.Derived.CenterReduction
import Langlands.GroupScheme.HomScheme.CentralAdmissibleArtinian
import Langlands.GroupScheme.HomScheme.ChartCoverTransport
import Langlands.GroupScheme.Rational.TorusCentralizerFactorization
import Langlands.GroupScheme.Reductive.NilIdealHomIsomorphism
import Langlands.GroupScheme.SubgroupFunctor.CentralizerBaseChange
import Langlands.GroupScheme.SubgroupFunctor.OpenEquality
import Langlands.GroupScheme.Torus.RelativeCentralizerDescent
import Langlands.GroupScheme.Torus.RelativeCommutativity

/-! # Recognizing and lifting torus centralizers over local nilpotent quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.TorusSubgroupModuli

open SubgroupFunctor

section Quotients

variable {A : Type u} [CommRing A] (I : Ideal A)

local notation "S" => Spec (CommRingCat.of A)
local notation "q" => Spec.algebraMap A (A ⧸ I)
local notation "Q" => baseChange q

private theorem range_centralizer_baseChange {G T C : GroupScheme S}
    (t : T ⟶ G) (c : C ⟶ G) (hc : range c = (range t).centralizer) :
    range ((Q).map c) = (range ((Q).map t)).centralizer := by
  rw [range_baseChangeHom, range_baseChangeHom, hc, SubgroupFunctor.centralizer_baseChange]

variable [IsLocalRing A]

/-- A smooth closed subgroup of an affine smooth group over a local ring is
an actual torus centralizer if its reduction modulo a nilpotent ideal is one.
The witnessing closed torus can be chosen to lift the given torus over the quotient. -/
theorem exists_torus_of_isCentralizer_quotient (hI : IsNilpotent I)
    {G H : GroupScheme S} [Smooth G.X.hom] [IsAffineHom G.X.hom] [Smooth H.X.hom]
    (i : H ⟶ G) (hi : IsClosedSubgroup i)
    {T₀ : GroupScheme (Spec (CommRingCat.of (A ⧸ I)))} (t₀ : T₀ ⟶ (Q).obj G)
    (ht₀ : IsClosedSubgroup t₀) (hT₀ : RelativeTorus.IsTorus T₀)
    (he : range ((Q).map i) = (range t₀).centralizer) :
    ∃ (T : GroupScheme S) (t : T ⟶ G), IsClosedSubgroup t ∧ RelativeTorus.IsTorus T ∧
      range ((Q).map t) = range t₀ ∧ range i = (range t).centralizer := by
  have hi₀ : IsClosedImmersion ((Q).map i).hom.hom.left := hi.baseChange q
  let B := hT₀.commGroupScheme
  let b : B.toGrp ⟶ (Q).obj G := t₀
  have hr : (torusCentralizer b).IsRepresentedBy ((Q).map i) := by
    refine ⟨Over.mono_of_mono_left _, ?_⟩
    rw [torusCentralizer_eq_centralizer_range]
    exact he
  let s := torusCentralizerFactor b hr
  have hs : IsClosedSubgroup s := isClosedSubgroup_torusCentralizerFactor b hr hi₀ ht₀
  have hsc : IsCentral s := isCentral_torusCentralizerFactor b hr
  have : IsClosedImmersion i.hom.hom.left := hi
  have : IsAffineHom H.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  obtain ⟨T, k, hk, hT, hred⟩ := exists_closedTorus_lift_of_affine I hI H (range s)
    (isAdmissible_range s hs hT₀)
  have hk₀ : IsCentral ((Q).map k) := by
    rw [isCentral_iff_range_le_center, hred]
    exact (isCentral_iff_range_le_center s).mp hsc
  have hkc := NilpotentConjugation.isCentral_of_isMultiplicativeType hT.isMultiplicativeType k I hI hk₀
  let t := k ≫ i
  have ht : IsClosedSubgroup t := by
    have : IsClosedImmersion k.hom.hom.left := hk
    change IsClosedImmersion (k.hom.hom.left ≫ i.hom.hom.left)
    infer_instance
  have htr : range ((Q).map t) = range t₀ := by
    change range ((Q).map (k ≫ i)) = range b
    rw [Functor.map_comp, range_postcomp_congr _ s _ hred, torusCentralizerFactor_comp]
  refine ⟨T, t, ht, hT, htr, ?_⟩
  let D := hT.commGroupScheme
  let d : D.toGrp ⟶ G := t
  obtain ⟨C, c, hclosed, hC, hc⟩ :=
    relativeTorusCentralizer_hasSmoothClosedRepresentative d hT (by infer_instance)
  have hcr : range c = (range t).centralizer := hc.2.trans (torusCentralizer_eq_centralizer_range d)
  have htop : (⊤ : SubgroupFunctor H) ≤ (range k).centralizer := by
    rw [le_centralizer_iff, centralizer_top]
    exact (isCentral_iff_range_le_center k).mp hkc
  have hle : range i ≤ range c := by
    rw [hcr]
    intro U x hx
    obtain ⟨y, rfl⟩ := hx
    have hy : y ∈ (⊤ : SubgroupFunctor H).carrier U := trivial
    exact centralizer_range_le_comap k i U (htop U hy)
  have : IsClosedImmersion c.hom.hom.left := hclosed
  let f := rangeFactor i c hle
  have hf : f ≫ c = i := rangeFactor_comp i c hle
  have hf₀ : (Q).map f ≫ (Q).map c = (Q).map i := by rw [← Functor.map_comp, hf]
  have : IsClosedImmersion ((Q).map c).hom.hom.left := hclosed.baseChange q
  have : Mono ((Q).map i).hom.hom := Over.mono_of_mono_left _
  have : Mono ((Q).map c).hom.hom := Over.mono_of_mono_left _
  have he₀ : range ((Q).map i) = range ((Q).map c) := by
    rw [range_centralizer_baseChange I t c hcr, htr, he]
  have hIso₀ : IsIso ((Q).map f) := isIso_factor_of_range_eq _ _ _ hf₀ he₀
  have hnil : I ≤ nilradical A := by
    obtain ⟨n, hn⟩ := hI
    intro x hx
    exact mem_nilradical.mpr ⟨n, by
      have hp := Ideal.pow_mem_pow hx n
      rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at hp
      exact hp⟩
  let : Smooth C.X.hom := hC
  have : IsIso f := isIso_of_nilIdeal_baseChange A I hnil f hIso₀
  rw [← hf]
  exact (range_iso_comp (asIso f) c).trans hcr

/-- The centralizer of a closed torus over a local nilpotent quotient of an
affine smooth group lifts to a smooth closed centralizer in the group. -/
theorem exists_centralizer_lift_of_quotient (hI : IsNilpotent I)
    (G : GroupScheme S) [Smooth G.X.hom] [IsAffineHom G.X.hom]
    {T₀ : GroupScheme (Spec (CommRingCat.of (A ⧸ I)))} (t₀ : T₀ ⟶ (Q).obj G)
    (ht₀ : IsClosedSubgroup t₀) (hT₀ : RelativeTorus.IsTorus T₀) :
    ∃ (T : GroupScheme S) (t : T ⟶ G) (C : GroupScheme S) (c : C ⟶ G),
      IsClosedSubgroup t ∧ RelativeTorus.IsTorus T ∧ IsClosedSubgroup c ∧ Smooth C.X.hom ∧
        range ((Q).map t) = range t₀ ∧ range c = (range t).centralizer ∧
        range ((Q).map c) = (range t₀).centralizer := by
  obtain ⟨T, t, ht, hT, hred⟩ := exists_closedTorus_lift_of_affine I hI G (range t₀)
    (isAdmissible_range t₀ ht₀ hT₀)
  let B := hT.commGroupScheme
  let b : B.toGrp ⟶ G := t
  obtain ⟨C, c, hclosed, hC, hc⟩ :=
    relativeTorusCentralizer_hasSmoothClosedRepresentative b hT (by infer_instance)
  have hcr : range c = (range t).centralizer := hc.2.trans (torusCentralizer_eq_centralizer_range b)
  exact ⟨T, t, C, c, ht, hT, hclosed, hC, hred, hcr,
    (range_centralizer_baseChange I t c hcr).trans (congrArg centralizer hred)⟩

/-- On a local Artinian base it suffices to identify the subgroup on the closed fibre. -/
theorem exists_torus_of_isCentralizer_closedFiber [IsArtinianRing A]
    {G H : GroupScheme S} [Smooth G.X.hom] [IsAffineHom G.X.hom] [Smooth H.X.hom]
    (i : H ⟶ G) (hi : IsClosedSubgroup i)
    {T₀ : GroupScheme (Spec (CommRingCat.of (A ⧸ IsLocalRing.maximalIdeal A)))}
    (t₀ : T₀ ⟶ (baseChange (Spec.algebraMap A (A ⧸ IsLocalRing.maximalIdeal A))).obj G)
    (ht₀ : IsClosedSubgroup t₀) (hT₀ : RelativeTorus.IsTorus T₀)
    (he : range ((baseChange (Spec.algebraMap A (A ⧸ IsLocalRing.maximalIdeal A))).map i) =
      (range t₀).centralizer) :
    ∃ (T : GroupScheme S) (t : T ⟶ G), IsClosedSubgroup t ∧ RelativeTorus.IsTorus T ∧
      range i = (range t).centralizer := by
  obtain ⟨T, t, ht, hT, _, h⟩ := exists_torus_of_isCentralizer_quotient
    (IsLocalRing.maximalIdeal A) ((isArtinianRing_iff_isNilpotent_maximalIdeal A).mp inferInstance)
    i hi t₀ ht₀ hT₀ he
  exact ⟨T, t, ht, hT, h⟩

end Quotients

/-- Recognition and lifting of actual torus centralizers over local nilpotent quotients. -/
def LocalNilpotentTorusCentralizersStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] (I : Ideal A), IsNilpotent I →
    let S := Spec (CommRingCat.of A)
    let S₀ := Spec (CommRingCat.of (A ⧸ I))
    let Q := baseChange (Spec.algebraMap A (A ⧸ I))
    ∀ (G : GroupScheme S) [Smooth G.X.hom] [IsAffineHom G.X.hom]
      (T₀ : GroupScheme S₀) (t₀ : T₀ ⟶ Q.obj G),
      IsClosedSubgroup t₀ → RelativeTorus.IsTorus T₀ →
      (∀ (H : GroupScheme S) [Smooth H.X.hom] (i : H ⟶ G),
        IsClosedSubgroup i → range (Q.map i) = (range t₀).centralizer →
        ∃ (T : GroupScheme S) (t : T ⟶ G), IsClosedSubgroup t ∧ RelativeTorus.IsTorus T ∧
          range (Q.map t) = range t₀ ∧ range i = (range t).centralizer) ∧
      (∃ (T : GroupScheme S) (t : T ⟶ G) (C : GroupScheme S) (c : C ⟶ G),
        IsClosedSubgroup t ∧ RelativeTorus.IsTorus T ∧ IsClosedSubgroup c ∧ Smooth C.X.hom ∧
          range (Q.map t) = range t₀ ∧ range c = (range t).centralizer ∧
          range (Q.map c) = (range t₀).centralizer)

theorem localNilpotentTorusCentralizers : LocalNilpotentTorusCentralizersStatement.{u} := by
  intro A _ _ I hI S S₀ Q G _ _ T₀ t₀ ht₀ hT₀
  exact ⟨fun _ _ i hi he => exists_torus_of_isCentralizer_quotient I hI i hi t₀ ht₀ hT₀ he,
    exists_centralizer_lift_of_quotient I hI G t₀ ht₀ hT₀⟩

end Langlands.GroupScheme.TorusSubgroupModuli
