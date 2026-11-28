import Langlands.Geometry.Analytic.FiniteEtaleAffinoidQuotient
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteTensorComparison.Proof
import Langlands.Geometry.Analytic.SmallAffinoidLocalizedMaps
import Mathlib.Algebra.Category.Ring.Constructions

/-! # Ordinary ring relations from finite affinoid kernel pairs -/

noncomputable section

universe u v

namespace Langlands.Analytic.SmallAffinoidSpectrum

open _root_.CategoryTheory _root_.CategoryTheory.Limits Set
open PresentedAffinoidAlgebra SaturatedAtlasPresentation
open PresentedAffinoidAlgebra.AffinoidPushout

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

private abbrev ringMap {A B : PresentedAffinoidAlgebra K} (f : BoundedAlgHom K A B) :
    CommRingCat.of A ⟶ CommRingCat.of B :=
  CommRingCat.ofHom f.toAlgHom.toRingHom

/-- The bounded affinoid pushout along a finite Banach first map
is the pushout of the underlying commutative rings. -/
theorem ring_isPushout_of_finiteBanach {A B C : PresentedAffinoidAlgebra K}
    (f : BoundedAlgHom K A B) (g : BoundedAlgHom K A C) (hf : f.IsFiniteBanach) :
    IsPushout (ringMap f) (ringMap g) (ringMap (leftMap f g)) (ringMap (rightMap f g)) := by
  let : Algebra A B := f.toAlgHom.toRingHom.toAlgebra
  let : Algebra A C := g.toAlgHom.toRingHom.toAlgebra
  let e := RingEquiv.ofBijective (tensorComparison f g) (tensorComparison_bijective f g hf)
  exact (CommRingCat.isPushout_tensorProduct A C B).flip.of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) e.toCommRingCatIso rfl rfl
    (CommRingCat.hom_ext (RingHom.ext fun b => tensorComparison_tensorRight f g b))
    (CommRingCat.hom_ext (RingHom.ext fun c => tensorComparison_tensorLeft f g c))

private abbrev localizedSpectrum (A : PresentedAffinoidAlgebra K) [Small.{v} (BanachSpectrum A)] :
    LocalizedCategory.{u, v, v} (K := K) :=
  localizationFunctor.obj (saturated.{u, v} A)

private abbrev spectrumMap {A B : PresentedAffinoidAlgebra K}
    [Small.{v} (BanachSpectrum A)] [Small.{v} (BanachSpectrum B)] (f : BoundedAlgHom K A B) :
    localizedSpectrum.{u, v} B ⟶ localizedSpectrum.{u, v} A :=
  localizedMapEquiv.{u, v} A B f

section Relation

variable {B C : PresentedAffinoidAlgebra K} [Small.{v} (BanachSpectrum B)]
  [Small.{v} (BanachSpectrum C)] {H : LocalizedCategory.{u, v, v} (K := K)}
  {q : localizedSpectrum.{u, v} B ⟶ H} {s t : BoundedAlgHom K B C}
  (h : IsPullback (spectrumMap.{u, v} s) (spectrumMap.{u, v} t) q q)

include h

private theorem exists_bounded_lift_of_kernelPair {D : PresentedAffinoidAlgebra K}
    [Small.{v} (BanachSpectrum D)] (a b : BoundedAlgHom K B D)
    (hw : spectrumMap.{u, v} a ≫ q = spectrumMap.{u, v} b ≫ q) :
    ∃ c : BoundedAlgHom K C D, c.comp s = a ∧ c.comp t = b := by
  obtain ⟨c, hc⟩ := (localizedMapEquiv.{u, v} C D).surjective (h.lift _ _ hw)
  refine ⟨c, (localizedMapEquiv.{u, v} B D).injective ?_,
    (localizedMapEquiv.{u, v} B D).injective ?_⟩
  · rw [localizedMapEquiv_comp, hc, h.lift_fst]
  · rw [localizedMapEquiv_comp, hc, h.lift_snd]

/-- A localized kernel pair with affinoid projections and a finite Banach
second coefficient map induces an equivalence relation on ordinary ring maps. -/
theorem ringEquivalence_of_localizedKernelPair (ht : t.IsFiniteBanach)
    (T : Type u) [CommRing T] :
    _root_.Equivalence fun a b : B →+* T => ∃ d : C →+* T,
      d.comp s.toAlgHom.toRingHom = a ∧ d.comp t.toAlgHom.toRingHom = b := by
  constructor
  · intro a
    obtain ⟨i, hi₁, hi₂⟩ := exists_bounded_lift_of_kernelPair h
      (BoundedAlgHom.id K B) (BoundedAlgHom.id K B) rfl
    refine ⟨a.comp i.toAlgHom.toRingHom, ?_, ?_⟩
    · rw [RingHom.comp_assoc, show i.toAlgHom.toRingHom.comp s.toAlgHom.toRingHom =
        RingHom.id B from
        congrArg (fun f : BoundedAlgHom K B B => f.toAlgHom.toRingHom) hi₁, RingHom.comp_id]
    · rw [RingHom.comp_assoc, show i.toAlgHom.toRingHom.comp t.toAlgHom.toRingHom =
        RingHom.id B from
        congrArg (fun f : BoundedAlgHom K B B => f.toAlgHom.toRingHom) hi₂, RingHom.comp_id]
  · rintro a b ⟨d, hds, hdt⟩
    obtain ⟨i, hi₁, hi₂⟩ := exists_bounded_lift_of_kernelPair h t s h.w.symm
    refine ⟨d.comp i.toAlgHom.toRingHom, ?_, ?_⟩
    · rw [RingHom.comp_assoc, show i.toAlgHom.toRingHom.comp s.toAlgHom.toRingHom = _ from
        congrArg (fun f : BoundedAlgHom K B C => f.toAlgHom.toRingHom) hi₁, hdt]
    · rw [RingHom.comp_assoc, show i.toAlgHom.toRingHom.comp t.toAlgHom.toRingHom = _ from
        congrArg (fun f : BoundedAlgHom K B C => f.toAlgHom.toRingHom) hi₂, hds]
  · rintro a b c ⟨d, hds, hdt⟩ ⟨e, hes, het⟩
    let D := algebra t s
    let : Small.{v} (BanachSpectrum D) :=
      small_spectrum_of_finiteBanachPushout t s finiteBanachPushout ht
    let l := leftMap t s
    let r := rightMap t s
    have hmiddle : spectrumMap.{u, v} l ≫ spectrumMap.{u, v} t =
        spectrumMap.{u, v} r ≫ spectrumMap.{u, v} s := by
      exact ((localizedMapEquiv_comp.{u, v} t l).symm.trans
        (congrArg (localizedMapEquiv.{u, v} B D) (condition t s))).trans
          (localizedMapEquiv_comp.{u, v} s r)
    have hw : spectrumMap.{u, v} (l.comp s) ≫ q = spectrumMap.{u, v} (r.comp t) ≫ q := by
      change localizedMapEquiv.{u, v} B D (l.comp s) ≫ q =
        localizedMapEquiv.{u, v} B D (r.comp t) ≫ q
      rw [localizedMapEquiv_comp, localizedMapEquiv_comp, Category.assoc, Category.assoc,
        h.w, ← Category.assoc, hmiddle, Category.assoc, h.w]
    obtain ⟨i, hi₁, hi₂⟩ := exists_bounded_lift_of_kernelPair h (l.comp s) (r.comp t) hw
    have hRing := ring_isPushout_of_finiteBanach t s ht
    have heq : ringMap t ≫ CommRingCat.ofHom d = ringMap s ≫ CommRingCat.ofHom e :=
      CommRingCat.hom_ext (hdt.trans hes.symm)
    let m := hRing.desc (CommRingCat.ofHom d) (CommRingCat.ofHom e) heq
    have hl : m.hom.comp l.toAlgHom.toRingHom = d :=
      congrArg CommRingCat.Hom.hom (hRing.inl_desc _ _ heq)
    have hr : m.hom.comp r.toAlgHom.toRingHom = e :=
      congrArg CommRingCat.Hom.hom (hRing.inr_desc _ _ heq)
    refine ⟨m.hom.comp i.toAlgHom.toRingHom, ?_, ?_⟩
    · rw [RingHom.comp_assoc, show i.toAlgHom.toRingHom.comp s.toAlgHom.toRingHom =
        l.toAlgHom.toRingHom.comp s.toAlgHom.toRingHom from
          congrArg (fun f : BoundedAlgHom K B D => f.toAlgHom.toRingHom) hi₁,
        ← RingHom.comp_assoc, hl, hds]
    · rw [RingHom.comp_assoc, show i.toAlgHom.toRingHom.comp t.toAlgHom.toRingHom =
        r.toAlgHom.toRingHom.comp t.toAlgHom.toRingHom from
          congrArg (fun f : BoundedAlgHom K B D => f.toAlgHom.toRingHom) hi₂,
        ← RingHom.comp_assoc, hr, het]

end Relation

section Quotient

variable {A B C : PresentedAffinoidAlgebra K}

/-- The two factor maps of a finite Banach affinoid pushout generate any
surjective bounded quotient of the pushout as a ring. -/
theorem range_sup_of_quotient_pushout {D : PresentedAffinoidAlgebra K}
    (f : BoundedAlgHom K A B) (g : BoundedAlgHom K A C) (hf : f.IsFiniteBanach)
    (j : BoundedAlgHom K (algebra f g) D) (hj : Function.Surjective j) :
    (j.comp (leftMap f g)).toAlgHom.toRingHom.range ⊔
      (j.comp (rightMap f g)).toAlgHom.toRingHom.range = ⊤ := by
  have h := CommRingCat.closure_range_union_range_eq_top_of_isPushout
    (ring_isPushout_of_finiteBanach f g hf)
  change Subring.closure
    (range (leftMap f g).toAlgHom.toRingHom ∪ range (rightMap f g).toAlgHom.toRingHom) = ⊤ at h
  rw [← RingHom.coe_range, ← RingHom.coe_range, Subring.closure_union,
    Subring.closure_eq, Subring.closure_eq] at h
  have hm := congrArg (fun S : Subring (algebra f g) => S.map j.toAlgHom.toRingHom) h
  rw [Subring.map_sup, RingHom.map_range, RingHom.map_range] at hm
  refine hm.trans (top_unique ?_)
  intro x _
  obtain ⟨y, rfl⟩ := hj x
  exact ⟨y, Subring.mem_top _, rfl⟩

variable [Small.{v} (BanachSpectrum A)] [Small.{v} (BanachSpectrum B)]
  [Small.{v} (BanachSpectrum C)] {H : LocalizedCategory.{u, v, v} (K := K)}
  {s t : BoundedAlgHom K B C} {q : localizedSpectrum.{u, v} B ⟶ H}

/-- Construct the finite étale affinoid quotient attached to a localized
kernel pair presented by finite étale affinoid maps over a finite base. -/
def finiteEtaleAffinoidQuotientOfLocalizedKernelPair
    (h : IsPullback (spectrumMap.{u, v} s) (spectrumMap.{u, v} t) q q)
    (f : BoundedAlgHom K A B) (hf : f.IsFiniteBanach) (he : f.AlgebraicallyFiniteEtale)
    (hs : s.AlgebraicallyFiniteEtale) (ht : t.AlgebraicallyFiniteEtale)
    (htBanach : t.IsFiniteBanach)
    (g : H ⟶ localizedSpectrum.{u, v} A) (hg : q ≫ g = spectrumMap.{u, v} f)
    (hgen : s.toAlgHom.toRingHom.range ⊔ t.toAlgHom.toRingHom.range = ⊤) :
    {Q : FiniteBanachEtaleAffinoidQuotient f s t //
      Q.baseMap.IsFiniteBanach ∧ Q.coverMap.IsFiniteBanach} := by
  have hw : s.comp f = t.comp f := by
    apply (localizedMapEquiv.{u, v} A C).injective
    change localizedMapEquiv.{u, v} A C (s.comp f) = localizedMapEquiv.{u, v} A C (t.comp f)
    rw [localizedMapEquiv_comp, localizedMapEquiv_comp]
    change spectrumMap.{u, v} s ≫ spectrumMap.{u, v} f =
      spectrumMap.{u, v} t ≫ spectrumMap.{u, v} f
    rw [← hg, ← Category.assoc, ← Category.assoc, h.w]
  exact finiteEtaleAffinoidQuotientOfFiniteBanach f s t hf he hs ht hw hgen
    (ringEquivalence_of_localizedKernelPair h htBanach)

end Quotient

end Langlands.Analytic.SmallAffinoidSpectrum
