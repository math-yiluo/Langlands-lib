import Langlands.AlgebraicGeometry.ArtinianLiftingSmooth
import Langlands.AlgebraicGeometry.GeometricIrreducibilityAffine
import Langlands.AlgebraicGeometry.UnramifiedFunctor.ArtinianNilpotentLifting
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCriterion

/-! # Murre's separated étale representability criterion -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry Opposite IsLocalRing
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

open GenericLift (rhom)

/-- Separated étale representability over a locally noetherian base, with
infinitesimal étaleness tested on local Artinian rings. -/
def MurreEtaleCriterionStatement : Prop :=
  ∀ (S : Scheme.{u}) [IsLocallyNoetherian S] (F : (Over S)ᵒᵖ ⥤ Type v),
    SmallValues F → ZariskiSheaf F → FaithfullyFlatSheaf F → FilteredColimits F →
    AdicLimits F → ValuativeSeparation F → ArtinianNilpotentBijective F →
    ∃ (Y : Scheme.{u}) (q : Y ⟶ S),
      Nonempty (F.RepresentableBy (Over.mk q)) ∧ IsSeparated q ∧ Etale q

variable {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type v}

private lemma artinianLifting_of_bijective (hN : ArtinianNilpotentBijective F) :
    ArtinianLifting F := by
  intro A _ _ _ f A' _ _ _ _ ξ _ _
  have hnil : IsNilpotent (maximalIdeal A) :=
    (isArtinianRing_iff_isNilpotent_maximalIdeal A).mp inferInstance
  exact (hN.quotient _ hnil f).2 ξ

private lemma liftsTo_artinian (hN : ArtinianNilpotentBijective F)
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing B] [IsArtinianRing B]
    {I : Ideal A} (hI : IsNilpotent I) {f : Spec (CommRingCat.of A) ⟶ S}
    (ξ : F.obj (op (algebraOver f (A ⧸ I)))) :
    LiftsTo B ξ := by
  let J := I.map (algebraMap A B)
  have hn : IsNilpotent J := by
    obtain ⟨n, hn⟩ := hI
    exact ⟨n, by simp only [J, ← Ideal.map_pow, hn, Ideal.zero_eq_bot, Ideal.map_bot]⟩
  let a := algHomOver f (Ideal.Quotient.mkₐ A J)
  have ha : Function.Bijective (F.map a.op) :=
    hN B (B ⧸ J) (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
      (by rwa [Ideal.mk_ker]) (algebraOver f B).hom (algebraOver f (B ⧸ J)).hom a.w
  exact ha.2 (restrictQuotient B ξ)

private lemma map_eq_bot_of_noLargerLift {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {I : Ideal A} {f : Spec (CommRingCat.of A) ⟶ S} {ξ : F.obj (op (algebraOver f (A ⧸ I)))}
    (h : LiftsTo B ξ) (hno : NoLargerLift B ξ) :
    I.map (algebraMap A B) = ⊥ := by
  by_contra hne
  let J := I.map (algebraMap A B)
  have hj : (⊥ : Ideal B) < J := bot_lt_iff_ne_bot.mpr hne
  obtain ⟨x, hx⟩ := h
  let a := algHomOver f (Ideal.Quotient.mkₐ A (⊥ : Ideal B))
  let b := algHomOver f (Ideal.Quotient.factorₐ A hj.le)
  have hab : b ≫ a = algHomOver f (Ideal.Quotient.mkₐ A J) := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hj.le)) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (⊥ : Ideal B))) = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.factor_comp_mk]
    rfl
  apply hno ⊥ hj (F.map a.op x)
  change F.map b.op (F.map a.op x) = _
  rw [← Functor.map_comp_apply, ← op_comp, hab]
  exact hx

private lemma genericLocalization_isArtinian {A : Type u} [CommRing A] [IsNoetherianRing A]
    {t : PrimeSpectrum A} (ht : IsGenericPoint t Set.univ) :
    IsArtinianRing (Localization.AtPrime t.asIdeal) := by
  let B := Localization.AtPrime t.asIdeal
  have ht' := SchemeFiberGeometry.asIdeal_eq_nilradical_of_isGenericPoint ht
  have hmax : maximalIdeal B = nilradical B := by
    refine le_antisymm ?_ (nilradical_le_prime _)
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.map_le_iff_le_comap.mpr fun x hx =>
      (mem_nilradical.mp (ht' ▸ hx)).map (algebraMap A B)
  have : (nilradical B).IsMaximal := hmax ▸ maximalIdeal.isMaximal B
  have : Ring.KrullDimLE 0 B := Ring.KrullDimLE.of_isMaximal_nilradical B
  exact IsNoetherianRing.isArtinianRing_of_krullDimLE_zero

private theorem exists_basicOpen_map_eq_bot {A : Type u} [CommRing A] [IsNoetherianRing A]
    (t : PrimeSpectrum A) (I : Ideal A)
    (h : I.map (algebraMap A (Localization.AtPrime t.asIdeal)) = ⊥) :
    ∃ g₀ : A, t ∈ PrimeSpectrum.basicOpen g₀ ∧
      ∀ g, PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen g₀ →
        I.map (algebraMap A (Localization.Away g)) = ⊥ := by
  classical
  let B := Localization.AtPrime t.asIdeal
  obtain ⟨s, hs⟩ := I.fg_of_isNoetherianRing
  change Ideal.span (↑s : Set A) = I at hs
  have hsmall : I ≤ RingHom.ker (algebraMap A B) :=
    (Ideal.map_eq_bot_iff_le_ker _).mp h
  have hann (x : A) (hx : x ∈ s) : ∃ z : t.asIdeal.primeCompl, (z : A) * x = 0 :=
    (IsLocalization.map_eq_zero_iff t.asIdeal.primeCompl B x).mp
      (hsmall (hs ▸ Ideal.subset_span hx))
  choose! z hz using hann
  let g₀ : A := ∏ x ∈ s, (z x : A)
  have hg₀ : g₀ ∈ t.asIdeal.primeCompl := prod_mem fun x _ => (z x).property
  have hkill (x : A) (hx : x ∈ s) : g₀ * x = 0 := by
    obtain ⟨d, hd⟩ : (z x : A) ∣ g₀ := Finset.dvd_prod_of_mem _ hx
    rw [hd, mul_right_comm, hz x hx, zero_mul]
  refine ⟨g₀, hg₀, fun g hg => ?_⟩
  have hu : IsUnit (algebraMap A (Localization.Away g) g₀) :=
    (PrimeSpectrum.basicOpen_le_basicOpen_iff_algebraMap_isUnit
      (S := Localization.Away g)).mp hg
  rw [Ideal.map_eq_bot_iff_le_ker, ← hs, Ideal.span_le]
  intro x hx
  change algebraMap A (Localization.Away g) x = 0
  apply hu.mul_right_injective
  change algebraMap A (Localization.Away g) g₀ * algebraMap A (Localization.Away g) x =
    algebraMap A (Localization.Away g) g₀ * 0
  rw [← map_mul, hkill x hx, map_zero, mul_zero]

private lemma genericNonLifting_of_bijective (hN : ArtinianNilpotentBijective F) :
    GenericNonLifting F := by
  intro A _ _ t ht I hI _ f ξ hno
  have : IsArtinianRing (Localization.AtPrime t.asIdeal) :=
    genericLocalization_isArtinian ht
  have h₀ : I.map (algebraMap A (Localization.AtPrime t.asIdeal)) = ⊥ :=
    map_eq_bot_of_noLargerLift (liftsTo_artinian hN hI ξ) hno
  obtain ⟨g₀, hg₀, hvanish⟩ := exists_basicOpen_map_eq_bot t I h₀
  refine ⟨g₀, ⟨t, hg₀⟩, fun g hg J hJ _ => ?_⟩
  rw [hvanish g hg] at hJ
  exact (not_lt_bot hJ).elim

private lemma smooth_of_representableBy [IsLocallyNoetherian S]
    (hN : ArtinianNilpotentBijective F) {Y : Scheme.{u}} {q : Y ⟶ S}
    [LocallyOfFiniteType q] (e : F.RepresentableBy (Over.mk q)) : Smooth q := by
  apply ArtinianLiftingSmooth.smooth_of_liftsArtinian
  intro A B _ _ _ _ _ _ φ hφ hK α β w _
  have hle : RingHom.ker φ ≤ maximalIdeal A := le_maximalIdeal (RingHom.ker_ne_top φ)
  have hn : IsNilpotent (RingHom.ker φ) := ⟨2, by
    rw [pow_two, Ideal.zero_eq_bot]
    exact eq_bot_iff.mpr ((Ideal.mul_mono hle le_rfl).trans hK.le)⟩
  let a : Over.mk (α ≫ q) ⟶ Over.mk q := Over.homMk α rfl
  let i : Over.mk (α ≫ q) ⟶ Over.mk β := rhom φ w.symm
  obtain ⟨x, hx⟩ := (hN A B φ hφ hn β (α ≫ q) w.symm).2 (e.homEquiv a)
  let c : Over.mk β ⟶ Over.mk q := e.homEquiv.symm x
  have hc : i ≫ c = a := e.homEquiv.injective ((e.homEquiv_comp i c).trans
    ((congrArg (F.map i.op) (e.homEquiv.apply_symm_apply x)).trans hx))
  exact ⟨c.left, c.w, congrArg (fun f : Over.mk (α ≫ q) ⟶ Over.mk q => f.left) hc⟩

/-- The separated étale criterion follows from the unramified criterion
and lifting along local Artinian nilpotent thickenings. -/
theorem murreEtaleCriterion : MurreEtaleCriterionStatement.{u, v} := by
  intro S _ F hsmall hz hfpqc hfiltered hadic hvaluative hN
  obtain ⟨Y, q, ⟨e⟩, hsep, hft, hfu⟩ := murreCriterion S F hsmall hz hfpqc hfiltered hadic
    (artinianLifting_of_bijective hN)
    (fun _ _ _ _ I hI f => (hN.quotient I hI f).1) hvaluative
    (fun _ _ _ _ _ _ _ _ _ I hI _ f ξ _ =>
      surjective_completeLocalQuotient_of_adicLimits hN hadic I hI f ξ)
    (genericNonLifting_of_bijective hN)
  have : Smooth q := smooth_of_representableBy hN e
  exact ⟨Y, q, ⟨e⟩, hsep, Etale.of_formallyUnramified_of_flat q⟩

end Langlands.AlgebraicGeometry.UnramifiedFunctor
