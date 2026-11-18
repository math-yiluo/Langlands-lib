import Langlands.AlgebraicGeometry.LocalArtinianExhaustion
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Defining-ideal support in the local exhaustion argument -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open Langlands.AlgebraicGeometry.UnramifiedFunctor
open Langlands.AlgebraicGeometry.Modules.AdicStalkQuotient

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry.LocalArtinianExhaustion

variable {X Y T : Scheme.{u}}

/-- An isomorphic pullback supplies a lift of its test morphism. -/
def liftOfPullbackIso (j : Y ⟶ X) (p : T ⟶ X) [IsIso (pullback.snd j p)] : T ⟶ Y :=
  inv (pullback.snd j p) ≫ pullback.fst j p

@[reassoc (attr := simp)] theorem liftOfPullbackIso_fac (j : Y ⟶ X) (p : T ⟶ X)
    [IsIso (pullback.snd j p)] : liftOfPullbackIso j p ≫ j = p := by
  simp only [liftOfPullbackIso, Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]

/-- A kernel ideal is zero on any affine open contained in an open base change
where the morphism is an isomorphism. -/
theorem ker_ideal_eq_bot_of_subset (j : Y ⟶ X) (p : T ⟶ X) [IsOpenImmersion p]
    [IsIso (pullback.snd j p)] (V : X.Opens) (hV : IsAffineOpen V)
    (hVp : V ≤ p.opensRange) : j.ker.ideal ⟨V, hV⟩ = ⊥ := by
  let a : V.toScheme ⟶ Y :=
    IsOpenImmersion.lift p V.ι (by rw [Scheme.Opens.range_ι]; exact hVp) ≫
      liftOfPullbackIso j p
  have ha : a ≫ j = V.ι := by simp [a]
  have hker : j.ker ≤ V.ι.ker := by
    simpa only [ha] using a.le_ker_comp j
  have : IsIso (V.ι.app V) := V.ι.isIso_app V (by simp)
  apply bot_unique
  exact (hker ⟨V, hV⟩).trans ((V.ι.ideal_ker_le ⟨V, hV⟩).trans_eq
    ((RingHom.injective_iff_ker_eq_bot _).mp
      (ConcreteCategory.bijective_of_isIso (V.ι.app V)).1))

/-- Principal opens formed using the actual base action are the expected
intersections with inverse images of base principal opens. -/
theorem basicOpen_baseSectionHom {R : CommRingCat.{u}} (f : X ⟶ Spec R)
    (U : X.Opens) (r : R) :
    X.basicOpen (baseSectionHom f U r) = U ⊓ f ⁻¹ᵁ (PrimeSpectrum.basicOpen r) := by
  change X.basicOpen (f.appLE ⊤ U le_top ((Scheme.ΓSpecIso R).inv r)) = _
  rw [Scheme.basicOpen_appLE, basicOpen_eq_of_affine]

/-- An element of the maximal ideal is invertible only above the punctured base. -/
theorem basicOpen_baseSectionHom_le_punctured {R : CommRingCat.{u}} [IsLocalRing R]
    (f : X ⟶ Spec R) (U : X.Opens) (r : R) (hr : r ∈ maximalIdeal R) :
    X.basicOpen (baseSectionHom f U r) ≤ f ⁻¹ᵁ puncturedSpectrum R := by
  rw [basicOpen_baseSectionHom]
  apply inf_le_right.trans
  apply f.preimage_mono
  intro p hp
  change p ≠ closedPoint R
  rintro rfl
  exact hp hr

/-- The affine defining ideal of a punctured-base isomorphism is supported
on the extended maximal ideal's closed locus. -/
theorem ker_ideal_support_subset {R : CommRingCat.{u}} [IsLocalRing R]
    (f : X ⟶ Spec R) (j : Y ⟶ X)
    [IsIso (pullback.snd j (pullback.fst f (puncturedSpectrum R).ι))]
    (U : X.affineOpens) :
    Module.support Γ(X, U) (j.ker.ideal U) ⊆
      PrimeSpectrum.zeroLocus ((maximalIdeal R).map (baseSectionHom f U) : Set Γ(X, U)) := by
  intro p hp
  change (maximalIdeal R).map (baseSectionHom f U) ≤ p.asIdeal
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  change baseSectionHom f U r ∈ p.asIdeal
  by_contra hs
  apply (Module.notMem_support_iff'.mpr ?_) hp
  intro a
  let s := baseSectionHom f U r
  have hV : X.basicOpen s ≤ (pullback.fst f (puncturedSpectrum R).ι).opensRange := by
    intro x hx
    change x ∈ Set.range (pullback.fst f (puncturedSpectrum R).ι)
    rw [Scheme.Pullback.range_fst, Scheme.Opens.range_ι]
    exact basicOpen_baseSectionHom_le_punctured f U r hr hx
  have hbot : j.ker.ideal (X.affineBasicOpen s) = ⊥ :=
    ker_ideal_eq_bot_of_subset j (pullback.fst f (puncturedSpectrum R).ι)
      (X.affineBasicOpen s) (X.affineBasicOpen s).2 hV
  let ρ := (X.presheaf.map (homOfLE (X.basicOpen_le s)).op).hom
  have hmem : ρ a.val = 0 := by
    have hm := Ideal.mem_map_of_mem ρ a.property
    rw [(j.ker).map_ideal_basicOpen U s, hbot, Ideal.mem_bot] at hm
    exact hm
  have : IsLocalization.Away s Γ(X, X.basicOpen s) := U.2.isLocalization_basicOpen s
  obtain ⟨t, ht⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers s) Γ(X, X.basicOpen s) a.val).mp hmem
  refine ⟨t.val, ?_, Subtype.ext ht⟩
  obtain ⟨n, hn⟩ := t.property
  rw [← hn]
  exact fun h => hs (p.isPrime.mem_of_pow_mem n h)

/-- On each affine open, a fixed positive thickening separates the defining
ideal from the extended maximal-ideal filtration. -/
theorem exists_affine_ker_inf_pow_eq_bot {R : CommRingCat.{u}} [IsLocalRing R]
    [IsLocallyNoetherian X] (f : X ⟶ Spec R) (j : Y ⟶ X)
    [IsIso (pullback.snd j (pullback.fst f (puncturedSpectrum R).ι))]
    (U : X.affineOpens) :
    ∃ n : ℕ, 0 < n ∧ j.ker.ideal U ⊓
      ((maximalIdeal R).map (baseSectionHom f U)) ^ (n + 1) = ⊥ := by
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  exact Langlands.Algebra.AdicSupportSeparation.exists_ideal_inf_pow_eq_bot_of_support
    _ _ (ker_ideal_support_subset f j U)

end Langlands.AlgebraicGeometry.LocalArtinianExhaustion
