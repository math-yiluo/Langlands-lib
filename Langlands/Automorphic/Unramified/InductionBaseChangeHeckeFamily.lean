import Langlands.Global.AdelicFunctoriality.GaloisPlaceCount
import Langlands.Global.HeckeCharacterUnramifiedNorm
import Langlands.Global.HeckeCharacterTransport
import Langlands.Representation.Unramified.EigenvaluesPowerRoots
import Langlands.Automorphic.Unramified.WeakInduction
import Langlands.Global.AdelicFunctoriality.UnramifiedUnitNorm

/-!
# Base change of a weak induction to a Galois closure

Let `K ⊆ M ⊆ L` be number fields with `L/K` Galois, `χ` a Hecke character of `M`, and `s` a
spectral system on the finite places of `K` that is a weak induction of `χ`. Let `ρ i`
represent the right cosets of `Gal(L/M)` in `Gal(L/K)`. At all but finitely many finite
places `u` of `L`, with `v` the place below in `K`, the `f(u|v)`-th powers of the spectrum of
`s` at `v` are the values at any uniformizer of `L_u` of the conjugate characters
`χ ∘ N_{L/M} ∘ ρ i`, with multiplicities. This is the unramified computation behind the
base change of an automorphic induction.
-/

noncomputable section

universe u

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified.WeakInduction

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Polynomial
open scoped NumberField
open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.Unramified

variable {K M L : Type u} [Field K] [Field M] [Field L]
  [NumberField K] [NumberField M] [NumberField L]
  [Algebra K M] [Algebra K L] [Algebra M L] [IsScalarTower K M L]

/-- The conjugate characters `χ ∘ N_{L/M} ∘ ρ i` of `L`. -/
def conjugateNormFamily (χ : HeckeCharacter M) {ι : Type*} (ρ : ι → L ≃ₐ[K] L) (i : ι) :
    HeckeCharacter L :=
  HeckeCharacter.comap (ρ i).toRingEquiv (HeckeCharacter.normComp (L := L) χ)

/-- Every finite place of a number field has a uniformizer. -/
theorem exists_uniformizer {F : Type u} [Field F] [NumberField F] (w : Global.FinitePlace F) :
    ∃ ϖ : (FiniteCompletion F w)ˣ,
      Valued.v (ϖ : FiniteCompletion F w) = WithZero.exp (-1 : ℤ) := by
  obtain ⟨x, hx⟩ := valuedAdicCompletion_surjective F w (WithZero.exp (-1 : ℤ))
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    exact WithZero.coe_ne_zero hx.symm
  exact ⟨Units.mk0 x hx0, hx⟩

omit [NumberField K] [Algebra K M] [IsScalarTower K M L] in
/-- The component of `χ ∘ N_{L/M} ∘ σ` at a uniformizer of `L_u`, where the place
`σ⁻¹ u` lies over `w`, is unramified over it, and `χ` is unramified at `w`. -/
theorem finiteComponent_comap_normComp (χ : HeckeCharacter M) (σ : L ≃ₐ[K] L)
    (u : Global.FinitePlace L) (w : Global.FinitePlace M)
    (hw : (finitePlaceEquiv σ⁻¹.toRingEquiv u).asIdeal.LiesOver w.asIdeal)
    (he : (finitePlaceEquiv σ⁻¹.toRingEquiv u).asIdeal.ramificationIdx (𝓞 M) = 1)
    (hχ : χ.IsUnramifiedAt w) (π : (FiniteCompletion L u)ˣ)
    (hπ : Valued.v (π : FiniteCompletion L u) = WithZero.exp (-1 : ℤ))
    (ϖ : (FiniteCompletion M w)ˣ)
    (hϖ : Valued.v (ϖ : FiniteCompletion M w) = WithZero.exp (-1 : ℤ)) :
    (HeckeCharacter.comap σ.toRingEquiv (HeckeCharacter.normComp (L := L) χ)).finiteComponent
        u π =
      χ.finiteComponent w ϖ ^ (finitePlaceEquiv σ⁻¹.toRingEquiv u).asIdeal.inertiaDeg (𝓞 M) := by
  obtain ⟨u', rfl⟩ : ∃ u', finitePlaceEquiv σ.toRingEquiv u' = u :=
    ⟨_, finitePlaceEquiv_algEquiv_apply_inv σ u⟩
  rw [finitePlaceEquiv_algEquiv_inv_apply] at hw he ⊢
  rw [HeckeCharacter.comap_finiteComponent]
  refine HeckeCharacter.normComp_finiteComponent_uniformizer χ w ⟨u', hw⟩ he hχ _ ?_ ϖ hϖ
  change Valued.v (finiteCompletionEquiv σ.toRingEquiv u' (π : FiniteCompletion L _)) = _
  rw [finiteCompletionEquiv_valuation, hπ]

/-- Only finitely many places of `L` lie above each place of `K`. -/
theorem tendsto_under_cofinite :
    Filter.Tendsto (fun w : HeightOneSpectrum (𝓞 L) => w.under (𝓞 K)) Filter.cofinite
      Filter.cofinite := by
  apply Filter.Tendsto.cofinite_of_finite_preimage_singleton
  intro v
  refine Finite.of_injective
    (fun w : (fun w : HeightOneSpectrum (𝓞 L) => w.under (𝓞 K)) ⁻¹' {v} =>
      (⟨w.1, ⟨?_⟩⟩ : FinitePlacesAbove L v)) ?_
  · have hw : w.1.under (𝓞 K) = v := w.2
    exact (congrArg HeightOneSpectrum.asIdeal hw).symm
  · intro a b hab
    have hab' := congrArg Subtype.val hab
    exact Subtype.ext hab'

/-- The computation of `eventually_power_eq_conjugateNormFamily` at one place `u` of `L`
above a place `v` of `K` where the weak induction holds and `L/K` is unramified. -/
theorem power_eq_map_conjugateNormFamily [IsGalois K L] {n : ℕ}
    (s : SpectralSystem (Global.FinitePlace K) n) (χ : HeckeCharacter M)
    {ι : Type*} [Fintype ι] (ρ : ι → L ≃ₐ[K] L) (hρ : IsRightCosetFamily M ρ)
    (v : Global.FinitePlace K) (u : Global.FinitePlace L) [huv : u.asIdeal.LiesOver v.asIdeal]
    (hexc : v ∉ s.exceptional) (hunr : IsUnramifiedAbove χ v)
    (heul : ∀ ϖ : ∀ w : FinitePlacesAbove M v, (FiniteCompletion M w.1)ˣ,
      IsUniformizerFamily v ϖ → s.eulerPolynomial v hexc = inducedEulerPolynomial χ v ϖ)
    (hram : ∀ q : HeightOneSpectrum (𝓞 L), q.asIdeal.LiesOver v.asIdeal →
      q.asIdeal.ramificationIdx (𝓞 K) = 1) :
    (∀ i, (conjugateNormFamily χ ρ i).IsUnramifiedAt u) ∧
      ∀ π : (FiniteCompletion L u)ˣ,
        Valued.v (π : FiniteCompletion L u) = WithZero.exp (-1 : ℤ) →
        ((s.eigenvalues v hexc).power (u.asIdeal.inertiaDeg (𝓞 K)) : Multiset ℂˣ) =
          (Finset.univ : Finset ι).val.map fun i =>
            (conjugateNormFamily χ ρ i).finiteComponent u π := by
  classical
  -- Every place of `L` above a place `w` of `M` over `v` has inertia degree `f(u|v)` over `K`.
  have hNtower (w : FinitePlacesAbove M v) (q : HeightOneSpectrum (𝓞 L))
      (hq : q.asIdeal.LiesOver w.1.asIdeal) :
      w.1.asIdeal.inertiaDeg (𝓞 K) * q.asIdeal.inertiaDeg (𝓞 M) =
        u.asIdeal.inertiaDeg (𝓞 K) := by
    have : q.asIdeal.LiesOver v.asIdeal := Ideal.LiesOver.trans q.asIdeal w.1.asIdeal v.asIdeal
    obtain ⟨τ, hτ⟩ := Langlands.ClassField.Global.exists_finitePlaceEquiv_eq v u q
    rw [← Ideal.inertiaDeg_tower (R := 𝓞 K) w.1.asIdeal q.asIdeal, ← hτ,
      inertiaDeg_finitePlaceEquiv_algEquiv]
  have hfpos (w : FinitePlacesAbove M v) : 0 < w.1.asIdeal.inertiaDeg (𝓞 K) :=
    Ideal.inertiaDeg_pos (R := 𝓞 K) w.1.asIdeal
  have hdvd (w : FinitePlacesAbove M v) :
      w.1.asIdeal.inertiaDeg (𝓞 K) ∣ u.asIdeal.inertiaDeg (𝓞 K) := by
    obtain ⟨q⟩ := nonempty_finitePlacesAbove (L := L) w.1
    exact Dvd.intro _ (hNtower w q.1 q.2)
  -- The places `(ρ i)⁻¹ u` and the places `w i` of `M` below them.
  have hlies (i : ι) : (finitePlaceEquiv (ρ i)⁻¹.toRingEquiv u).asIdeal.LiesOver v.asIdeal :=
    Langlands.ClassField.Global.liesOver_finitePlaceEquiv v u (ρ i)⁻¹
  let wi (i : ι) : FinitePlacesAbove M v :=
    ⟨(finitePlaceEquiv (ρ i)⁻¹.toRingEquiv u).under (𝓞 M), by
      have := hlies i
      exact Ideal.LiesOver.tower_bot (finitePlaceEquiv (ρ i)⁻¹.toRingEquiv u).asIdeal _
        v.asIdeal⟩
  have hwi (i : ι) : (finitePlaceEquiv (ρ i)⁻¹.toRingEquiv u).asIdeal.LiesOver
      (wi i).1.asIdeal := ⟨rfl⟩
  have hei (i : ι) :
      (finitePlaceEquiv (ρ i)⁻¹.toRingEquiv u).asIdeal.ramificationIdx (𝓞 M) = 1 := by
    have h1 := hram _ (hlies i)
    rw [Ideal.ramificationIdx_tower (R := 𝓞 K) (wi i).1.asIdeal] at h1
    exact Nat.eq_one_of_mul_eq_one_left h1
  refine ⟨fun i => ?_, fun π hπ => ?_⟩
  · -- unramifiedness
    have hu := finitePlaceEquiv_algEquiv_apply_inv (ρ i) u
    rw [← hu]
    change (HeckeCharacter.comap (ρ i).toRingEquiv
      (HeckeCharacter.normComp (L := L) χ)).IsUnramifiedAt
      (finitePlaceEquiv (ρ i).toRingEquiv (finitePlaceEquiv (ρ i)⁻¹.toRingEquiv u))
    rw [HeckeCharacter.isUnramifiedAt_comap_iff]
    exact HeckeCharacter.normComp_isUnramifiedAt χ (wi i).1 ((hunr (wi i)).2)
      ⟨_, hwi i⟩
  · -- the values at a uniformizer
    choose ϖ hϖ using fun w : FinitePlacesAbove M v => exists_uniformizer w.1
    have hE : (s.eigenvalues v hexc).eulerPolynomial =
        ∏ w : FinitePlacesAbove M v, (1 - C ((χ.finiteComponent w.1 (ϖ w) : ℂˣ) : ℂ) *
          X ^ w.1.asIdeal.inertiaDeg (𝓞 K)) := heul ϖ hϖ
    have hpow := Eigenvalues.coe_power_eq_sum_replicate (s.eigenvalues v hexc)
      (fun w : FinitePlacesAbove M v => χ.finiteComponent w.1 (ϖ w))
      (fun w : FinitePlacesAbove M v => w.1.asIdeal.inertiaDeg (𝓞 K))
      (u.asIdeal.inertiaDeg (𝓞 K)) hfpos hdvd hE
    rw [hpow]
    let G : FinitePlacesAbove M v → ℂˣ := fun w =>
      χ.finiteComponent w.1 (ϖ w) ^ (u.asIdeal.inertiaDeg (𝓞 K) / w.1.asIdeal.inertiaDeg (𝓞 K))
    have hval (i : ι) : (conjugateNormFamily χ ρ i).finiteComponent u π = G (wi i) := by
      rw [conjugateNormFamily, finiteComponent_comap_normComp χ (ρ i) u (wi i).1 (hwi i) (hei i)
        (hunr (wi i)).2 π hπ (ϖ (wi i)) (hϖ (wi i))]
      simp only [G]
      congr 1
      rw [← hNtower (wi i) _ (hwi i), Nat.mul_div_cancel_left _ (hfpos (wi i))]
    rw [Multiset.map_congr rfl (fun i _ => hval i),
      show (fun i => G (wi i)) = G ∘ wi from rfl, ← Multiset.map_map G wi]
    have hcount : Finset.univ.val.map wi =
        ∑ w : FinitePlacesAbove M v, Multiset.replicate (w.1.asIdeal.inertiaDeg (𝓞 K)) w := by
      ext w
      rw [Multiset.count_map, Multiset.count_sum']
      simp only [Multiset.count_replicate, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      have hfilter : (Finset.univ.val.filter fun i => w = wi i) =
          (Finset.univ.filter fun i =>
            (finitePlaceEquiv (ρ i)⁻¹.toRingEquiv u).asIdeal.LiesOver w.1.asIdeal).val := by
        rw [Finset.filter_val]
        refine Multiset.filter_congr fun i _ => ?_
        constructor
        · rintro rfl
          exact hwi i
        · intro h
          refine Subtype.ext (HeightOneSpectrum.ext ?_)
          exact h.over
      rw [hfilter, Finset.card_val, card_filter_rightCosetFamily_liesOver ρ hρ v u w.1,
        (hunr w).1, one_mul]
    rw [hcount, ← Multiset.coe_mapAddMonoidHom, map_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp [Multiset.mapAddMonoidHom, Multiset.map_replicate, G]

/-- **Base change of a weak induction.** If `s` is a weak induction of `χ` from `M` to `K`
and `ρ i` represent the right cosets of `Gal(L/M)` in `Gal(L/K)`, then at all but finitely
many finite places `u` of `L`, with `v = u ∩ K`: `s` is defined at `v`, every conjugate
`χ ∘ N_{L/M} ∘ ρ i` is unramified at `u`, and the `f(u|v)`-th powers of the spectrum of `s`
at `v` are, with multiplicities, the values of these conjugates at any uniformizer of `L_u`. -/
theorem eventually_power_eq_conjugateNormFamily [IsGalois K L] {n : ℕ}
    (s : SpectralSystem (Global.FinitePlace K) n) (χ : HeckeCharacter M)
    (hs : s.IsWeakInductionOf χ) {ι : Type*} [Fintype ι] (ρ : ι → L ≃ₐ[K] L)
    (hρ : IsRightCosetFamily M ρ) :
    ∀ᶠ u : Global.FinitePlace L in Filter.cofinite,
      ∃ hu : u.under (𝓞 K) ∉ s.exceptional,
        (∀ i, (conjugateNormFamily χ ρ i).IsUnramifiedAt u) ∧
        ∀ π : (FiniteCompletion L u)ˣ,
          Valued.v (π : FiniteCompletion L u) = WithZero.exp (-1 : ℤ) →
          ((s.eigenvalues (u.under (𝓞 K)) hu).power (u.asIdeal.inertiaDeg (𝓞 K)) :
              Multiset ℂˣ) =
            (Finset.univ : Finset ι).val.map fun i =>
              (conjugateNormFamily χ ρ i).finiteComponent u π := by
  have hv : ∀ᶠ v : Global.FinitePlace K in Filter.cofinite,
      (∀ hv : v ∉ s.exceptional, IsUnramifiedAbove χ v ∧
        ∀ ϖ : ∀ w : FinitePlacesAbove M v, (FiniteCompletion M w.1)ˣ,
          IsUniformizerFamily v ϖ → s.eulerPolynomial v hv = inducedEulerPolynomial χ v ϖ) ∧
      v ∉ s.exceptional ∧
      ∀ q : HeightOneSpectrum (𝓞 L), q.asIdeal.LiesOver v.asIdeal →
        q.asIdeal.ramificationIdx (𝓞 K) = 1 :=
    hs.2.and (s.exceptional.eventually_cofinite_notMem.and
      (eventually_ramificationIdx_eq_one K L))
  filter_upwards [tendsto_under_cofinite.eventually hv] with u hu
  obtain ⟨hind, hexc, hram⟩ := hu
  have huv : u.asIdeal.LiesOver (u.under (𝓞 K)).asIdeal := ⟨rfl⟩
  obtain ⟨hunr, heul⟩ := hind hexc
  exact ⟨hexc, power_eq_map_conjugateNormFamily s χ ρ hρ _ u hexc hunr heul hram⟩

end Langlands.Automorphic.Unramified.WeakInduction
