import Langlands.AlgebraicGeometry.FiniteEtale.ConnectedCoverQuotientLift
import Langlands.AlgebraicGeometry.FiniteEtale.KummerFactorizationStatement
import Langlands.AlgebraicGeometry.FiniteEtale.UniformizerBinomialPullback

/-! # Finite prime-group quotient values under change of strictly Henselian trait -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

universe u v

namespace Langlands.AlgebraicGeometry.FiniteEtale

/-- Inverting one uniformizer in a DVR gives its fraction ring. -/
theorem isFractionRing_away_uniformizer {W : Type u} [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] {π : W} (hπ : Irreducible π) :
    IsFractionRing W (Localization.Away π) := by
  apply IsLocalization.of_le_of_exists_dvd (M := Submonoid.powers π)
  · rintro x ⟨n, rfl⟩
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero _ hπ.ne_zero)
  · intro x hx
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (mem_nonZeroDivisors_iff_ne_zero.mp hx) hπ
    refine ⟨π ^ n, ⟨n, rfl⟩, ↑u⁻¹, ?_⟩
    calc
      π ^ n = π ^ n * ((u : W) * ↑u⁻¹) := by simp
      _ = ((u : W) * π ^ n) * ↑u⁻¹ := by ac_rfl

/-- A uniformizer does not belong to the square of the maximal ideal. -/
theorem uniformizer_notMem_maximalIdeal_sq {W : Type u} [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] {π : W} (hπ : Irreducible π) : π ∉ maximalIdeal W ^ 2 := by
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  rintro ⟨a, ha⟩
  have h : a * π = 1 := mul_right_cancel₀ hπ.ne_zero (by simpa [pow_two, mul_assoc] using ha)
  exact hπ.not_isUnit (IsUnit.of_mul_eq_one a (by rw [mul_comm, h]))

/-- A morphism of strictly Henselian traits preserving the uniformizer preserves the image
of each continuous homomorphism of the old generic fundamental group to a finite
prime group for a prime invertible on the trait, assuming strict-local Kummer factorization. -/
def WeaklyUnramifiedDvrQuotientLiftStatement : Prop := StrictlyHenselianKummerFactorizationStatement.{u, v} →
  ∀ (W L W' L' : Type u) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [HenselianLocalRing W] [IsSepClosed (ResidueField W)]
    [Field L] [Algebra W L] [IsFractionRing W L]
    [CommRing W'] [IsDomain W'] [IsDiscreteValuationRing W']
    [Field L'] [Algebra W' L'] [IsFractionRing W' L']
    (i : W →+* W') (iFrac : L →+* L'),
    iFrac.comp (algebraMap W L) = (algebraMap W' L').comp i →
    ∀ (π : W), Irreducible π → Irreducible (i π) → ∀ (ℓ : ℕ) [Fact ℓ.Prime],
    IsUnit (ℓ : W) →
    ∀ {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ Spec (.of L')),
      let f := Spec.map (CommRingCat.ofHom iFrac)
      let s := t ≫ f
      ∀ (H : Type v) [Group H] [Finite H] [TopologicalSpace H] [DiscreteTopology H],
        IsPGroup ℓ H →
        ∀ (ρ : FundamentalGroup s (geometricFiberFinite s) →* H), Continuous ρ →
        ∀ g : FundamentalGroup s (geometricFiberFinite s),
          ∃ h : FundamentalGroup t (geometricFiberFinite t),
            ρ (fundamentalGroupMap f t s rfl (geometricFiberFinite t) (geometricFiberFinite s) h) = ρ g

private theorem fundamentalGroupMap_rightInverseIso {S U : Scheme.{u}} {Ω : Type u} [Field Ω]
    [IsAlgClosed Ω] (e : S ≅ U) (s : Spec (.of Ω) ⟶ S) (sU : Spec (.of Ω) ⟶ U)
    (h : s ≫ e.hom = sU) (h' : sU ≫ e.inv = s) (g : FundamentalGroup s (geometricFiberFinite s)) :
    fundamentalGroupMap e.inv sU s h' (geometricFiberFinite sU) (geometricFiberFinite s)
      (fundamentalGroupMap e.hom s sU h (geometricFiberFinite s) (geometricFiberFinite sU) g) = g := by
  subst sU
  have he := DFunLike.congr_fun
    (fundamentalGroupMap_comp e.inv (s ≫ e.hom) s (by simp) (geometricFiberFinite (s ≫ e.hom))
      (geometricFiberFinite s) e.hom s rfl (by simp) (geometricFiberFinite s)) g
  have hId (f : S ⟶ S) (hf : s ≫ f = s) (hf' : f = 𝟙 S) :
      fundamentalGroupMap f s s hf (geometricFiberFinite s) (geometricFiberFinite s) g = g := by
    subst f
    rw [fundamentalGroupMap_id]
    rfl
  exact he.symm.trans (hId (e.hom ≫ e.inv) (by simp) e.hom_inv_id)

/-- Apply connected cover quotient lifting to the binomial of the factoring Kummer level. -/
theorem weaklyUnramifiedDvrQuotientLift : WeaklyUnramifiedDvrQuotientLiftStatement.{u, v} := by
  intro hK W L W' L' _ _ _ _ _ _ _ _ _ _ _ _ _ _ i iFrac hi π hπ hπ' ℓ hℓ hu Ω _ _ t
  dsimp only
  intro H _ _ _ _ hHG ρ hρ g
  let f := Spec.map (CommRingCat.ofHom iFrac)
  let s := t ≫ f
  let hs := geometricFiberFinite s
  let ht := geometricFiberFinite t
  let B := Localization.Away π
  have : IsFractionRing W B := isFractionRing_away_uniformizer hπ
  let ε := IsLocalization.algEquiv (nonZeroDivisors W) B L
  let e := Scheme.Spec.mapIso ε.toRingEquiv.toCommRingCatIso.op
  let sB := t ≫ (f ≫ e.hom)
  have hsb : s ≫ e.hom = sB := Category.assoc _ _ _
  let hsB := geometricFiberFinite sB
  have hinv : sB ≫ e.inv = s := by rw [← hsb]; simp
  let ψ := fundamentalGroupMap e.inv sB s hinv hsB hs
  let η := fundamentalGroupMap e.hom s sB hsb hs hsB
  let ρB := ρ.comp ψ
  have hρB : Continuous ρB := hρ.comp (continuous_fundamentalGroupMap e.inv sB s hinv hsB hs)
  have hparam : π ∈ maximalIdeal W := (mem_maximalIdeal π).mpr hπ.not_isUnit
  obtain ⟨m, y, hy, hkill⟩ := hK W π hparam (uniformizer_notMem_maximalIdeal_sq hπ) ℓ hu
    Ω sB H hHG ρB hρB
  let b := algebraMap W B π
  have hb : IsUnit b := IsLocalization.map_units B (⟨π, Submonoid.mem_powers _⟩ : Submonoid.powers π)
  have hℓm : IsUnit ((ℓ ^ m : ℕ) : B) := by
    simpa using (hu.map (algebraMap W B)).pow m
  let Y := binomialCover b (pow_ne_zero m hℓ.out.ne_zero) hℓm hb
  let x : Fiber sB Y := Over.homMk y hy
  let θ := iFrac.comp ε.toRingHom
  have hθ : θ b = algebraMap W' L' (i π) := by
    change iFrac (ε (algebraMap W B π)) = _
    rw [ε.commutes]
    exact DFunLike.congr_fun hi π
  have hθspec : f ≫ e.hom = Spec.map (CommRingCat.ofHom θ) := by
    change Spec.map (CommRingCat.ofHom iFrac) ≫ Spec.map (CommRingCat.ofHom ε.toRingHom) = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hconn : ConnectedSpace ((pullbackFunctor (f ≫ e.hom)).obj Y).obj.left := by
    change ConnectedSpace (pullback (binomialMorphism b (ℓ ^ m)) (f ≫ e.hom) : Scheme.{u})
    rw [hθspec]
    exact uniformizerBinomialPullback B W' L' θ b (i π) hθ hπ' (ℓ ^ m) (pow_ne_zero m hℓ.out.ne_zero)
  obtain ⟨h, hh⟩ := connectedCoverQuotientLift (f ≫ e.hom) t Y x hconn ρB hkill (η g)
  have hcomp := DFunLike.congr_fun (fundamentalGroupMap_comp e.hom s sB rfl hs hsB
    f t rfl rfl ht) h
  change ρ (ψ ((fundamentalGroupMap (f ≫ e.hom) t sB rfl ht hsB) h)) = ρ (ψ (η g)) at hh
  rw [hcomp, MonoidHom.comp_apply] at hh
  change ρ (ψ (η ((fundamentalGroupMap f t s rfl ht hs) h))) = ρ (ψ (η g)) at hh
  refine ⟨h, ?_⟩
  simpa only [ψ, η, hsB, fundamentalGroupMap_rightInverseIso] using hh

end Langlands.AlgebraicGeometry.FiniteEtale
