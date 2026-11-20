import Langlands.Global.AdelicWavePacketIsometryStatement
import Langlands.Global.AdelicWavePacketInnerProductStatement
import Langlands.Global.AdelicInducedInnerProductIntegrableStatement
import Langlands.Global.AdelicWeylSetAssociation
import Langlands.Global.AdelicGroupPolish

/-! # The wave packet isometry from Proposition 2 of Lapid

Lapid 2011, Theorem 2 (p.314), Arthur 2005, Theorem 7.2(b): the wave packet isometry
`WavePacketIsometryStatement` follows from Lapid's Proposition 2
(`WavePacketInnerProductStatement`) applied to every pair of members of the family, the
absolute convergence of the inner products `(·,·)_P` on `A^2_P`
(`InducedInnerProductIntegrableStatement`), and the counting identity
`∑ i, (n_P i)⁻¹ |Ω(P i, P i')| = 1`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions

section Sesquilinear

variable {F : Type} [Field F] [NumberField F]
  {G P M : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  (K : Subgroup (AdelicGroupPoints F G)) (hKc : IsCompact (K : Set (AdelicGroupPoints F G)))
  (p : P ⟶ G) (l : M ⟶ P) (μM : Measure (AdelicGroupPoints F M)) {n : ℕ}
  (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P) (β : (Fin n → ℝ) → ℝ)

/-- The integrand `(k, m) ↦ β(y(m)) δ_P(m)⁻¹ φ(m k) conj ψ(m k)` of `inducedInnerProduct` on
`K × M(F) \ M(𝔸)`. -/
def inducedInnerProductIntegrand (φ ψ : AdelicGroupPoints F G → ℂ)
    (z : K × RationalQuotient F M) : ℂ :=
  (β (parameterCoordinates F P e (characterLog F P (map F M P l z.2.out))) : ℂ) *
    parameterPower F P (-modulusParameter F P) (map F M P l z.2.out) *
    φ (map F P G p (map F M P l z.2.out) * (z.1 : AdelicGroupPoints F G)) *
    (starRingEnd ℂ) (ψ (map F P G p (map F M P l z.2.out) * (z.1 : AdelicGroupPoints F G)))

/-- The measure `dk × dm` on `K × M(F) \ M(𝔸)` underlying `inducedInnerProduct`. -/
def inducedInnerProductMeasure : Measure (K × RationalQuotient F M) :=
  (compactHaarProbability F G K hKc).prod
    (LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F M)
      (isDiscrete_rationalSubgroup F M) μM)

instance sFinite_discreteQuotientMeasure_of_haar [μM.IsHaarMeasure] :
    SFinite (LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F M)
      (isDiscrete_rationalSubgroup F M) μM) := by
  unfold LeftCosetSpace.discreteQuotientMeasure LeftCosetSpace.quotientMeasure
  infer_instance

omit [LocallyOfFiniteType G.X.hom] in
/-- For an integrable integrand, `inducedInnerProduct` is the integral over the product
`K × M(F) \ M(𝔸)` (Fubini). -/
theorem inducedInnerProduct_eq_integral [μM.IsHaarMeasure] (φ ψ : AdelicGroupPoints F G → ℂ)
    (h : Integrable (inducedInnerProductIntegrand K p l e β φ ψ)
      (inducedInnerProductMeasure K hKc μM)) :
    inducedInnerProduct K hKc p l μM e β φ ψ =
      ∫ z, inducedInnerProductIntegrand K p l e β φ ψ z ∂(inducedInnerProductMeasure K hKc μM) :=
  (integral_prod _ h).symm

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine M.X.left]
  [LocallyOfFiniteType M.X.hom] in
theorem inducedInnerProductIntegrand_sum_sum {X Y : Type*} [Fintype X] [Fintype Y]
    (a : X → ℂ) (φ : X → AdelicGroupPoints F G → ℂ) (b : Y → ℂ)
    (ψ : Y → AdelicGroupPoints F G → ℂ) (z : K × RationalQuotient F M) :
    inducedInnerProductIntegrand K p l e β (fun g => ∑ x, a x * φ x g)
        (fun g => ∑ y, b y * ψ y g) z =
      ∑ x, ∑ y, a x * (starRingEnd ℂ) (b y) *
        inducedInnerProductIntegrand K p l e β (φ x) (ψ y) z := by
  simp only [inducedInnerProductIntegrand, map_sum, map_mul]
  rw [Finset.mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

omit [LocallyOfFiniteType G.X.hom] in
/-- Sesquilinearity of `inducedInnerProduct` on finite spans, for integrable integrands. -/
theorem inducedInnerProduct_sum_sum [μM.IsHaarMeasure] {X Y : Type*} [Fintype X] [Fintype Y]
    (a : X → ℂ) (φ : X → AdelicGroupPoints F G → ℂ) (b : Y → ℂ)
    (ψ : Y → AdelicGroupPoints F G → ℂ)
    (h : ∀ x y, Integrable (inducedInnerProductIntegrand K p l e β (φ x) (ψ y))
      (inducedInnerProductMeasure K hKc μM)) :
    inducedInnerProduct K hKc p l μM e β (fun g => ∑ x, a x * φ x g)
        (fun g => ∑ y, b y * ψ y g) =
      ∑ x, ∑ y, a x * (starRingEnd ℂ) (b y) * inducedInnerProduct K hKc p l μM e β (φ x) (ψ y) := by
  have hfun : inducedInnerProductIntegrand K p l e β (fun g => ∑ x, a x * φ x g)
      (fun g => ∑ y, b y * ψ y g) = fun z => ∑ x, ∑ y, a x * (starRingEnd ℂ) (b y) *
        inducedInnerProductIntegrand K p l e β (φ x) (ψ y) z :=
    funext (inducedInnerProductIntegrand_sum_sum K p l e β a φ b ψ)
  have hint : ∀ x y, Integrable (fun z => a x * (starRingEnd ℂ) (b y) *
      inducedInnerProductIntegrand K p l e β (φ x) (ψ y) z)
      (inducedInnerProductMeasure K hKc μM) := fun x y => (h x y).const_mul _
  have hint' : ∀ x, Integrable (fun z => ∑ y, a x * (starRingEnd ℂ) (b y) *
      inducedInnerProductIntegrand K p l e β (φ x) (ψ y) z)
      (inducedInnerProductMeasure K hKc μM) := fun x =>
    integrable_finsetSum _ fun y _ => hint x y
  rw [inducedInnerProduct_eq_integral K hKc p l μM e β _ _
    (by rw [hfun]; exact integrable_finsetSum _ fun x _ => hint' x), hfun,
    integral_finsetSum _ fun x _ => hint' x]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [integral_finsetSum _ fun y _ => hint x y]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [integral_const_mul, inducedInnerProduct_eq_integral K hKc p l μM e β _ _ (h x y)]

end Sesquilinear

section Coordinates

/-- A linear map `ℝᵃ → ℝᵇ` preserving Lebesgue measure has `b ≤ a`: otherwise its range is a
proper subspace, of measure zero, with preimage all of `ℝᵃ`. -/
theorem le_of_measurePreserving_linearMap {a b : ℕ} (f : (Fin a → ℝ) →ₗ[ℝ] (Fin b → ℝ))
    (hf : MeasurePreserving f volume volume) : b ≤ a := by
  by_contra h
  rw [not_le] at h
  have hrange : LinearMap.range f ≠ ⊤ := by
    intro htop
    have := LinearMap.finrank_range_le f
    rw [htop, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at this
    omega
  have h0 : volume ((LinearMap.range f : Submodule ℝ (Fin b → ℝ)) : Set (Fin b → ℝ)) = 0 :=
    Measure.addHaar_submodule volume _ hrange
  have hmeas : MeasurableSet ((LinearMap.range f : Submodule ℝ (Fin b → ℝ)) :
      Set (Fin b → ℝ)) :=
    (Submodule.closed_of_finiteDimensional _).measurableSet
  have hpre := hf.measure_preimage hmeas.nullMeasurableSet
  have huniv : (f : (Fin a → ℝ) → (Fin b → ℝ)) ⁻¹'
      ((LinearMap.range f : Submodule ℝ (Fin b → ℝ)) : Set (Fin b → ℝ)) = Set.univ := by
    ext x
    simp
  rw [huniv, h0] at hpre
  exact isOpen_univ.measure_ne_zero volume Set.univ_nonempty hpre

/-- Change of variables along a measure-preserving map `ℝᵃ → ℝᵇ` for the measures
`(2π)^{-a} dx` and `(2π)^{-b} dx`, when `a = b`. -/
theorem integral_comp_spectralMeasure {a b : ℕ} (hab : a = b) (f : (Fin a → ℝ) → (Fin b → ℝ))
    (hf : MeasurePreserving f volume volume) (g : (Fin b → ℝ) → ℂ) (hg : Continuous g) :
    ∫ x, g (f x) ∂(spectralMeasure a) = ∫ y, g y ∂(spectralMeasure b) := by
  unfold spectralMeasure
  rw [integral_smul_measure, integral_smul_measure,
    ← integral_map hf.measurable.aemeasurable hg.aestronglyMeasurable, hf.map_eq, hab]

theorem integrable_comp_spectralMeasure {a b : ℕ} (f : (Fin a → ℝ) → (Fin b → ℝ))
    (hf : MeasurePreserving f volume volume) (g : (Fin b → ℝ) → ℂ) (hg : Integrable g volume) :
    Integrable (fun x => g (f x)) (spectralMeasure a) := by
  unfold spectralMeasure
  refine (hf.integrable_comp_of_integrable hg).smul_measure ?_
  exact ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (by simp [Real.pi_pos]))

end Coordinates

end Langlands.Global.AdelicGroupPoints

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

/-- The wave packet isometry (Lapid 2011, Theorem 2; Arthur 2005, Theorem 7.2(b)) follows from
Lapid's Proposition 2 (`WavePacketInnerProductStatement`) and the absolute convergence of the
inner products `(·,·)_P` on `A^2_P` (`InducedInnerProductIntegrableStatement`). -/
theorem wavePacketIsometry_of_innerProduct (h2 : WavePacketInnerProductStatement)
    (hI : InducedInnerProductIntegrableStatement) : WavePacketIsometryStatement := by
  intro F _ _ G _ _ _ I _ P M U A _ _ _ _ p _ iU l _ a r _ _ _ hA hT π hG hU hπ K hK N d rho
    hsmooth hcalc hKmax hrho μM _ hμM n e β hβ k v c E D hv hc hD hE hEis T _ w cw hW hinj hsurj
    hmp m ψ coeff DM hψ hDM hcoeff hint hcompat Θ nP Φ μG
  have : ∀ i, LocallyOfFiniteType (P i).X.hom := fun i =>
    IsClosedSubgroup.locallyOfFiniteType (j := p i)
      (inferInstance : IsClosedImmersion (p i).hom.hom.left)
  -- Proposition 2 for every ordered pair of members.
  have H2 : ∀ i i', MemLp (fun y : RationalQuotient F G => Θ i y.out) 2 μG ∧
      MemLp (fun y : RationalQuotient F G => Θ i' y.out) 2 μG ∧
      ∫ y, Θ i y.out * (starRingEnd ℂ) (Θ i' y.out) ∂μG =
        ∫ x, ∑ t, ∑ j, ∑ q, ∑ j',
            c i j x * coeff i i' t j q (imaginaryParameter F (P i) (e i x)) *
              (starRingEnd ℂ)
                (c i' j' ((e i').symm (realWeylParameter (l i) (cw i i' t) (π i') (e i x)))) *
              inducedInnerProduct K (hK i').isCompact (p i') (l i') (μM i') (e i') (β i')
                (ψ i i' t j q) (v i' j')
          ∂(spectralMeasure (n i)) := fun i i' =>
    h2 F G (P i) (M i) (U i) (P i') (M i') (U i') (A i) (A i') (p i) (iU i) (l i) (a i) (r i)
      (hA i) (hT i) (p i') (iU i') (l i') (a i') (r i') (hA i') (hT i') (π i') hG (hU i) (hU i')
      (hπ i') K (hK i) (hK i') rho hsmooth hcalc hKmax hrho (μM i') (hμM i') (e i) (e i') (β i')
      (hβ i').1 (hβ i').2.1 (hβ i').2.2 (k i) (v i) (c i) (E i) (D i) (hv i) (hc i) (hD i) (hE i)
      (hEis i) (k i') (v i') (c i') (E i') (D i') (hv i') (hc i') (hD i') (hE i') (hEis i')
      (T i i') (w i i') (cw i i') (hW i i') (hinj i i') (hsurj i i') m (ψ i i') (coeff i i')
      (DM i) (hψ i i') (hDM i) (hcoeff i i') (hint i i')
  -- Absolute convergence of the inner products on `A^2_{P i}`.
  have hII : ∀ i (φ φ' : AdelicGroupPoints F G → ℂ),
      IsSquareIntegrableInducedForm K (hK i).isCompact rho hsmooth hcalc (p i) (iU i) (l i) φ →
      IsSquareIntegrableInducedForm K (hK i).isCompact rho hsmooth hcalc (p i) (iU i) (l i) φ' →
      Integrable (inducedInnerProductIntegrand K (p i) (l i) (e i) (β i) φ φ')
        (inducedInnerProductMeasure K (hK i).isCompact (μM i)) := fun i φ φ' hφ hφ' =>
    hI F G (P i) (M i) (U i) (A i) (p i) (iU i) (l i) (a i) (r i) (hA i) (hT i) (π i) hG (hU i)
      (hπ i) K (hK i) rho hsmooth hcalc hKmax hrho (μM i) (hμM i) (e i) (β i) (hβ i).1
      (hβ i).2.1 φ φ' hφ hφ'
  -- The functions `x ↦ (F i x, F i x)_{P i}` and the coordinate changes `x ↦ x'`.
  obtain ⟨Nf, hNf⟩ : ∃ Nf : ∀ i, (Fin (n i) → ℝ) → ℂ, ∀ i x, Nf i x =
      inducedInnerProduct K (hK i).isCompact (p i) (l i) (μM i) (e i) (β i)
        (fun g => ∑ j, c i j x * v i j g) (fun g => ∑ j, c i j x * v i j g) :=
    ⟨fun i x => inducedInnerProduct K (hK i).isCompact (p i) (l i) (μM i) (e i) (β i)
        (fun g => ∑ j, c i j x * v i j g) (fun g => ∑ j, c i j x * v i j g),
      fun _ _ => rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ∀ i i', T i i' → (Fin (n i) → ℝ) → (Fin (n i') → ℝ), ∀ i i' t x,
      Y i i' t x = (e i').symm (realWeylParameter (l i) (cw i i' t) (π i') (e i x)) :=
    ⟨fun i i' t x => (e i').symm (realWeylParameter (l i) (cw i i' t) (π i') (e i x)),
      fun _ _ _ _ => rfl⟩
  have hmpY : ∀ i i' t, MeasurePreserving (Y i i' t) volume volume := fun i i' t => by
    rw [show Y i i' t = _ from funext (hY i i' t)]
    exact hmp i i' t
  have hN : ∀ i x, Nf i x = ∑ j, ∑ j', c i j x * (starRingEnd ℂ) (c i j' x) *
      inducedInnerProduct K (hK i).isCompact (p i) (l i) (μM i) (e i) (β i) (v i j) (v i j') :=
    fun i x => (hNf i x).trans (inducedInnerProduct_sum_sum K (hK i).isCompact (p i) (l i) (μM i)
      (e i) (β i) (fun j => c i j x) (v i) (fun j => c i j x) (v i)
      fun j j' => hII i _ _ (hv i j) (hv i j'))
  have hNcont : ∀ i, Continuous (Nf i) := fun i => by
    rw [show Nf i = _ from funext (hN i)]
    refine continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun j' _ => ?_
    exact ((hc i j).1.continuous.mul
      (Complex.continuous_conj.comp (hc i j').1.continuous)).mul continuous_const
  have hNsupp : ∀ i, HasCompactSupport (Nf i) := fun i => by
    refine HasCompactSupport.intro (isCompact_iUnion fun j => (hc i j).2.isCompact)
      fun x hx => ?_
    rw [hN]
    refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun j' _ => ?_
    rw [image_eq_zero_of_notMem_tsupport fun h => hx (Set.mem_iUnion.mpr ⟨j, h⟩), zero_mul,
      zero_mul]
  have hNint : ∀ i, Integrable (Nf i) volume := fun i =>
    (hNcont i).integrable_of_hasCompactSupport (hNsupp i)
  have hNint' : ∀ i, Integrable (Nf i) (spectralMeasure (n i)) := fun i => by
    unfold spectralMeasure
    exact (hNint i).smul_measure
      (ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (by simp [Real.pi_pos])))
  -- Associate members have the same rank.
  have hdim : ∀ i i', T i i' → n i = n i' := fun i i' t => by
    obtain ⟨c', hc', -, -⟩ := (hW i i' t).exists_symm
    obtain ⟨t', -⟩ := hsurj i' i _ ⟨_, c', hc', rfl⟩
    exact le_antisymm
      (le_of_measurePreserving_linearMap
        ((e i).symm.toLinearMap ∘ₗ realWeylParameter (l i') (cw i' i t') (π i) ∘ₗ
          (e i').toLinearMap) (hmp i' i t'))
      (le_of_measurePreserving_linearMap
        ((e i').symm.toLinearMap ∘ₗ realWeylParameter (l i) (cw i i' t) (π i') ∘ₗ
          (e i).toLinearMap) (hmp i i' t))
  -- The integrand of Proposition 2 is `∑ t, (F i' (x'_t), F i' (x'_t))_{P i'}`.
  have hpt : ∀ i i' (t : T i i') (x : Fin (n i) → ℝ),
      Nf i' (Y i i' t x) =
        ∑ j, ∑ q, ∑ j', c i j x * coeff i i' t j q (imaginaryParameter F (P i) (e i x)) *
          (starRingEnd ℂ) (c i' j' (Y i i' t x)) *
          inducedInnerProduct K (hK i').isCompact (p i') (l i') (μM i') (e i') (β i')
            (ψ i i' t j q) (v i' j') := by
    intro i i' t x
    rw [hY]
    have h1 : (fun g => ∑ j', c i' j' ((e i').symm (realWeylParameter (l i) (cw i i' t) (π i')
        (e i x))) * v i' j' g) = fun g => ∑ jq : Fin (k i) × Fin m,
          (c i jq.1 x * coeff i i' t jq.1 jq.2 (imaginaryParameter F (P i) (e i x))) *
            ψ i i' t jq.1 jq.2 g := by
      funext g
      rw [hcompat i i' t x g, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      ring
    rw [hNf]
    refine (congrArg (fun φ => inducedInnerProduct K (hK i').isCompact (p i') (l i') (μM i')
      (e i') (β i') φ (fun g => ∑ j', c i' j' ((e i').symm (realWeylParameter (l i) (cw i i' t)
        (π i') (e i x))) * v i' j' g)) h1).trans ?_
    refine (inducedInnerProduct_sum_sum K (hK i').isCompact (p i') (l i') (μM i') (e i') (β i')
      (fun jq : Fin (k i) × Fin m =>
        c i jq.1 x * coeff i i' t jq.1 jq.2 (imaginaryParameter F (P i) (e i x)))
      (fun jq => ψ i i' t jq.1 jq.2)
      (fun j' => c i' j' ((e i').symm (realWeylParameter (l i) (cw i i' t) (π i') (e i x))))
      (v i') fun jq j' => hII i' _ _ (hψ i i' t jq.1 jq.2) (hv i' j')).trans ?_
    exact Fintype.sum_prod_type _
  -- `(Θ i, Θ i') = |T i i'| ∫ (F i' x, F i' x)_{P i'} dx`.
  have hpair : ∀ i i', ∫ y, Θ i y.out * (starRingEnd ℂ) (Θ i' y.out) ∂μG =
      (Fintype.card (T i i') : ℂ) * ∫ x, Nf i' x ∂(spectralMeasure (n i')) := by
    intro i i'
    rw [(H2 i i').2.2]
    simp only [← hY, ← hpt]
    rw [integral_finsetSum _ fun t _ =>
        integrable_comp_spectralMeasure _ (hmpY i i' t) _ (hNint i'),
      Finset.sum_congr rfl fun t _ =>
        integral_comp_spectralMeasure (hdim i i' t) _ (hmpY i i' t) _ (hNcont i'),
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- Expansion of `‖Φ‖²`.
  have hΘ : ∀ i, MemLp (fun y : RationalQuotient F G => Θ i y.out) 2 μG := fun i => (H2 i i).1
  have hprod : ∀ i i', Integrable
      (fun y : RationalQuotient F G => Θ i y.out * (starRingEnd ℂ) (Θ i' y.out)) μG :=
    fun i i' => (hΘ i).integrable_mul (hΘ i').star
  have hΦ : MemLp (fun y : RationalQuotient F G => Φ y.out) 2 μG :=
    memLp_finsetSum Finset.univ fun i _ => (hΘ i).const_mul ((nP i : ℂ))⁻¹
  have hconj : ∀ i, (starRingEnd ℂ) ((nP i : ℂ))⁻¹ = ((nP i : ℂ))⁻¹ := fun i => by
    rw [map_inv₀, Complex.conj_natCast]
  have hexp : ∀ y : RationalQuotient F G, Φ y.out * (starRingEnd ℂ) (Φ y.out) =
      ∑ i, ∑ i', ((nP i : ℂ))⁻¹ * ((nP i' : ℂ))⁻¹ *
        (Θ i y.out * (starRingEnd ℂ) (Θ i' y.out)) := by
    intro y
    show (∑ i, ((nP i : ℂ))⁻¹ * Θ i y.out) *
      (starRingEnd ℂ) (∑ i', ((nP i' : ℂ))⁻¹ * Θ i' y.out) = _
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
    rw [map_mul, hconj]
    ring
  have hΦΦ : ∫ y, Φ y.out * (starRingEnd ℂ) (Φ y.out) ∂μG =
      ∑ i, ∑ i', ((nP i : ℂ))⁻¹ * ((nP i' : ℂ))⁻¹ *
        ((Fintype.card (T i i') : ℂ) * ∫ x, Nf i' x ∂(spectralMeasure (n i'))) := by
    rw [integral_congr_ae (ae_of_all _ hexp),
      integral_finsetSum _ fun i _ => integrable_finsetSum _ fun i' _ =>
        (hprod i i').const_mul _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun i' _ => (hprod i i').const_mul _]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [integral_const_mul, hpair]
  -- The counting identity `∑ i, (n_P i)⁻¹ |T i i'| = 1`.
  have hcount : ∀ i', ((nP i' : ℂ))⁻¹ * ∑ i, ((nP i : ℂ))⁻¹ * (Fintype.card (T i i') : ℂ) =
      ((nP i' : ℂ))⁻¹ := fun i' => by
    by_cases h : nP i' = 0
    · simp [h]
    · have h1 := congrArg (fun s : ℝ => (s : ℂ))
        (sum_inv_card_mul_card_eq_one p l π T w cw hπ hW hinj hsurj i' h)
      simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_inv,
        Complex.ofReal_natCast, Complex.ofReal_one] at h1
      rw [show ∑ i, ((nP i : ℂ))⁻¹ * (Fintype.card (T i i') : ℂ) = 1 from h1, mul_one]
  have hRe : ∀ i, ∫ x, (inducedInnerProduct K (hK i).isCompact (p i) (l i) (μM i) (e i) (β i)
      (fun g => ∑ j, c i j x * v i j g) (fun g => ∑ j, c i j x * v i j g)).re
        ∂(spectralMeasure (n i)) = (∫ x, Nf i x ∂(spectralMeasure (n i))).re := fun i => by
    simp only [← hNf]
    exact integral_re (hNint' i)
  refine ⟨hΦ, ?_⟩
  have hnorm : ∀ y : RationalQuotient F G,
      ‖Φ y.out‖ ^ 2 = (Φ y.out * (starRingEnd ℂ) (Φ y.out)).re := fun y => by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hΦint : Integrable
      (fun y : RationalQuotient F G => Φ y.out * (starRingEnd ℂ) (Φ y.out)) μG :=
    hΦ.integrable_mul hΦ.star
  rw [integral_congr_ae (ae_of_all _ hnorm),
    show ∫ y, (Φ y.out * (starRingEnd ℂ) (Φ y.out)).re ∂μG =
      (∫ y, Φ y.out * (starRingEnd ℂ) (Φ y.out) ∂μG).re from integral_re hΦint, hΦΦ]
  simp only [hRe]
  calc (∑ i, ∑ i', ((nP i : ℂ))⁻¹ * ((nP i' : ℂ))⁻¹ *
          ((Fintype.card (T i i') : ℂ) * ∫ x, Nf i' x ∂(spectralMeasure (n i')))).re
      = (∑ i', ((nP i' : ℂ))⁻¹ * (∑ i, ((nP i : ℂ))⁻¹ * (Fintype.card (T i i') : ℂ)) *
          ∫ x, Nf i' x ∂(spectralMeasure (n i'))).re := by
        rw [Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun i' _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    _ = (∑ i', ((nP i' : ℂ))⁻¹ * ∫ x, Nf i' x ∂(spectralMeasure (n i'))).re := by
        simp only [hcount]
    _ = ∑ i, ((nP i : ℝ))⁻¹ * (∫ x, Nf i x ∂(spectralMeasure (n i))).re := by
        rw [Complex.re_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show ((nP i : ℂ))⁻¹ = (((nP i : ℝ))⁻¹ : ℝ) by
          rw [Complex.ofReal_inv, Complex.ofReal_natCast], Complex.re_ofReal_mul]

end Langlands.Global
