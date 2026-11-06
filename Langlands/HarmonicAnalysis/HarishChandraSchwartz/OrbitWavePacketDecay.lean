import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitWavePacket
import Langlands.Representation.Plancherel.ProductInducedOrbitBaseChange
import Langlands.HarmonicAnalysis.TorusFourierAveraging
import Langlands.HarmonicAnalysis.TorusFourierInversion
import Langlands.HarmonicAnalysis.TorusMonomialDerivative

/-! # The first bound in the proof of Prop. VI.3.1 for the wave packets `f_ψ`

Waldspurger, proof of Prop. VI.3.1 (printed p. 303): for `χ ∈ Im X(M)`, `λ ∈ Im X(G)` and
`g ∈ G`, `(E^G_P sp_{λχ} ψ)(g) = λ(g) (E^G_P sp_χ ψ)(g)`; averaging over `Im X(G)` and the
rapid decay of Fourier coefficients on that torus give, with Lemma VI.2.2,
`|f_ψ(g)| ≤ c (1 + |H_G(g)|)^{-r} Ξ(g)` for every `r`.

This module proves these two steps for the wave packet `inducedOrbitWavePacket` of
`OrbitWavePacket`. The coefficient of the twist `I_P^G(A ⊗ χ)` at the transport of a fixed
compact section `F₀` is `twistedSectionCoefficient χ F₀`. For a character `Λ` of `G` trivial on
`K` and `U` whose restriction to `M` is the unramified character `θ`, the coefficient for `θ χ`
is `Λ(g)` times the one for `χ` (`twistedSectionCoefficient_mul`). The coefficient is continuous
in `χ` along continuous families of unitary characters (`continuous_twistedSectionCoefficient`).

The torus `Im X(G)` is given in coordinates `z : L → Circle`, with its characters
`g ↦ z^{n_G(g)}` for a homomorphism `n_G : G → ℤ^L` (`H_G` in lattice coordinates) trivial on
`K` and `U`, and its restriction to `M` is the integer monomial map `finiteTorusMonomial a` in
the torus coordinates `e` of the unitary unramified characters of `M`. For continuous Laurent
coordinates `e`, a weight `w` that is smooth in these coordinates, a finite left invariant
measure `ρ` on the characters, the hypotheses of Lemma VI.2.2 used in `OrbitWavePacket`, and
every real `r`, `exists_norm_inducedOrbitWavePacket_le_xi_rpow` gives `c > 0` with
`|f_ψ(g)| ≤ c Ξ(g) (1 + ‖n_G(g)‖)^{-r}` for all `g ∈ G`.
-/

noncomputable section

open MeasureTheory Langlands.Aubert.General Langlands.Plancherel Langlands.Induction
open Langlands.HarmonicAnalysis.TorusFourier
open scoped NNReal ENNReal

namespace Langlands.HarishChandraSchwartz

universe uG uV uI uJ uL

section Lattice

variable {G : Type uG} [Group G] {L : Type uL} [Fintype L]

/-- The character `g ↦ z^{n(g)}` of `G` attached to a homomorphism `n : G → ℤ^L` and a point
`z` of the torus `(S¹)^L`: for `n = H_G` in lattice coordinates, these are the characters of
`Im X(G)` in Waldspurger's proof of Prop. VI.3.1. -/
def latticeTorusCharacter (n : G →* Multiplicative (L → ℤ)) (z : L → Circle) : G →* ℂ where
  toFun g := torusCharacter (Multiplicative.toAdd (n g)) z
  map_one' := by
    rw [map_one, toAdd_one, torusCharacter_zero]
  map_mul' g g' := by
    rw [map_mul, toAdd_mul, torusCharacter_add]

theorem latticeTorusCharacter_apply (n : G →* Multiplicative (L → ℤ)) (z : L → Circle) (g : G) :
    latticeTorusCharacter n z g = torusCharacter (Multiplicative.toAdd (n g)) z :=
  rfl

end Lattice

section Twist

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (hU : IsClosed (U : Set G)) (A : SmoothRep.{0, uG, uV} ℂ M) (K : OpenSubgroup G)
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (hK : IsCompact (K : Set G)) {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))
  (hν : ∀ i, Continuous (ν i)) [LocallyCompactSpace P] (hP : IsClosed (P : Set G))
  (hm : Continuous h.projection) (hPK : ∀ g : G, ∃ q ∈ P, ∃ k ∈ K, g = q * k)
  (hG : ∀ g : G, Measure.modularCharacter g = 1)
  (hδP : ∀ q : P, Measure.modularCharacter q =
    (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer q : ℝ≥0))
  (hA : A.IsAdmissible)

set_option maxHeartbeats 1000000 in
/-- The coefficient `g ↦ ⟨I_P^G(A ⊗ χ)(g) v_χ, v̌_χ⟩` of the twist `A ⊗ χ` at the transport
`twistedSection χ F₀` of a section `F₀` of the compact picture (Waldspurger's `v_χ`, proof of
Lemma VI.2.2), as a linear map in `F₀`. -/
def twistedSectionCoefficient (χ : unramifiedCharacters ν) :
    ProductInducedCompactPicture h K A →ₗ[ℂ] LocallyConstant G ℂ :=
  (CompactInduction.coefficientMap h hU
    (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) K hK hP hm hPK hG hδP
    ((SmoothRep.isAdmissible_twist_iff _ _ A).mpr hA)).comp
    (productInducedCompactEquiv ν h K hP hK hν hm hU (factorization_subtype hPK) χ A).symm.toLinearMap

set_option maxHeartbeats 1000000 in
theorem twistedSectionCoefficient_apply (χ : unramifiedCharacters ν)
    (F₀ : ProductInducedCompactPicture h K A) :
    twistedSectionCoefficient h hU A K hK ν hν hP hm hPK hG hδP hA χ F₀ =
      CompactInduction.coefficientMap h hU
        (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) K hK hP hm hPK hG hδP
        ((SmoothRep.isAdmissible_twist_iff _ _ A).mpr hA)
        (twistedSection h hU A K ν hP hK hν hm (factorization_subtype hPK) χ F₀) :=
  rfl

omit [T2Space G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace P] in
include hK in
/-- **Twisting the diagonal integrand**: for every parabolic–compact factorization
`k g = q k₁`, the diagonal integrand of the transport of `F₀` to `A ⊗ θχ` is `θ(m(q))` times
the one for `A ⊗ χ`, where `m(q)` is the Levi component of `q`. -/
theorem integrand_twistedSection_mul (θ χ : unramifiedCharacters ν)
    (F₀ : ProductInducedCompactPicture h K A) (g : G) (k k₁ : K) (q : P)
    (he : (k : G) * g = (q : G) * (k₁ : G)) :
    CompactInduction.integrand h hU
        (A.twist (θ * χ).val.toMonoidHom (unramifiedCharacter_isOpen_ker ν (θ * χ))) K g
        (twistedSection h hU A K ν hP hK hν hm (factorization_subtype hPK) (θ * χ) F₀) k =
      (θ.val (h.projection q) : ℂ) *
        CompactInduction.integrand h hU
          (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) K g
          (twistedSection h hU A K ν hP hK hν hm (factorization_subtype hPK) χ F₀) k := by
  have key : ∀ χ' : unramifiedCharacters ν,
      CompactInduction.integrand h hU
          (A.twist χ'.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ')) K g
          (twistedSection h hU A K ν hP hK hν hm (factorization_subtype hPK) χ' F₀) k =
        (HaarModulus.closedHalfCharacter U hU P h.le_normalizer q : ℂ) *
          ((χ'.val (h.projection q) : ℂ) *
            coefficientTensorMap A (eval _ _ F₀ ⟨((k₁ : G), (k : G)), k₁.2, k.2⟩)
              (h.projection q)) := by
    intro χ'
    rw [CompactInduction.integrand_factorization h hU _ K _ g k k₁ q he,
      compactValue_twistedSection, coefficientTensorMap_twist, LinearEquiv.apply_symm_apply]
  rw [key (θ * χ), key χ]
  have hmul : ((θ * χ).val (h.projection q) : ℂ) =
      (θ.val (h.projection q) : ℂ) * (χ.val (h.projection q) : ℂ) := by
    rw [Subgroup.coe_mul, ContinuousMonoidHom.mul_apply, Units.val_mul]
  rw [hmul]
  ring

/-- The coefficient is the integral of its diagonal integrand over `K`. -/
theorem twistedSectionCoefficient_eq_integral (χ : unramifiedCharacters ν)
    (F₀ : ProductInducedCompactPicture h K A) (g : G) :
    twistedSectionCoefficient h hU A K hK ν hν hP hm hPK hG hδP hA χ F₀ g =
      ∫ k : K, CompactInduction.integrand h hU
          (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) K g
          (twistedSection h hU A K ν hP hK hν hm (factorization_subtype hPK) χ F₀) k
        ∂CompactInduction.measure K hK :=
  CompactInduction.coefficientMap_integral h hU _ K hK hP hm hPK hG hδP _ _ g

/-- **Equivariance under the characters of `G`** (Waldspurger, proof of Prop. VI.3.1,
printed p. 303: `(E^G_P sp_{λχ} ψ)(g) = λ(g) (E^G_P sp_χ ψ)(g)`): if `Λ` is a character of
`G` trivial on `K` and `U` whose restriction to `M` is `θ`, the coefficient of the transport
of `F₀` to `A ⊗ θχ` at `g` is `Λ(g)` times the one for `A ⊗ χ`. -/
theorem twistedSectionCoefficient_mul (θ χ : unramifiedCharacters ν) (Λ : G →* ℂ)
    (hΛK : ∀ k ∈ K, Λ k = 1) (hΛU : ∀ u ∈ U, Λ u = 1)
    (hΛM : ∀ m : M, (θ.val m : ℂ) = Λ m) (F₀ : ProductInducedCompactPicture h K A) (g : G) :
    twistedSectionCoefficient h hU A K hK ν hν hP hm hPK hG hδP hA (θ * χ) F₀ g =
      Λ g * twistedSectionCoefficient h hU A K hK ν hν hP hm hPK hG hδP hA χ F₀ g := by
  rw [twistedSectionCoefficient_eq_integral, twistedSectionCoefficient_eq_integral,
    ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  obtain ⟨q, hq, k₁, hk₁, he⟩ := hPK ((k : G) * g)
  rw [integrand_twistedSection_mul h hU A K hK ν hν hP hm hPK θ χ F₀ g k ⟨k₁, hk₁⟩ ⟨q, hq⟩ he]
  congr 1
  rw [hΛM]
  have hu := h.projection_inv_mul_mem ⟨q, hq⟩
  have h1 : Λ q = Λ (h.projection ⟨q, hq⟩ : M) := by
    calc Λ q = Λ ((h.projection ⟨q, hq⟩ : M) * (((h.projection ⟨q, hq⟩ : M) : G)⁻¹ * q)) := by
          rw [mul_inv_cancel_left]
      _ = Λ (h.projection ⟨q, hq⟩ : M) * Λ (((h.projection ⟨q, hq⟩ : M) : G)⁻¹ * q) :=
          map_mul _ _ _
      _ = Λ (h.projection ⟨q, hq⟩ : M) := by rw [hΛU _ hu, mul_one]
  have h2 : Λ g = Λ q := by
    have hg : g = (k : G)⁻¹ * (q * k₁) := by rw [← he, inv_mul_cancel_left]
    rw [hg, map_mul, map_mul, hΛK _ (K.inv_mem k.2), hΛK _ hk₁, one_mul, mul_one]
  rw [h2, h1]

/-- **Continuity in the character**: along a family `y ↦ χ_y` of unitary unramified characters
whose values `χ_y(m)` are continuous in `y`, the coefficient of the transport of `F₀` to
`A ⊗ χ_y` at `g` is continuous in `y`. -/
theorem continuous_twistedSectionCoefficient {Y : Type*} [TopologicalSpace Y]
    [FirstCountableTopology Y]
    (χ : Y → unramifiedCharacters ν) (hχ : ∀ m : M, Continuous fun y => ((χ y).val m : ℂ))
    (hχu : ∀ y m, ‖((χ y).val m : ℂ)‖ = 1) (F₀ : ProductInducedCompactPicture h K A) (g : G) :
    Continuous fun y => twistedSectionCoefficient h hU A K hK ν hν hP hm hPK hG hδP hA (χ y) F₀ g := by
  choose q hq k₁ hk₁ he using fun k : K => hPK ((k : G) * g)
  have hform : ∀ y (k : K), CompactInduction.integrand h hU
      (A.twist (χ y).val.toMonoidHom (unramifiedCharacter_isOpen_ker ν (χ y))) K g
      (twistedSection h hU A K ν hP hK hν hm (factorization_subtype hPK) (χ y) F₀) k =
      ((χ y).val (h.projection ⟨q k, hq k⟩) : ℂ) *
        CompactInduction.integrand h hU
          (A.twist (1 : unramifiedCharacters ν).val.toMonoidHom
            (unramifiedCharacter_isOpen_ker ν 1)) K g
          (twistedSection h hU A K ν hP hK hν hm (factorization_subtype hPK) 1 F₀) k := by
    intro y k
    have hk := integrand_twistedSection_mul h hU A K hK ν hν hP hm hPK (χ y) 1 F₀ g k
      ⟨k₁ k, hk₁ k⟩ ⟨q k, hq k⟩ (he k)
    rw [mul_one] at hk
    exact hk
  simp_rw [twistedSectionCoefficient_eq_integral]
  refine continuous_of_dominated (bound := fun k => ‖CompactInduction.integrand h hU
      (A.twist (1 : unramifiedCharacters ν).val.toMonoidHom
        (unramifiedCharacter_isOpen_ker ν 1)) K g
      (twistedSection h hU A K ν hP hK hν hm (factorization_subtype hPK) 1 F₀) k‖)
    (fun y => ?_) (fun y => Filter.Eventually.of_forall fun k => ?_) ?_
    (Filter.Eventually.of_forall fun k => ?_)
  · exact (CompactInduction.integrand_isLocallyConstant h hU _ K _ g).continuous.aestronglyMeasurable
  · rw [hform, norm_mul, hχu, one_mul]
  · exact (CompactInduction.integrand_integrable h hU _ K hK _ g).norm
  · simp_rw [hform]
    exact (hχ _).mul continuous_const

end Twist

section Orbit

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] [SecondCountableTopology G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] {P M U : Subgroup G} [LocallyCompactSpace P]
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hP : IsClosed (P : Set G)) (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  (hG : ∀ g : G, Measure.modularCharacter g = 1)
  (hδ : ∀ p : P, Measure.modularCharacter p =
    (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer p : ℝ≥0))
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))
  (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := M))
  (hν : ∀ i, Continuous (ν i)) (hr : Continuous h.projection)
  {J : Type uJ} [Fintype J] (e : unitaryUnramifiedCharacters ν ≃* (J → Circle))
  {P₀ : Subgroup G} {δ₀ : P₀ →* ℝ≥0ˣ} {δ₀M : P₀.subgroupOf M →* ℝ≥0ˣ}
  [CompactSpace (K : Subgroup G)] [CompactSpace ((K : Subgroup G).subgroupOf M)]
  (C : Subgroup M) [C.Normal] (hC : C ≤ Subgroup.center M)
  [MeasurableSpace (M ⧸ C)] (μ : Measure (M ⧸ C)) [μ.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation μ)
  [Finite (discreteSeriesStabilizer C hC μ ν (discreteSeriesClass C hC μ π hsq))]
  (ρ : Measure (unitaryUnramifiedCharacters ν))
  (w : discreteSeriesOrbit C hC μ ν (discreteSeriesClass C hC μ π hsq) → ℂ)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- **The first bound in the proof of Prop. VI.3.1** (Waldspurger, printed p. 303): let the
torus `Im X(G)` be given in coordinates `z : L → Circle`, with characters
`g ↦ z^{n_G(g)}` for a homomorphism `n_G : G → ℤ^L` trivial on `K` and `U`, whose restriction to
`M` is the character with torus coordinates `finiteTorusMonomial a z`. For a weight `w` smooth in
the torus coordinates, a finite left invariant measure `ρ` on the unitary unramified characters,
a section `ψ = q ∈ C^∞(O, P)` and every real `r`, there is `c > 0` with
`|f_ψ(g)| ≤ c Ξ(g) (1 + ‖n_G(g)‖)^{-r}` for all `g ∈ G`. -/
theorem exists_norm_inducedOrbitWavePacket_le_xi_rpow [IsFiniteMeasure ρ] [ρ.IsMulLeftInvariant]
    (hLaurent : HasLaurentUnitaryCoordinates ν e) (he : Continuous e)
    (hws : IsSmoothFiniteTorusFunction fun y =>
      w (discreteSeriesOrbitMap C hC μ ν (discreteSeriesClass C hC μ π hsq) (e.symm y)))
    {L : Type uL} [Fintype L] (nG : G →* Multiplicative (L → ℤ)) (a : J → L → ℤ)
    (hnK : ∀ k ∈ K, nG k = 1) (hnU : ∀ u ∈ U, nG u = 1)
    (hnM : ∀ (m : M) (z : L → Circle),
      ((e.symm (finiteTorusMonomial a z)).val m : ℂ) = torusCharacter (Multiplicative.toAdd (nG m)) z)
    (hδU : IsUnimodularModulus U hU)
    (hL : LeviData (K : Subgroup G) P₀ P M δ₀
      (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) δ₀M h.projection)
    (hP₀K : IsIwasawaPair P₀ (K : Subgroup G))
    (hMK : IsIwasawaPair (P₀.subgroupOf M) ((K : Subgroup G).subgroupOf M))
    (hδ₀ : ∀ p : P₀, (p : G) ∈ K → δ₀ p = 1)
    (hcoeff : ∀ (v : π.obj) (ℓ : SmoothDual π.obj.representation),
      ∃ c : ℝ, 0 < c ∧ ∀ m, ‖ℓ.val (π.obj.representation m v)‖ ≤ c * xi hMK δ₀M m)
    (q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) (r : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ g : G,
      ‖inducedOrbitWavePacket h hU hP K hK hPK hG hδ ν π hν hr e C hC μ hsq ρ w q g‖ ≤
        c * xi hP₀K δ₀ g * (1 + ‖Multiplicative.toAdd (nG g)‖) ^ (-r) := by
  classical
  have hPK' : ∀ g : G, ∃ p ∈ P, ∃ k ∈ K, g = p * k := fun g => by
    obtain ⟨p, k, hg⟩ := hPK g
    exact ⟨p, p.2, k, k.2, hg⟩
  -- the orbit map and the weight in torus coordinates
  set W : (J → Circle) → ℂ := fun y => w (discreteSeriesOrbitMap C hC μ ν (discreteSeriesClass C hC μ π hsq) (e.symm y)) with hW
  have hWc : Continuous W := hws.continuous
  -- continuity of `w` on the orbit
  have hwc : Continuous w := by
    apply (isOpenQuotientMap_discreteSeriesOrbitMap C hC μ ν (discreteSeriesClass C hC μ π hsq)).isQuotientMap.continuous_iff.mpr
    have ht := hWc.comp he
    simpa only [Function.comp_def, W, e.symm_apply_apply] using ht
  have hwm : AEStronglyMeasurable w (discreteSeriesOrbitMeasure ν C hC μ (discreteSeriesClass C hC μ π hsq) ρ) :=
    hwc.aestronglyMeasurable
  -- the restricted family of the section and its decomposition
  let R := productInducedFamilyRestriction ν e h K hP hK hν hr hU hPK π.obj
    (productInducedOrbitPullback ν π e h hU q.val)
  have hR : R ∈ finiteSmoothFamilies J (ProductInducedCompactPicture h K π.obj) := q.property.2
  obtain ⟨n, f, v, hF⟩ := (mem_finiteSmoothFamilies_iff J _ R).mp hR
  -- the coefficients of the fixed compact vectors
  set T : unramifiedCharacters ν → ProductInducedCompactPicture h K π.obj →ₗ[ℂ]
      LocallyConstant G ℂ := fun χ =>
    twistedSectionCoefficient h hU π.obj K hK ν hν hP hr hPK' hG hδ π.property.2 χ with hT
  -- the orbit coefficient in torus coordinates
  have hcoef : ∀ (y : J → Circle) (g : G),
      unitaryOrbitCoefficientMap h hU hP K hK hPK hG hδ ν π hν hr C hC μ hsq e q
        (discreteSeriesOrbitMap C hC μ ν (discreteSeriesClass C hC μ π hsq) (e.symm y)) g =
        ∑ i, (f i).val y * T (unitaryTorusParameter ν e y) (v i) g := by
    intro y g
    rw [unitaryOrbitCoefficientMap_parameter]
    have hts : twistedSection h hU π.obj K ν hP hK hν hr (factorization_subtype hPK')
        (unitaryTorusParameter ν e y) (R y) =
        q.val (unitaryOrbitParameterRepresentative ν π e y) :=
      (productInducedCompactEquiv ν h K hP hK hν hr hU (factorization_subtype hPK')
        (unitaryTorusParameter ν e y) π.obj).symm_apply_apply _
    have hTR : T (unitaryTorusParameter ν e y) (R y) g =
        unitaryOrbitRepresentativeCoefficientMap h hU hP K hK hPK hG hδ ν π hr
          (unitaryOrbitParameterRepresentative ν π e y)
          (q.val (unitaryOrbitParameterRepresentative ν π e y)) g := by
      rw [← hts]
      rfl
    rw [← hTR, hF y, map_sum, ← LocallyConstant.evalAddMonoidHom_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LocallyConstant.evalAddMonoidHom_apply, map_smul, LocallyConstant.coe_smul,
      Pi.smul_apply, smul_eq_mul]
  -- the measure on the torus
  set μT : Measure (J → Circle) := ρ.map e with hμT
  have hem : Measurable e := he.measurable
  have : IsFiniteMeasure μT := Measure.isFiniteMeasure_map ρ e
  have : μT.IsMulLeftInvariant :=
    isMulLeftInvariant_map e.toMulHom hem e.surjective
  -- the auxiliary probability measure on the torus `Im X(G)`
  let νG : Measure (L → Circle) := Measure.haarMeasure ⊤
  have : IsProbabilityMeasure νG := ⟨by
    have := Measure.haarMeasure_self (G := L → Circle) (K₀ := ⊤)
    simpa using this⟩
  -- continuity, unitarity and equivariance of the coefficients
  have hutpc : ∀ m : M, Continuous fun y => ((unitaryTorusParameter ν e y).val m : ℂ) := by
    intro m
    obtain ⟨k, hk⟩ := hLaurent m
    have heq : (fun y => ((unitaryTorusParameter ν e y).val m : ℂ)) = torusCharacter k :=
      funext hk
    rw [heq]
    exact continuous_torusCharacter k
  have hTc : ∀ i g, Continuous fun y => T (unitaryTorusParameter ν e y) (v i) g := fun i g =>
    continuous_twistedSectionCoefficient h hU π.obj K hK ν hν hP hr hPK' hG hδ π.property.2
      (unitaryTorusParameter ν e) hutpc (fun y m => norm_unitaryTorusParameter_apply ν e y m)
      (v i) g
  have hTn : ∀ i g (z : L → Circle) (y : J → Circle),
      T (unitaryTorusParameter ν e (finiteTorusMonomial a z * y)) (v i) g =
        torusCharacter (Multiplicative.toAdd (nG g)) z *
          T (unitaryTorusParameter ν e y) (v i) g := by
    intro i g z y
    rw [unitaryTorusParameter_mul]
    exact twistedSectionCoefficient_mul h hU π.obj K hK ν hν hP hr hPK' hG hδ π.property.2
      _ _ (latticeTorusCharacter nG z)
      (fun k hk => by rw [latticeTorusCharacter_apply, hnK k hk, toAdd_one, torusCharacter_zero])
      (fun u hu => by rw [latticeTorusCharacter_apply, hnU u hu, toAdd_one, torusCharacter_zero])
      (fun m => hnM m z) (v i) g
  -- the bounds of Lemma VI.2.2 for the fixed vectors
  choose B hB0 hB using fun i => norm_twist_coefficientMap_le_xi h hU π.obj K hK ν hν hP hr hPK'
    hG hδ π.property.2 hδU hL hP₀K hMK hδ₀ hcoeff (v i)
  -- the bounds of the smooth weights along `Im X(G)`
  set k : ℕ := ⌈r⌉₊
  have hrk : r ≤ k := Nat.le_ceil r
  have hφs : ∀ i, IsSmoothFiniteTorusFunction fun y => W y * (f i).val y := fun i =>
    hws.mul (f i).property
  choose Mb hMb0 hMb using fun i =>
    exists_bound_comp_monomial_mul (hφs i) a k
  set S := Nat.card (discreteSeriesStabilizer C hC μ ν (discreteSeriesClass C hC μ π hsq))
  set c₀ : ℝ := (S : ℝ)⁻¹ * ∑ i, 2 ^ k * (1 + Fintype.card L) * Mb i * μT.real Set.univ * B i
  have hc₀ : 0 ≤ c₀ := by
    refine mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.sum_nonneg fun i _ => ?_)
    have := (hB0 i).le
    have := hMb0 i
    positivity
  refine ⟨1 + c₀, by positivity, fun g => ?_⟩
  have hxi : 0 ≤ xi hP₀K δ₀ g := integral_nonneg fun k => iwasawaWeight_nonneg _
  have hdec : 0 ≤ (1 + ‖Multiplicative.toAdd (nG g)‖) ^ (-r) :=
    Real.rpow_nonneg (by positivity) _
  -- the wave packet as a finite sum of torus integrals
  have hint : ∀ i, Integrable (fun y => (W y * (f i).val y) * T (unitaryTorusParameter ν e y) (v i) g) μT :=
    fun i => ((hφs i).continuous.mul (hTc i g)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hpar := inducedOrbitWavePacket_eq_parameterIntegral h hU hP K hK hPK hG hδ ν π hν hr e C
    hC μ hsq ρ w hLaurent he hwm q g
  have hmap : ∫ χ, w (discreteSeriesOrbitMap C hC μ ν (discreteSeriesClass C hC μ π hsq) χ) *
      unitaryOrbitCoefficientMap h hU hP K hK hPK hG hδ ν π hν hr C hC μ hsq e q
        (discreteSeriesOrbitMap C hC μ ν (discreteSeriesClass C hC μ π hsq) χ) g ∂ρ =
      ∑ i, ∫ y, (W y * (f i).val y) * T (unitaryTorusParameter ν e y) (v i) g ∂μT := by
    rw [← integral_finsetSum _ fun i _ => hint i]
    have hcont : Continuous fun y => ∑ i, (W y * (f i).val y) *
        T (unitaryTorusParameter ν e y) (v i) g :=
      continuous_finsetSum _ fun i _ => ((hφs i).continuous.mul (hTc i g))
    rw [hμT, integral_map hem.aemeasurable hcont.aestronglyMeasurable]
    refine integral_congr_ae (Filter.Eventually.of_forall fun χ => ?_)
    simp only [W, e.symm_apply_apply]
    have hc := hcoef (e χ) g
    rw [e.symm_apply_apply] at hc
    rw [hc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hpar, hmap, norm_smul, Real.norm_eq_abs, abs_inv, Nat.abs_cast]
  -- the estimate of each torus integral
  have hbound : ∀ i, ‖∫ y, (W y * (f i).val y) * T (unitaryTorusParameter ν e y) (v i) g ∂μT‖ ≤
      2 ^ k * (1 + Fintype.card L) * Mb i * μT.real Set.univ * (B i * xi hP₀K δ₀ g) *
        (1 + ‖Multiplicative.toAdd (nG g)‖) ^ (-r) := fun i =>
    norm_integral_mul_le_rpow μT νG (continuous_finiteTorusMonomial a)
      (hφs i).continuous
      (fun χ => isSmoothFiniteTorusFunction_comp_monomial_mul (hφs i) a χ)
      (hTc i g) (hTn i g) hrk (hMb i).1 (hMb i).2
      (fun χ => hB i (unitaryTorusParameter ν e χ) (norm_unitaryTorusParameter_apply ν e χ) g)
  calc (S : ℝ)⁻¹ * ‖∑ i, ∫ y, (W y * (f i).val y) * T (unitaryTorusParameter ν e y) (v i) g ∂μT‖
      ≤ (S : ℝ)⁻¹ * ∑ i, 2 ^ k * (1 + Fintype.card L) * Mb i * μT.real Set.univ *
          (B i * xi hP₀K δ₀ g) * (1 + ‖Multiplicative.toAdd (nG g)‖) ^ (-r) :=
        mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hbound i))
          (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = c₀ * xi hP₀K δ₀ g * (1 + ‖Multiplicative.toAdd (nG g)‖) ^ (-r) := by
        simp only [c₀, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    _ ≤ (1 + c₀) * xi hP₀K δ₀ g * (1 + ‖Multiplicative.toAdd (nG g)‖) ^ (-r) := by
        have := mul_nonneg hxi hdec
        nlinarith

end Orbit

end Langlands.HarishChandraSchwartz
