import Langlands.Global.AdelicEisensteinGoodPositionRootHyperplaneReduction
import Langlands.Global.AdelicGoodPositionIwasawaCompactStatement
import Langlands.Global.AdelicEisensteinConjugateCompactProof
import Langlands.Global.AdelicEisensteinFiniteCompactOperatorComparison
import Langlands.Global.AdelicEisensteinConvergenceProof
import Langlands.Global.InfiniteAdelicMaximalCompactConjugacy
import Langlands.Automorphic.GroupSchemeAutomorphicRightTranslation

/-! # Eisenstein continuations with root-hyperplane singularities for every maximal compact

`EisensteinRootHyperplaneContinuationStatement` follows from its case for maximal compact
subgroups in good position (`EisensteinGoodPositionRootHyperplaneContinuationStatement`) and
the existence of such subgroups (`GoodPositionIwasawaCompactStatement`). The infinite parts of
two maximal compact subgroups are conjugate; conjugating the compact and translating the
argument multiplies the Eisenstein series by an exponential of the parameter; a change of the
finite part of the compact replaces the series by a finite combination of series with
exponential coefficients. Both operations preserve meromorphy and root-hyperplane clearing. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Set
open scoped CategoryTheory.MonObj Manifold

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

section Helpers

variable {F : Type u} [Field F]

/-- The exponential `λ ↦ exp (c ⟨λ, v⟩)` is entire in every linear coordinate system. -/
theorem differentiable_exp_complexParameterPairing {P : GroupScheme (Spec (CommRingCat.of F))}
    {n : ℕ} (e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P) (v : RealCharacterDual F P)
    (c : ℂ) : Differentiable ℂ (fun s => Complex.exp (c * complexParameterPairing F P (e s) v)) := by
  let Lv : ComplexCharacterParameter F P →ₗ[ℂ] ℂ :=
    { toFun := fun lam => complexParameterPairing F P lam v
      map_add' := fun x y => by simp only [map_add, LinearMap.add_apply]
      map_smul' := fun z x => by
        simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply] }
  have hL : Differentiable ℂ (fun s => Lv (e s)) :=
    (LinearMap.toContinuousLinearMap (Lv.comp e.toLinearMap)).differentiable
  exact (hL.const_mul c).cexp

variable [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]

/-- Conjugation preserves maximal compact subgroups of `G(𝔸)`. -/
theorem AdelicGroupPoints.IsMaximalCompactSubgroup.map_conj {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsMaximalCompactSubgroup F G K) (t : AdelicGroupPoints F G) :
    IsMaximalCompactSubgroup F G (K.map (MulAut.conj t).toMonoidHom) := by
  let c : AdelicGroupPoints F G ≃ₜ* AdelicGroupPoints F G :=
    { MulAut.conj t with
      continuous_toFun := by
        change Continuous fun x => t * x * t⁻¹
        exact (continuous_const.mul continuous_id).mul continuous_const
      continuous_invFun := by
        change Continuous fun x => t⁻¹ * x * t
        exact (continuous_const.mul continuous_id).mul continuous_const }
  exact CompactIwasawa.IsMaximalCompact.map hK c

/-- The infinite factor of a maximal compact subgroup is its infinite projection. -/
theorem AdelicGroupPoints.IsMaximalCompactSubgroup.comap_ofInfinite_eq_map_infinite
    {K : Subgroup (AdelicGroupPoints F G)} (hK : IsMaximalCompactSubgroup F G K) :
    K.comap (ofInfinite F G).toMonoidHom = K.map (infinite F G).toMonoidHom := by
  ext k
  constructor
  · intro hk
    exact ⟨_, hk, infinite_ofInfinite F G k⟩
  · rintro ⟨x, hx, rfl⟩
    exact ((hK.mem_iff x).mp hx).1

/-- Conjugating by an infinite point conjugates the infinite projection. -/
theorem map_infinite_map_conj_ofInfinite (K : Subgroup (AdelicGroupPoints F G))
    (a : InfiniteAdelicGroupPoints F G) :
    (K.map (MulAut.conj (ofInfinite F G a)).toMonoidHom).map (infinite F G).toMonoidHom =
      (K.map (infinite F G).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  refine MonoidHom.ext fun x => ?_
  have h : infinite F G (ofInfinite F G a * x * (ofInfinite F G a)⁻¹) =
      a * infinite F G x * a⁻¹ := by
    rw [map_mul, map_mul, map_inv, infinite_ofInfinite]
  exact h

end Helpers

/-- The reduction of `EisensteinRootHyperplaneContinuationStatement` to its case for
maximal compact subgroups in good position and the existence of such subgroups. -/
def EisensteinRootHyperplaneCompactReductionStatement : Prop :=
  GoodPositionIwasawaCompactStatement.{u} →
    EisensteinGoodPositionRootHyperplaneContinuationStatement.{u} →
      EisensteinRootHyperplaneContinuationStatement.{u}

/-- **Change of the maximal compact subgroup.** -/
theorem eisensteinRootHyperplaneCompactReduction :
    EisensteinRootHyperplaneCompactReductionStatement.{u} := by
  classical
  intro hgood hGP F _ _ G P M U A _ _ _ p _ iU l a r _ _ _ hA hT hG hU K hK N d rho hsmooth
    hcalc φ hKmax hrho hφ
  have := hG.smooth
  obtain ⟨m₀, ⟨e₀⟩⟩ := exists_complexParameterEquiv hG r.isCompatible.parabolic
  have : FiniteDimensional ℂ (ComplexCharacterParameter F P) :=
    FiniteDimensional.of_injective e₀.symm.toLinearMap e₀.symm.injective
  obtain ⟨𝓕, K₀, hK₀max, hK₀, hK₀min, hK₀levi⟩ := hgood F G P p hG r.isCompatible.parabolic
  -- Conjugate the infinite part of `K` to that of `K₀`.
  obtain ⟨b, hb⟩ := InfiniteAdelicGroupPoints.infiniteAdelicMaximalCompactConjugacy F G
    (K.comap (ofInfinite F G).toMonoidHom) (K₀.comap (ofInfinite F G).toMonoidHom) hG
    hKmax.isMaximalCompact_comap_ofInfinite hK₀max.isMaximalCompact_comap_ofInfinite
  let t : AdelicGroupPoints F G := (ofInfinite F G b)⁻¹
  have htinv : t⁻¹ = ofInfinite F G b := inv_inv _
  let K' := K.map (MulAut.conj t⁻¹).toMonoidHom
  have hK' : IsIwasawaCompact p K' := hK.conjInv t
  have hK'max : IsMaximalCompactSubgroup F G K' := hKmax.map_conj t⁻¹
  have hinf : K'.map (infinite F G).toMonoidHom = K₀.map (infinite F G).toMonoidHom := by
    change (K.map (MulAut.conj t⁻¹).toMonoidHom).map (infinite F G).toMonoidHom = _
    rw [htinv, map_infinite_map_conj_ofInfinite, ← hKmax.comap_ofInfinite_eq_map_infinite, hb,
      hK₀max.comap_ofInfinite_eq_map_infinite]
  -- The translated inducing function.
  let ψ : AdelicGroupPoints F G → ℂ := fun x => φ (x * ofInfinite F G b)
  have hψ : IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
      (K₀.comap (ofInfinite F G).toMonoidHom) rho ψ := by
    have h := hφ.infiniteRightTranslate hcalc b
    rwa [hb] at h
  have hψt : (fun x => ψ (x * t)) = φ := by
    funext x
    simp only [ψ, t, inv_mul_cancel_right]
  let c₁ : ComplexCharacterParameter F P → ℂ := fun lam =>
    Complex.exp ((-1 : ℂ) * complexParameterPairing F P lam (hK'.height t))
  have hconj (lam : ComplexCharacterParameter F P) (g : AdelicGroupPoints F G) :
      hK.eisensteinSeries φ lam g = c₁ lam * hK'.eisensteinSeries ψ lam (g * t) := by
    rw [hK.eisensteinSeries_mul_conjInv t hK' ψ lam g, hψt, ← mul_assoc]
    have h1 : c₁ lam * hK'.heightPower lam t = 1 := by
      simp only [c₁, IsIwasawaCompact.heightPower, ← Complex.exp_add]
      rw [neg_one_mul, neg_add_cancel, Complex.exp_zero]
    rw [h1, one_mul]
  -- Finite change of the compact.
  obtain ⟨S, cut, hcut, htwist⟩ :=
    hψ.exists_parameterTwist_of_infinite_eq iU l hK' hK₀ hK'max hK₀max hinf
  let cv : RealCharacterDual F P → ComplexCharacterParameter F P → ℂ := fun v lam =>
    Complex.exp (complexParameterPairing F P lam v)
  have hGPv : ∀ v : S, ∃ (EP : ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ)
      (DP : Set (ComplexCharacterParameter F P)),
      (∀ g, IsMeromorphicInCoordinatesOn (fun lam => EP lam g) DP) ∧
      (∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam →
        EP lam = hK₀.eisensteinSeries (cut v) lam) ∧
      ∀ (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P) (s₀ : Fin n → ℂ),
        ∃ (S : Finset (characterLattice A)) (m : ℕ) (W : Set (Fin n → ℂ)),
          (S : Set (characterLattice A)) ⊆ r.unipotentRoots ∧ IsOpen W ∧ s₀ ∈ W ∧
          ∀ g : AdelicGroupPoints F G, ∃ h : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ h W ∧
            ∀ s ∈ W, e s ∈ DP →
              h s = (∏ β ∈ S, r.rootFunctional hA hT β (e s - e s₀)) ^ m * EP (e s) g :=
    fun v => hGP F G P M U A p iU l a r hA hT hG hU 𝓕 K₀ hK₀ hK₀min hK₀levi rho hsmooth hcalc
      (cut v) hK₀max hrho (hcut v v.2)
  choose EPv DPv hmerov hagreev hclearv using hGPv
  choose Ra hRa using hagreev
  have hsumv : ∀ v : S, ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam →
      ∀ g, Summable (hK₀.eisensteinTerm (cut v) lam g) := fun v =>
    eisensteinAbsoluteConvergence.exists_summable_eisensteinTerm r hA hT hG hU hK₀ rho hsmooth
      hcalc hK₀max hrho (hcut v v.2)
  choose Rs hRs using hsumv
  let EP : ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ := fun lam g =>
    c₁ lam * ∑ v : S, cv v lam * EPv v lam (g * t)
  let DP : Set (ComplexCharacterParameter F P) := ⋂ v : S, DPv v
  have hDPv (v : S) : IsOpenDenseInCoordinates (DPv v) :=
    (hmerov v 1).isOpenDenseInCoordinates
  have hDP : IsOpenDenseInCoordinates DP := fun n e => by
    rw [preimage_iInter]
    exact ⟨isOpen_iInter_of_finite fun v => (hDPv v n e).1,
      dense_iInter_of_isOpen (fun v => (hDPv v n e).1) fun v => (hDPv v n e).2⟩
  let B : ℝ := ∑ v : S, (max (Rs v) 0 + max (Ra v) 0)
  have hB (v : S) : max (Rs v) 0 + max (Ra v) 0 ≤ B :=
    Finset.single_le_sum (f := fun w : S => max (Rs w) 0 + max (Ra w) 0)
      (fun w _ => add_nonneg (le_max_right _ _) (le_max_right _ _)) (Finset.mem_univ v)
  have hBs (v : S) : Rs v ≤ B :=
    (le_max_left (Rs v) 0).trans ((le_add_of_nonneg_right (le_max_right (Ra v) 0)).trans (hB v))
  have hBa (v : S) : Ra v ≤ B :=
    (le_max_left (Ra v) 0).trans ((le_add_of_nonneg_left (le_max_right (Rs v) 0)).trans (hB v))
  have hc₁ : ∀ (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P),
      Differentiable ℂ (c₁ ∘ e) := fun n e =>
    differentiable_exp_complexParameterPairing e (hK'.height t) (-1)
  have hcv : ∀ (v : RealCharacterDual F P) (n : ℕ)
      (e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P), Differentiable ℂ (cv v ∘ e) :=
    fun v n e => by
      show Differentiable ℂ (fun s => Complex.exp (complexParameterPairing F P (e s) v))
      simpa only [one_mul] using differentiable_exp_complexParameterPairing e v 1
  refine ⟨EP, DP, fun g => ?_, ⟨B, fun lam hlam => funext fun g => ?_⟩, fun n e s₀ => ?_⟩
  · -- Meromorphy.
    have hterm (v : S) : IsMeromorphicInCoordinatesOn
        (fun lam => cv v lam * EPv v lam (g * t)) DP :=
      ((isMeromorphicInCoordinatesOn_univ (hcv v)).mul (hmerov v (g * t))).congr_mono hDP
        (fun x hx => ⟨mem_univ x, mem_iInter.1 hx v⟩) (fun _ _ => rfl)
    have hsum := IsMeromorphicInCoordinatesOn.sum Finset.univ hDP (fun v _ => hterm v)
    exact ((isMeromorphicInCoordinatesOn_univ hc₁).mul hsum).congr_mono hDP
      (fun x hx => ⟨mem_univ x, hx⟩) (fun x _ => by simp only [EP, Pi.mul_apply, Finset.sum_apply])
  · -- Agreement with the series.
    have hsum : ∑ v : S, cv v lam * EPv v lam (g * t) =
        ∑ v : S, cv v lam * hK₀.eisensteinSeries (cut v) lam (g * t) :=
      Finset.sum_congr rfl fun v _ => by
        rw [hRa v lam (ParabolicRootPresentation.IsRegularParameter.mono r hA hT (hBa v) hlam)]
    change c₁ lam * ∑ v : S, cv v lam * EPv v lam (g * t) = hK.eisensteinSeries φ lam g
    rw [hsum, Finset.sum_coe_sort S (fun v => cv v lam * hK₀.eisensteinSeries (cut v) lam (g * t)),
      ← hK'.eisensteinSeries_eq_finset_sum_of_twist hK₀ S (fun v => cv v lam) ψ cut lam
        (htwist lam) (g * t) (fun v hv => hRs ⟨v, hv⟩ lam
          (ParabolicRootPresentation.IsRegularParameter.mono r hA hT (hBs ⟨v, hv⟩) hlam) (g * t)),
      hconj lam g]
  · -- Root-hyperplane clearing.
    choose Sv mv Wv hSv hWv hs₀v hhv using fun v : S => hclearv v n e s₀
    let Sr : Finset (characterLattice A) := Finset.univ.biUnion Sv
    let Mx : ℕ := ∑ v : S, mv v
    let W : Set (Fin n → ℂ) := ⋂ v : S, Wv v
    refine ⟨Sr, Mx, W, ?_, isOpen_iInter_of_finite hWv, mem_iInter.2 hs₀v, fun g => ?_⟩
    · intro β hβ
      obtain ⟨v, -, hβv⟩ := Finset.mem_biUnion.1 hβ
      exact hSv v hβv
    choose hv hhvd hhveq using fun v : S => hhv v (g * t)
    let Lr : characterLattice A → (Fin n → ℂ) → ℂ := fun β s =>
      r.rootFunctional hA hT β (e s - e s₀)
    let Q : S → (Fin n → ℂ) → ℂ := fun v s =>
      (∏ β ∈ Sv v, Lr β s) ^ (Mx - mv v) * (∏ β ∈ Sr \ Sv v, Lr β s) ^ Mx
    have hQ (v : S) : Differentiable ℂ (Q v) :=
      (differentiable_centeredLinearProduct (r.rootFunctional hA hT) e s₀ (Sv v) (Mx - mv v)).mul
        (differentiable_centeredLinearProduct (r.rootFunctional hA hT) e s₀ (Sr \ Sv v) Mx)
    refine ⟨fun s => c₁ (e s) * ∑ v : S, cv v (e s) * (Q v s * hv v s), ?_, ?_⟩
    · refine (hc₁ n e).differentiableOn.mul (DifferentiableOn.fun_sum fun v _ => ?_)
      exact (hcv v n e).differentiableOn.mul ((hQ v).differentiableOn.mul
        ((hhvd v).mono (iInter_subset _ v)))
    · intro s hsW hsD
      have key (v : S) : Q v s * hv v s =
          (∏ β ∈ Sr, Lr β s) ^ Mx * EPv v (e s) (g * t) := by
        rw [hhveq v s (mem_iInter.1 hsW v) (mem_iInter.1 hsD v)]
        have hsplit : ∏ β ∈ Sr, Lr β s =
            (∏ β ∈ Sr \ Sv v, Lr β s) * ∏ β ∈ Sv v, Lr β s :=
          (Finset.prod_sdiff (Finset.subset_biUnion_of_mem Sv (Finset.mem_univ v))).symm
        have hle : mv v ≤ Mx :=
          Finset.single_le_sum (f := mv) (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
        calc Q v s * ((∏ β ∈ Sv v, Lr β s) ^ mv v * EPv v (e s) (g * t))
            = ((∏ β ∈ Sv v, Lr β s) ^ (Mx - mv v) * (∏ β ∈ Sv v, Lr β s) ^ mv v) *
                (∏ β ∈ Sr \ Sv v, Lr β s) ^ Mx * EPv v (e s) (g * t) := by
              simp only [Q]; ring
          _ = (∏ β ∈ Sr, Lr β s) ^ Mx * EPv v (e s) (g * t) := by
              rw [← pow_add, Nat.sub_add_cancel hle, hsplit, mul_pow]; ring
      change c₁ (e s) * ∑ v : S, cv v (e s) * (Q v s * hv v s) =
        (∏ β ∈ Sr, Lr β s) ^ Mx * (c₁ (e s) * ∑ v : S, cv v (e s) * EPv v (e s) (g * t))
      simp only [key, Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      ring

/-- `EisensteinRootHyperplaneContinuationStatement` from the function-valued continuation of
Eisenstein series, the injectivity of leading cuspidal components, the weighted majorants of
cusp forms, the root-hyperplane form of the cuspidal tests and the existence of maximal compact
subgroups in good position. -/
theorem eisensteinRootHyperplaneContinuation_of_premises
    (hCont : EisensteinMeromorphicContinuationStatement.{u})
    (hinj : LeadingCuspidalInjectivityStatement.{u})
    (hmaj : LeviCuspFormPairingMajorantStatement.{u})
    (htest : EisensteinCuspidalTestRootHyperplaneStatement.{u})
    (hgood : GoodPositionIwasawaCompactStatement.{u}) :
    EisensteinRootHyperplaneContinuationStatement.{u} :=
  eisensteinRootHyperplaneCompactReduction hgood
    (eisensteinGoodPositionRootHyperplaneReduction hCont hinj hmaj htest)

end Langlands.Global
