import Langlands.Representation.Archimedean.RealLeviModes
import Langlands.Representation.Archimedean.PrincipalSeriesAnnihilator
import Langlands.Representation.Archimedean.GKModuleDensity

/-!
# The quotient of the dual principal series by the annihilator of a standard module

Let `ds` be a list of real blocks of rank `N`, `χ` its position characters, `X` the
`O(N)`-finite functions of its standard module and `Y^∨` the `O(N)`-finite functions of the
principal series of the inverse characters `χ⁻¹`. The pairing `⟨v, x⟩ = ∫_{O(N)} v x` is
invariant under right translation by `O(N)` and under right derivatives. Its annihilator
`N_ds ⊆ Y^∨` of `X` (`nullSpace`) is a `(𝔤, K)`-submodule, and the quotient
`Z = Y^∨ / N_ds` is a `(𝔤𝔩_N(ℝ), O(N))`-module (`zRep`, `zLie`).

If `X` is irreducible, `Z` satisfies the hypotheses of Schur's lemma and Jacobson density
(`GKModuleDensity.Hyp`): `Z` is irreducible (by the double annihilator theorem
`RealLeviModes.mem_kFin_standard_of_annihilates` and orthogonal vectors), admissible (by lifting
`O(N)`-intertwiners through orthogonal complements for the `L²(O(N))` inner product),
`O(N)`-finite, with continuous matrix coefficients. Independently of irreducibility, for every
proper `O(N)`-stable subspace `W` of `X` some `u ∈ Y^∨` annihilates `W` but not `X`
(`RealLeviDualityStatement`, proof `realLeviDuality`).
-/

noncomputable section

open MeasureTheory Matrix ComplexConjugate

open scoped Manifold ContDiff Matrix.Norms.Operator InnerProductSpace TensorProduct

namespace Langlands.Archimedean

open Langlands.GeneralLinear Langlands.HarmonicAnalysis Langlands.LocalFactor.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

attribute [local instance 100] LieRing.ofAssociativeRing

namespace RealLeviDuality

/-! ## Quotients of `(𝔤, K)`-modules -/

section Quotient

universe uK uL uV

variable {K : Type uK} [Group K] {L : Type uL} [LieRing L] [LieAlgebra ℂ L]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The action of `L` on the quotient by a stable subspace. -/
def quotLie (π : L →ₗ⁅ℂ⁆ Module.End ℂ V) (W : Submodule ℂ V)
    (h : ∀ X : L, W ≤ W.comap (π X)) : L →ₗ⁅ℂ⁆ Module.End ℂ (V ⧸ W) where
  toFun X := W.mapQ W (π X) (h X)
  map_add' X Y := by
    ext v
    simp
  map_smul' c X := by
    ext v
    simp
  map_lie' := by
    intro X Y
    ext v
    simp only [LieRing.of_associative_ring_bracket, LieHom.map_lie, LinearMap.coe_comp,
      Function.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply, LinearMap.sub_apply,
      Module.End.mul_apply, Submodule.Quotient.mk_sub]

@[simp]
theorem quotLie_mk (π : L →ₗ⁅ℂ⁆ Module.End ℂ V) (W : Submodule ℂ V)
    (h : ∀ X : L, W ≤ W.comap (π X)) (X : L) (v : V) :
    quotLie π W h X (Submodule.Quotient.mk v) = Submodule.Quotient.mk (π X v) :=
  rfl

theorem quotient_finite (ρ : Representation ℂ K V) (W : Submodule ℂ V)
    (h : ∀ k : K, W ≤ W.comap (ρ k))
    (hfin : ∀ v : V, FiniteVectors.IsFiniteVector ρ v) (z : V ⧸ W) :
    ∃ F : Submodule ℂ (V ⧸ W), z ∈ F ∧ FiniteDimensional ℂ F ∧
      ∀ (k : K), ∀ w ∈ F, ρ.quotient W h k w ∈ F := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective W z
  have : Module.Finite ℂ (FiniteVectors.orbitSpan ρ v) := hfin v
  refine ⟨(FiniteVectors.orbitSpan ρ v).map W.mkQ,
    ⟨v, FiniteVectors.self_mem_orbitSpan ρ v, rfl⟩, inferInstance, ?_⟩
  rintro k _ ⟨w, hw, rfl⟩
  exact ⟨ρ k w, (FiniteVectors.orbitSubrepresentation ρ v).apply_mem_toSubmodule k hw, rfl⟩

theorem quotient_continuous [TopologicalSpace K] (ρ : Representation ℂ K V) (W : Submodule ℂ V)
    (h : ∀ k : K, W ≤ W.comap (ρ k))
    (hc : ∀ (v : V) (ℓ : V →ₗ[ℂ] ℂ), Continuous fun k : K => ℓ (ρ k v))
    (z : V ⧸ W) (ℓ : V ⧸ W →ₗ[ℂ] ℂ) :
    Continuous fun k : K => ℓ (ρ.quotient W h k z) := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective W z
  exact hc v (ℓ ∘ₗ W.mkQ)

end Quotient

/-! ## Lifting `K`-intertwiners through quotients of unitary representations -/

section Lift

open PrincipalSeriesAnnihilator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {G : Type*} [Group G]
  (ρ : Representation ℂ G E)
  (hiso : ∀ (g : G) (x y : E), ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
  (hfin : ∀ x : E, FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun g => ρ g x)))
  (W : Submodule ℂ E) (hW : ∀ g : G, W ≤ W.comap (ρ g))

include hiso hfin in
/-- An intertwiner from a matrix representation into a quotient of a unitary representation
with finite-dimensional orbit spans lifts to an intertwiner into the representation: lift the
images of the standard basis vectors, then subtract their orthogonal projections onto the
intersection of `W` with the finite-dimensional span of their orbits. -/
theorem exists_lift_of_mem_gkIntertwiners {d : ℕ} (τ : G →* Matrix (Fin d) (Fin d) ℂ)
    {T : (Fin d → ℂ) →ₗ[ℂ] E ⧸ W} (hT : T ∈ gkIntertwiners (ρ.quotient W hW) d τ) :
    ∃ S ∈ gkIntertwiners ρ d τ, W.mkQ ∘ₗ S = T := by
  classical
  choose v hv using fun i : Fin d => Submodule.Quotient.mk_surjective W (T (Pi.single i 1))
  set F : Submodule ℂ E := ⨆ i, Submodule.span ℂ (Set.range fun g => ρ g (v i)) with hFdef
  have hFs : IsStable ρ F := isStable_iSup fun i => isStable_span_orbit (v i)
  have : ∀ i, FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun g => ρ g (v i))) :=
    fun i => hfin (v i)
  have : FiniteDimensional ℂ F := by
    rw [hFdef]
    infer_instance
  have hvF : ∀ i, v i ∈ F := fun i =>
    Submodule.mem_iSup_of_mem i (Submodule.subset_span ⟨1, by simp⟩)
  set P : Submodule ℂ E := F ⊓ W with hPdef
  have hPs : IsStable ρ P := isStable_inf hFs fun g x hx => hW g hx
  have : FiniteDimensional ℂ P := Submodule.finiteDimensional_of_le inf_le_left
  have : CompleteSpace P := FiniteDimensional.complete ℂ P
  set u : Fin d → E := fun i => v i - P.starProjection (v i) with hudef
  have huF : ∀ i, u i ∈ F := fun i =>
    F.sub_mem (hvF i) (inf_le_left (b := W) (P.starProjection_apply_mem (v i)))
  have huP : ∀ i, u i ∈ Pᗮ := fun i => P.sub_starProjection_mem_orthogonal (v i)
  set S : (Fin d → ℂ) →ₗ[ℂ] E := Fintype.linearCombination ℂ u with hSdef
  have hSmem : ∀ (A : Submodule ℂ E), (∀ i, u i ∈ A) → ∀ x, S x ∈ A := by
    intro A hA x
    have hx : S x ∈ LinearMap.range S := LinearMap.mem_range_self S x
    rw [hSdef, Fintype.range_linearCombination] at hx
    exact Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hA i) hx
  have hST : W.mkQ ∘ₗ S = T := by
    refine LinearMap.pi_ext fun i c => ?_
    have hsingle : (Pi.single i c : Fin d → ℂ) = c • Pi.single i 1 := by
      ext j
      by_cases hj : j = i
      · subst hj
        simp
      · simp [hj]
    have hu : W.mkQ (u i) = T (Pi.single i 1) := by
      simp only [hudef, map_sub, Submodule.mkQ_apply]
      rw [hv i, (Submodule.Quotient.mk_eq_zero W).mpr
        (inf_le_right (a := F) (P.starProjection_apply_mem (v i))), sub_zero]
    rw [LinearMap.comp_apply, hSdef, Fintype.linearCombination_apply_single, map_smul, hu,
      hsingle, map_smul]
  refine ⟨S, fun g x => ?_, hST⟩
  have hDF : S (τ g *ᵥ x) - ρ g (S x) ∈ F :=
    F.sub_mem (hSmem F huF _) (hFs g _ (hSmem F huF x))
  have hDP : S (τ g *ᵥ x) - ρ g (S x) ∈ Pᗮ :=
    Pᗮ.sub_mem (hSmem Pᗮ huP _) (isStable_orthogonal hiso hPs g _ (hSmem Pᗮ huP x))
  have hDW : S (τ g *ᵥ x) - ρ g (S x) ∈ W := by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub]
    have h1 : (Submodule.Quotient.mk (S (τ g *ᵥ x)) : E ⧸ W) = T (τ g *ᵥ x) :=
      LinearMap.congr_fun hST _
    have h2 : (Submodule.Quotient.mk (ρ g (S x)) : E ⧸ W) = ρ.quotient W hW g (T x) := by
      rw [← LinearMap.congr_fun hST x]
      rfl
    rw [h1, h2, hT g x, sub_self]
  have hD : S (τ g *ᵥ x) - ρ g (S x) ∈ P ⊓ Pᗮ := ⟨⟨hDF, hDW⟩, hDP⟩
  rw [P.inf_orthogonal_eq_bot, Submodule.mem_bot, sub_eq_zero] at hD
  exact hD

include hiso hfin in
/-- Quotients of admissible unitary representations with finite-dimensional orbit spans are
admissible. -/
theorem isAdmissible_quotient [TopologicalSpace G] (hadm : IsAdmissibleGKModule ρ) :
    IsAdmissibleGKModule (ρ.quotient W hW) := by
  intro d τ hτ
  have := hadm d τ hτ
  let Φ : gkIntertwiners ρ d τ →ₗ[ℂ] gkIntertwiners (ρ.quotient W hW) d τ :=
    { toFun := fun S => ⟨W.mkQ ∘ₗ (S : (Fin d → ℂ) →ₗ[ℂ] E), fun g x => by
        rw [LinearMap.comp_apply, S.2 g x]
        rfl⟩
      map_add' := fun S T => Subtype.ext (LinearMap.comp_add _ _ _)
      map_smul' := fun c S => Subtype.ext (LinearMap.comp_smul _ _ _) }
  refine Module.Finite.of_surjective Φ fun T => ?_
  obtain ⟨S, hS, hST⟩ := exists_lift_of_mem_gkIntertwiners ρ hiso hfin W hW τ T.2
  exact ⟨⟨S, hS⟩, Subtype.ext hST⟩

end Lift

/-! ## The pairing between principal series of inverse characters -/

section Pairing

open RealPrincipalSeriesDuality PartialJacquet RealBlockFourierFinite

attribute [local instance] measurableSpaceK

local instance borelSpaceK_ld (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

variable {N : ℕ} {χ : ℕ → ℝˣ → ℂ} {e : ℕ → ℂ}

theorem toUnits_mk (k : Langlands.GeneralLinear N ℝ) (hk : k ∈ unitaryCompact ℝ N) :
    (Unitary.toUnits (⟨(k : Matrix (Fin N) (Fin N) ℝ), hk⟩ : Matrix.unitaryGroup (Fin N) ℝ) :
      Langlands.GeneralLinear N ℝ) = k :=
  Units.ext rfl

/-- Right translation by `k ∈ O(N)` moves across the pairing as right translation by `k⁻¹`. -/
theorem integral_rightTranslation_mul (v x : Langlands.GeneralLinear N ℝ → ℂ)
    {k : Langlands.GeneralLinear N ℝ} (hk : k ∈ unitaryCompact ℝ N) :
    ∫ κ : unitaryCompact ℝ N,
        Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℝ) k v κ * x κ ∂haarK N =
      ∫ κ : unitaryCompact ℝ N,
        v κ * Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℝ) k⁻¹ x κ ∂haarK N := by
  rw [← integral_mul_right_eq_self (μ := haarK N) (fun κ : unitaryCompact ℝ N =>
    v κ * Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℝ) k⁻¹ x κ) ⟨k, hk⟩]
  refine integral_congr_ae (ae_of_all _ fun κ => ?_)
  show v (κ * k) * x κ = v (κ * k) * x (κ * k * k⁻¹)
  rw [mul_inv_cancel_right]

/-- The pairing of right derivatives: `⟨R(X) v, x⟩ = -⟨v, R(X) x⟩`. -/
theorem integral_rightDerivative_mul (hχ : IsSignedPower χ e)
    {v x : Langlands.GeneralLinear N ℝ → ℂ} (hv : v ∈ principalSeries ℝ N (dualChar χ))
    (hx : x ∈ principalSeries ℝ N χ) (X : Matrix (Fin N) (Fin N) ℝ) :
    ∫ κ : unitaryCompact ℝ N, rightDerivative (matrixModel ℝ N) X v κ * x κ ∂haarK N =
      -∫ κ : unitaryCompact ℝ N, v κ * rightDerivative (matrixModel ℝ N) X x κ ∂haarK N := by
  have hχ' : ∀ (i : ℕ) (y : ℝˣ), dualChar χ i y * χ i y = 1 :=
    fun i y => inv_mul_cancel₀ (hχ.ne_zero i y)
  have hdv := rightDerivative_mem_principalSeries (dualChar χ) hv X
  have hdx := rightDerivative_mem_principalSeries χ hx X
  have h0 := integral_rightDerivative_eq_zero (contMDiff_mul_fun hv.1 hx.1)
    (isModulusEquivariant_mul hχ' hv hx) X
  have hsum : ∫ κ : unitaryCompact ℝ N, rightDerivative (matrixModel ℝ N) X v κ * x κ ∂haarK N +
      ∫ κ : unitaryCompact ℝ N, v κ * rightDerivative (matrixModel ℝ N) X x κ ∂haarK N = 0 := by
    rw [← integral_add (integrable_mul_of_continuous hdv.1.continuous hx.1.continuous)
      (integrable_mul_of_continuous hv.1.continuous hdx.1.continuous), ← h0]
    refine integral_congr_ae (ae_of_all _ fun κ => ?_)
    exact (rightDerivative_mul_fun hv.1 hx.1 X _).symm
  exact eq_neg_of_add_eq_zero_left hsum

/-- `O(N)`-finite functions of the principal series of `χ` have conjugates on `O(N)` in the
principal series of `χ⁻¹`. -/
theorem exists_conj_mem_dual (hχ : IsSignedPower χ e) {x : Langlands.GeneralLinear N ℝ → ℂ}
    (hx : x ∈ kFiniteFunctions (principalSeries ℝ N χ) (unitaryCompact ℝ N)) :
    ∃ v ∈ kFiniteFunctions (principalSeries ℝ N (dualChar χ)) (unitaryCompact ℝ N),
      ∀ k ∈ unitaryCompact ℝ N, v k = conj (x k) := by
  refine RealLeviModes.exists_ext_conj hχ.dual hx.1.1.continuous hx.2 fun i g => ?_
  rw [apply_signReflection_mul hχ.one hx.1 i g,
    JacquetKernel.conj_eq_inv_of_norm_eq_one (hχ.dual.norm_neg_one i), dualChar, inv_inv]

/-- `O(N)`-finite functions of the principal series of `χ⁻¹` have conjugates on `O(N)` in the
principal series of `χ`. -/
theorem exists_conj_mem_of_dual (hχ : IsSignedPower χ e) {v : Langlands.GeneralLinear N ℝ → ℂ}
    (hv : v ∈ kFiniteFunctions (principalSeries ℝ N (dualChar χ)) (unitaryCompact ℝ N)) :
    ∃ x ∈ kFiniteFunctions (principalSeries ℝ N χ) (unitaryCompact ℝ N),
      ∀ k ∈ unitaryCompact ℝ N, x k = conj (v k) := by
  refine RealLeviModes.exists_ext_conj hχ hv.1.1.continuous hv.2 fun i g => ?_
  rw [apply_signReflection_mul hχ.dual.one hv.1 i g, dualChar,
    JacquetKernel.conj_eq_inv_of_norm_eq_one (hχ.norm_neg_one i)]

theorem integral_conj_mul_self_ne_zero {x : Langlands.GeneralLinear N ℝ → ℂ} (hx : Continuous x)
    {k₀ : Langlands.GeneralLinear N ℝ} (hk₀ : k₀ ∈ unitaryCompact ℝ N) (h : x k₀ ≠ 0) :
    ∫ κ : unitaryCompact ℝ N, conj (x κ) * x κ ∂haarK N ≠ 0 := by
  intro h0
  have h1 : ∫ κ : unitaryCompact ℝ N, ‖x κ‖ ^ 2 ∂haarK N = 0 := by
    have e1 : ∫ κ : unitaryCompact ℝ N, conj (x κ) * x κ ∂haarK N =
        ((∫ κ : unitaryCompact ℝ N, ‖x κ‖ ^ 2 ∂haarK N : ℝ) : ℂ) := by
      refine (integral_congr_ae (ae_of_all _ fun κ => ?_)).trans integral_complex_ofReal
      exact PrincipalSeriesAnnihilator.conj_mul_self_eq _
    rw [e1] at h0
    exact_mod_cast h0
  exact h (RealLeviModes.eq_zero_of_integral_norm_sq_eq_zero hx h1 k₀ hk₀)

end Pairing

/-! ## The annihilator of the standard module and the quotient -/

section Null

open RealPrincipalSeriesDuality PartialJacquet RealInducedStandardBound

attribute [local instance] measurableSpaceK

variable (N : ℕ) (ds : List RealBlock)

/-- The `O(N)`-finite functions of the principal series of the inverse position characters. -/
abbrev DualSpace : Submodule ℂ (Langlands.GeneralLinear N ℝ → ℂ) :=
  kFiniteFunctions (principalSeries ℝ N (dualChar (realPositionCharacter ds))) (unitaryCompact ℝ N)

/-- The `O(N)`-finite functions of the standard module. -/
abbrev StdSpace : Submodule ℂ (Langlands.GeneralLinear N ℝ → ℂ) :=
  kFiniteFunctions (realStandardModule N ds) (unitaryCompact ℝ N)

variable {N ds}

theorem continuous_of_mem_dualSpace {v : Langlands.GeneralLinear N ℝ → ℂ}
    (hv : v ∈ DualSpace N ds) : Continuous v :=
  hv.1.1.continuous

theorem continuous_of_mem_stdSpace {x : Langlands.GeneralLinear N ℝ → ℂ}
    (hx : x ∈ StdSpace N ds) : Continuous x :=
  hx.1.1.1.continuous

theorem mem_kFin_of_mem_stdSpace {x : Langlands.GeneralLinear N ℝ → ℂ} (hx : x ∈ StdSpace N ds) :
    x ∈ kFiniteFunctions (principalSeries ℝ N (realPositionCharacter ds)) (unitaryCompact ℝ N) :=
  ⟨hx.1.1, hx.2⟩

variable (N ds)

/-- The annihilator in `DualSpace` of a subset `A` of functions. -/
def annihilator (A : Set (Langlands.GeneralLinear N ℝ → ℂ)) (hA : ∀ x ∈ A, Continuous x) :
    Submodule ℂ (DualSpace N ds) where
  carrier := {v | ∀ x ∈ A,
    ∫ κ : unitaryCompact ℝ N, (v : Langlands.GeneralLinear N ℝ → ℂ) κ * x κ ∂haarK N = 0}
  add_mem' {v w} hv hw x hx := by
    have h1 : Integrable (fun κ : unitaryCompact ℝ N =>
        (v : Langlands.GeneralLinear N ℝ → ℂ) κ * x κ) (haarK N) :=
      RealLeviModes.integrable_of_continuous
        (G := fun g => (v : Langlands.GeneralLinear N ℝ → ℂ) g * x g)
        ((continuous_of_mem_dualSpace v.2).mul (hA x hx))
    have h2 : Integrable (fun κ : unitaryCompact ℝ N =>
        (w : Langlands.GeneralLinear N ℝ → ℂ) κ * x κ) (haarK N) :=
      RealLeviModes.integrable_of_continuous
        (G := fun g => (w : Langlands.GeneralLinear N ℝ → ℂ) g * x g)
        ((continuous_of_mem_dualSpace w.2).mul (hA x hx))
    show ∫ κ : unitaryCompact ℝ N, ((v : Langlands.GeneralLinear N ℝ → ℂ) κ +
      (w : Langlands.GeneralLinear N ℝ → ℂ) κ) * x κ ∂haarK N = 0
    simp only [add_mul]
    rw [integral_add h1 h2, hv x hx, hw x hx, add_zero]
  zero_mem' x _ := by simp
  smul_mem' c v hv x hx := by
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc] at hv ⊢
    rw [integral_const_mul, hv x hx, mul_zero]

/-- The annihilator of the standard module. -/
def nullSpace : Submodule ℂ (DualSpace N ds) :=
  annihilator N ds (StdSpace N ds) fun _ hx => continuous_of_mem_stdSpace hx

variable {N ds}

theorem mem_nullSpace {v : DualSpace N ds} :
    v ∈ nullSpace N ds ↔ ∀ x ∈ StdSpace N ds,
      ∫ κ : unitaryCompact ℝ N, (v : Langlands.GeneralLinear N ℝ → ℂ) κ * x κ ∂haarK N = 0 :=
  Iff.rfl

variable (N ds)

theorem nullSpace_le_comap_rep (k : Matrix.unitaryGroup (Fin N) ℝ) :
    nullSpace N ds ≤
      (nullSpace N ds).comap (principalSeriesRep ℝ N (dualChar (realPositionCharacter ds)) k) := by
  intro v hv x hx
  show ∫ κ : unitaryCompact ℝ N, Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℝ)
    (Unitary.toUnits k) (v : Langlands.GeneralLinear N ℝ → ℂ) κ * x κ ∂haarK N = 0
  have hk : (Unitary.toUnits k : Langlands.GeneralLinear N ℝ) ∈ unitaryCompact ℝ N := k.2
  rw [integral_rightTranslation_mul _ _ hk]
  exact hv _ (rightTranslation_mem_kFiniteFunctions_realStandardModule N ds hx
    ((unitaryCompact ℝ N).inv_mem hk))

theorem coe_principalSeriesLie_tmul (χ : ℕ → ℝˣ → ℂ) (z : ℂ) (X : Matrix (Fin N) (Fin N) ℝ)
    (v : kFiniteFunctions (principalSeries ℝ N χ) (unitaryCompact ℝ N)) :
    ((principalSeriesLie ℝ N χ (z ⊗ₜ X) v : kFiniteFunctions (principalSeries ℝ N χ)
        (unitaryCompact ℝ N)) : Langlands.GeneralLinear N ℝ → ℂ) =
      z • rightDerivative (matrixModel ℝ N) X (v : Langlands.GeneralLinear N ℝ → ℂ) := by
  rw [principalSeriesLie, kFiniteLie_tmul]
  rfl

theorem nullSpace_le_comap_lie (X : ℂ ⊗[ℝ] Matrix (Fin N) (Fin N) ℝ) :
    nullSpace N ds ≤
      (nullSpace N ds).comap (principalSeriesLie ℝ N (dualChar (realPositionCharacter ds)) X) := by
  have hχ := RealStrictCharacterLanglandsQuotient.isSignedPower ds
  induction X using TensorProduct.inductionOn with
  | tmul z Y =>
    intro v hv x hx
    show ∫ κ : unitaryCompact ℝ N, ((principalSeriesLie ℝ N (dualChar (realPositionCharacter ds))
      (z ⊗ₜ Y) v : DualSpace N ds) : Langlands.GeneralLinear N ℝ → ℂ) κ * x κ ∂haarK N = 0
    rw [coe_principalSeriesLie_tmul]
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [integral_const_mul, integral_rightDerivative_mul hχ v.2.1 hx.1.1 Y,
      hv _ (rightDerivative_mem_kFiniteFunctions_realStandardModule N ds hx Y), neg_zero,
      mul_zero]
  | add X Y hX hY =>
    intro v hv
    simp only [Submodule.mem_comap, map_add, LinearMap.add_apply]
    exact (nullSpace N ds).add_mem (hX hv) (hY hv)

/-- The quotient `Z = Y^∨ / N_ds`. -/
abbrev Zq : Type := DualSpace N ds ⧸ nullSpace N ds

/-- Right translation by `O(N)` on `Z`. -/
def zRep : Representation ℂ (Matrix.unitaryGroup (Fin N) ℝ) (Zq N ds) :=
  (principalSeriesRep ℝ N (dualChar (realPositionCharacter ds))).quotient (nullSpace N ds)
    (nullSpace_le_comap_rep N ds)

/-- The right-derivative action of `ℂ ⊗_ℝ 𝔤𝔩_N(ℝ)` on `Z`. -/
def zLie : (ℂ ⊗[ℝ] Matrix (Fin N) (Fin N) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ (Zq N ds) :=
  quotLie (principalSeriesLie ℝ N (dualChar (realPositionCharacter ds))) (nullSpace N ds)
    (nullSpace_le_comap_lie N ds)

@[simp]
theorem zRep_mk (k : Matrix.unitaryGroup (Fin N) ℝ) (v : DualSpace N ds) :
    zRep N ds k (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (principalSeriesRep ℝ N (dualChar (realPositionCharacter ds)) k v) :=
  rfl

@[simp]
theorem zLie_mk (X : ℂ ⊗[ℝ] Matrix (Fin N) (Fin N) ℝ) (v : DualSpace N ds) :
    zLie N ds X (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (principalSeriesLie ℝ N (dualChar (realPositionCharacter ds)) X v) :=
  rfl

end Null

/-! ## Irreducibility and the hypotheses of the density theorem -/

section Hyp

open RealPrincipalSeriesDuality PartialJacquet RealInducedStandardBound PrincipalSeriesAnnihilator

attribute [local instance] measurableSpaceK

variable {N : ℕ} {ds : List RealBlock}

theorem integral_mul_congr_left {v v' : Langlands.GeneralLinear N ℝ → ℂ}
    (x : Langlands.GeneralLinear N ℝ → ℂ) (h : ∀ k ∈ unitaryCompact ℝ N, v k = v' k) :
    ∫ κ : unitaryCompact ℝ N, v κ * x κ ∂haarK N = ∫ κ : unitaryCompact ℝ N, v' κ * x κ ∂haarK N :=
  integral_congr_ae (ae_of_all _ fun κ => congrArg (· * x κ) (h κ κ.2))

theorem integral_mul_congr_right (v : Langlands.GeneralLinear N ℝ → ℂ)
    {x x' : Langlands.GeneralLinear N ℝ → ℂ} (h : ∀ k ∈ unitaryCompact ℝ N, x k = x' k) :
    ∫ κ : unitaryCompact ℝ N, v κ * x κ ∂haarK N = ∫ κ : unitaryCompact ℝ N, v κ * x' κ ∂haarK N :=
  integral_congr_ae (ae_of_all _ fun κ => congrArg (v κ * ·) (h κ κ.2))

/-- `∫ v · R(k) x = ∫ R(k⁻¹) v · x` for `k ∈ O(N)`. -/
theorem integral_mul_rightTranslation (v x : Langlands.GeneralLinear N ℝ → ℂ)
    {k : Langlands.GeneralLinear N ℝ} (hk : k ∈ unitaryCompact ℝ N) :
    ∫ κ : unitaryCompact ℝ N,
        v κ * Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℝ) k x κ ∂haarK N =
      ∫ κ : unitaryCompact ℝ N,
        Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℝ) k⁻¹ v κ * x κ ∂haarK N := by
  have h := integral_rightTranslation_mul v x ((unitaryCompact ℝ N).inv_mem hk)
  rw [inv_inv] at h
  exact h.symm

theorem eq_zero_of_mem_stdSpace {x : Langlands.GeneralLinear N ℝ → ℂ} (hx : x ∈ StdSpace N ds)
    (h : ∀ k ∈ unitaryCompact ℝ N, x k = 0) : x = 0 :=
  eq_zero_of_mem_principalSeries_of_eqOn_unitaryCompact hx.1.1 h

/-- **Double annihilator.** An `O(N)`-finite function of the principal series of `χ`
annihilated by `N_ds` lies in the standard module. -/
theorem mem_stdSpace_of_annihilates (hN : realRank ds = N) {x : Langlands.GeneralLinear N ℝ → ℂ}
    (hx : x ∈ kFiniteFunctions (principalSeries ℝ N (realPositionCharacter ds))
      (unitaryCompact ℝ N))
    (h : ∀ v ∈ nullSpace N ds,
      ∫ κ : unitaryCompact ℝ N, (v : Langlands.GeneralLinear N ℝ → ℂ) κ * x κ ∂haarK N = 0) :
    x ∈ StdSpace N ds :=
  RealLeviModes.mem_kFin_standard_of_annihilates hN hx fun v hv hnull =>
    h ⟨v, hv⟩ fun _ hx' => RealLeviModes.integral_mul_eq_zero_of_mem_standard hv hnull hx'

theorem coe_realStandardLie_tmul (z : ℂ) (X : Matrix (Fin N) (Fin N) ℝ) (x : StdSpace N ds) :
    ((realStandardLie N ds (z ⊗ₜ X) x : StdSpace N ds) : Langlands.GeneralLinear N ℝ → ℂ) =
      z • rightDerivative (matrixModel ℝ N) X (x : Langlands.GeneralLinear N ℝ → ℂ) := by
  rw [realStandardLie, kFiniteLie_tmul]
  rfl

variable (N ds)

/-- The annihilator in `StdSpace` of a subspace of `DualSpace`. -/
def stdAnnihilator (B : Submodule ℂ (DualSpace N ds)) : Submodule ℂ (StdSpace N ds) where
  carrier := {x | ∀ v ∈ B, ∫ κ : unitaryCompact ℝ N,
    (v : Langlands.GeneralLinear N ℝ → ℂ) κ * (x : Langlands.GeneralLinear N ℝ → ℂ) κ ∂haarK N = 0}
  add_mem' {x y} hx hy v hv := by
    have h1 : Integrable (fun κ : unitaryCompact ℝ N =>
        (v : Langlands.GeneralLinear N ℝ → ℂ) κ * (x : Langlands.GeneralLinear N ℝ → ℂ) κ)
        (haarK N) :=
      RealLeviModes.integrable_of_continuous
        (G := fun g => (v : Langlands.GeneralLinear N ℝ → ℂ) g * (x : Langlands.GeneralLinear N ℝ → ℂ) g)
        ((continuous_of_mem_dualSpace v.2).mul (continuous_of_mem_stdSpace x.2))
    have h2 : Integrable (fun κ : unitaryCompact ℝ N =>
        (v : Langlands.GeneralLinear N ℝ → ℂ) κ * (y : Langlands.GeneralLinear N ℝ → ℂ) κ)
        (haarK N) :=
      RealLeviModes.integrable_of_continuous
        (G := fun g => (v : Langlands.GeneralLinear N ℝ → ℂ) g * (y : Langlands.GeneralLinear N ℝ → ℂ) g)
        ((continuous_of_mem_dualSpace v.2).mul (continuous_of_mem_stdSpace y.2))
    show ∫ κ : unitaryCompact ℝ N, (v : Langlands.GeneralLinear N ℝ → ℂ) κ *
      ((x : Langlands.GeneralLinear N ℝ → ℂ) κ + (y : Langlands.GeneralLinear N ℝ → ℂ) κ)
        ∂haarK N = 0
    simp only [mul_add]
    rw [integral_add h1 h2, hx v hv, hy v hv, add_zero]
  zero_mem' v _ := by simp
  smul_mem' c x hx v hv := by
    show ∫ κ : unitaryCompact ℝ N, (v : Langlands.GeneralLinear N ℝ → ℂ) κ *
      (c * (x : Langlands.GeneralLinear N ℝ → ℂ) κ) ∂haarK N = 0
    simp only [mul_left_comm _ c]
    rw [integral_const_mul, hx v hv, mul_zero]

variable {N ds}

theorem stdAnnihilator_stable_rep {B : Submodule ℂ (DualSpace N ds)}
    (hB : ∀ (k : Matrix.unitaryGroup (Fin N) ℝ), ∀ v ∈ B,
      principalSeriesRep ℝ N (dualChar (realPositionCharacter ds)) k v ∈ B)
    (k : Matrix.unitaryGroup (Fin N) ℝ) :
    ∀ x ∈ stdAnnihilator N ds B, realStandardRep N ds k x ∈ stdAnnihilator N ds B := by
  intro x hx v hv
  have hk : (Unitary.toUnits k : Langlands.GeneralLinear N ℝ) ∈ unitaryCompact ℝ N := k.2
  show ∫ κ : unitaryCompact ℝ N, (v : Langlands.GeneralLinear N ℝ → ℂ) κ *
    Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℝ) (Unitary.toUnits k)
      (x : Langlands.GeneralLinear N ℝ → ℂ) κ ∂haarK N = 0
  rw [integral_mul_rightTranslation _ _ hk]
  have hinv : (Unitary.toUnits k : Langlands.GeneralLinear N ℝ)⁻¹ = Unitary.toUnits k⁻¹ :=
    (map_inv _ _).symm
  rw [hinv]
  exact hx _ (hB k⁻¹ v hv)

theorem stdAnnihilator_stable_lie {B : Submodule ℂ (DualSpace N ds)}
    (hB : ∀ (X : ℂ ⊗[ℝ] Matrix (Fin N) (Fin N) ℝ), ∀ v ∈ B,
      principalSeriesLie ℝ N (dualChar (realPositionCharacter ds)) X v ∈ B)
    (X : ℂ ⊗[ℝ] Matrix (Fin N) (Fin N) ℝ) :
    ∀ x ∈ stdAnnihilator N ds B, realStandardLie N ds X x ∈ stdAnnihilator N ds B := by
  have hχ := RealStrictCharacterLanglandsQuotient.isSignedPower ds
  induction X using TensorProduct.inductionOn with
  | tmul z Y =>
    intro x hx v hv
    show ∫ κ : unitaryCompact ℝ N, (v : Langlands.GeneralLinear N ℝ → ℂ) κ *
      ((realStandardLie N ds (z ⊗ₜ Y) x : StdSpace N ds) : Langlands.GeneralLinear N ℝ → ℂ) κ
        ∂haarK N = 0
    rw [coe_realStandardLie_tmul]
    simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ z]
    rw [integral_const_mul, ← neg_neg (∫ κ : unitaryCompact ℝ N, _ ∂haarK N),
      ← integral_rightDerivative_mul hχ v.2.1 (mem_kFin_of_mem_stdSpace x.2).1 Y]
    have h1 := hx _ (hB (1 ⊗ₜ Y) v hv)
    rw [coe_principalSeriesLie_tmul, one_smul] at h1
    rw [h1, neg_zero, mul_zero]
  | add X Y hX hY =>
    intro x hx
    rw [map_add, LinearMap.add_apply]
    exact (stdAnnihilator N ds B).add_mem (hX x hx) (hY x hx)

theorem exists_not_mem_nullSpace (x : StdSpace N ds) (hx : x ≠ 0) :
    ∃ v : DualSpace N ds, v ∉ nullSpace N ds := by
  have hχ := RealStrictCharacterLanglandsQuotient.isSignedPower ds
  obtain ⟨k₀, hk₀, hne⟩ : ∃ k₀ ∈ unitaryCompact ℝ N,
      (x : Langlands.GeneralLinear N ℝ → ℂ) k₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (Subtype.ext (eq_zero_of_mem_stdSpace x.2 h))
  obtain ⟨v, hv, hvc⟩ := exists_conj_mem_dual hχ (mem_kFin_of_mem_stdSpace x.2)
  refine ⟨⟨v, hv⟩, fun hnull => ?_⟩
  refine integral_conj_mul_self_ne_zero (continuous_of_mem_stdSpace x.2) hk₀ hne ?_
  rw [← integral_mul_congr_left _ hvc]
  exact hnull _ x.2

variable (N ds)

theorem isIrreducible_z (hN : realRank ds = N)
    (hX : IsIrreducibleGKModule (realStandardRep N ds) (realStandardLie N ds)) :
    IsIrreducibleGKModule (zRep N ds) (zLie N ds) := by
  have hχ := RealStrictCharacterLanglandsQuotient.isSignedPower ds
  refine ⟨?_, fun S hSK hSL => ?_⟩
  · have := hX.1
    obtain ⟨x, hx⟩ := exists_ne (0 : StdSpace N ds)
    obtain ⟨v, hv⟩ := exists_not_mem_nullSpace x hx
    exact ⟨⟨Submodule.Quotient.mk v, 0, fun h => hv ((Submodule.Quotient.mk_eq_zero _).mp h)⟩⟩
  by_cases hS : S = ⊤
  · exact Or.inr hS
  left
  set S' : Submodule ℂ (DualSpace N ds) := S.comap (nullSpace N ds).mkQ with hS'def
  have hnS' : nullSpace N ds ≤ S' := fun v hv => by
    show Submodule.Quotient.mk v ∈ S
    rw [(Submodule.Quotient.mk_eq_zero _).mpr hv]
    exact S.zero_mem
  suffices hle : S' ≤ nullSpace N ds by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    exact (Submodule.mem_bot ℂ).mpr ((Submodule.Quotient.mk_eq_zero _).mpr (hle hz))
  have hS'K : ∀ (k : Matrix.unitaryGroup (Fin N) ℝ), ∀ v ∈ S',
      principalSeriesRep ℝ N (dualChar (realPositionCharacter ds)) k v ∈ S' :=
    fun k v hv => hSK k _ hv
  have hS'L : ∀ (X : ℂ ⊗[ℝ] Matrix (Fin N) (Fin N) ℝ), ∀ v ∈ S',
      principalSeriesLie ℝ N (dualChar (realPositionCharacter ds)) X v ∈ S' :=
    fun X v hv => hSL X _ hv
  obtain ⟨f, hf⟩ : ∃ f : DualSpace N ds, f ∉ S' := by
    by_contra h
    push Not at h
    apply hS
    rw [eq_top_iff]
    intro z _
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    exact h v
  set W : Submodule ℂ (Langlands.GeneralLinear N ℝ → ℂ) := S'.map (DualSpace N ds).subtype
    with hWdef
  have hWX : W ≤ DualSpace N ds := by
    rintro _ ⟨v, _, rfl⟩
    exact v.2
  have hWK : ∀ k ∈ unitaryCompact ℝ N, ∀ w ∈ W,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℝ) k w ∈ W := by
    rintro k hk _ ⟨v, hv, rfl⟩
    refine ⟨principalSeriesRep ℝ N (dualChar (realPositionCharacter ds))
      ⟨(k : Matrix (Fin N) (Fin N) ℝ), hk⟩ v, hS'K _ v hv, ?_⟩
    rw [Submodule.subtype_apply, principalSeriesRep_apply_coe, toUnits_mk]
    rfl
  have hfW : (f : Langlands.GeneralLinear N ℝ → ℂ) ∉ W := by
    rintro ⟨v, hv, hvf⟩
    exact hf (Subtype.ext hvf ▸ hv)
  obtain ⟨w0, hw0, ⟨k1, hk1⟩, horth⟩ :=
    principalSeriesOrthogonalVector N _ W f hWX hWK f.2 hfW
  obtain ⟨x0, hx0, hx0c⟩ := exists_conj_mem_of_dual hχ hw0
  have hS'x0 : ∀ v ∈ S',
      ∫ κ : unitaryCompact ℝ N, (v : Langlands.GeneralLinear N ℝ → ℂ) κ * x0 κ ∂haarK N = 0 := by
    intro v hv
    rw [integral_mul_congr_right _ hx0c]
    exact horth _ ⟨v, hv, rfl⟩
  have hx0X : x0 ∈ StdSpace N ds :=
    mem_stdSpace_of_annihilates hN hx0 fun v hv => hS'x0 v (hnS' hv)
  have hA : stdAnnihilator N ds S' = ⊤ := by
    refine (hX.2 _ (stdAnnihilator_stable_rep hS'K) (stdAnnihilator_stable_lie hS'L)).resolve_left
      fun hbot => ?_
    have hmem : (⟨x0, hx0X⟩ : StdSpace N ds) ∈ stdAnnihilator N ds S' := hS'x0
    rw [hbot, Submodule.mem_bot] at hmem
    have h0 : x0 k1 = 0 := by
      have := congrArg (fun y : StdSpace N ds => (y : Langlands.GeneralLinear N ℝ → ℂ) k1) hmem
      simpa using this
    rw [hx0c _ k1.2, map_eq_zero] at h0
    exact hk1 h0
  intro v hv x hx
  have hmem : (⟨x, hx⟩ : StdSpace N ds) ∈ stdAnnihilator N ds S' := hA ▸ Submodule.mem_top
  exact hmem v hv

theorem admissible_z : IsAdmissibleGKModule (zRep N ds) := by
  set χ' := dualChar (realPositionCharacter ds)
  let ρE : Representation ℂ (Matrix.unitaryGroup (Fin N) ℝ) (KFin N χ') :=
    principalSeriesRep ℝ N χ'
  have hiso : ∀ (g : Matrix.unitaryGroup (Fin N) ℝ) (x y : KFin N χ'),
      ⟪ρE g x, ρE g y⟫_ℂ = ⟪x, y⟫_ℂ :=
    fun g x y => rho_isometry ⟨Unitary.toUnits g, g.2⟩ x y
  have hfin : ∀ x : KFin N χ', FiniteDimensional ℂ
      (Submodule.span ℂ (Set.range fun g => ρE g x)) := by
    intro x
    have := finiteDimensional_orbit (n := N) (χ := χ') x
    refine Submodule.finiteDimensional_of_le
      (S₂ := Submodule.span ℂ (Set.range fun k => rho (n := N) (χ := χ') k x))
      (Submodule.span_le.mpr ?_)
    rintro _ ⟨g, rfl⟩
    exact Submodule.subset_span ⟨⟨Unitary.toUnits g, g.2⟩, rfl⟩
  have hadm : IsAdmissibleGKModule ρE :=
    isAdmissibleGKModule_kFiniteRep (V := principalSeries ℝ N χ') _ le_rfl
  exact isAdmissible_quotient ρE hiso hfin (nullSpace N ds) (nullSpace_le_comap_rep N ds) hadm

theorem hyp_z (hN : realRank ds = N)
    (hX : IsIrreducibleGKModule (realStandardRep N ds) (realStandardLie N ds)) :
    GKModuleDensity.Hyp (zRep N ds) (zLie N ds) where
  irreducible := isIrreducible_z N ds hN hX
  admissible := admissible_z N ds
  finite := quotient_finite _ _ _ fun v => kFiniteRep_isFiniteVector _ _ v
  continuous := quotient_continuous _ _ _ fun v ℓ =>
    kFiniteRep_continuous (principalSeries ℝ N (dualChar (realPositionCharacter ds)))
      (fun _ hf => hf.1) _ v ℓ

end Hyp

/-! ## Relative annihilators of proper `O(N)`-stable subspaces -/

section Relative

open RealPrincipalSeriesDuality PartialJacquet RealInducedStandardBound PrincipalSeriesAnnihilator

attribute [local instance] measurableSpaceK

variable {N : ℕ} {ds : List RealBlock}

/-- For every proper `O(N)`-stable subspace `W` of the standard module some `u ∈ Y^∨`
annihilates `W` but not the whole standard module: take a nonzero vector `v` of the principal
series of `χ` orthogonal to `W + X^⊥` (it is not orthogonal to `X`) and let `u` extend
`conj v` from `O(N)`. -/
theorem exists_annihilator_not_null (W : Submodule ℂ (StdSpace N ds))
    (hWK : ∀ (k : Matrix.unitaryGroup (Fin N) ℝ), ∀ w ∈ W, realStandardRep N ds k w ∈ W)
    (hW : W ≠ ⊤) :
    ∃ u ∈ DualSpace N ds,
      (∀ w ∈ W, ∫ κ : unitaryCompact ℝ N,
        u κ * (w : Langlands.GeneralLinear N ℝ → ℂ) κ ∂haarK N = 0) ∧
      ∃ x ∈ StdSpace N ds, ∫ κ : unitaryCompact ℝ N, u κ * x κ ∂haarK N ≠ 0 := by
  have hχ := RealStrictCharacterLanglandsQuotient.isSignedPower ds
  obtain ⟨x1, hx1⟩ : ∃ x1 : StdSpace N ds, x1 ∉ W := by
    by_contra h
    push Not at h
    exact hW (eq_top_iff.mpr fun x _ => h x)
  set χ := realPositionCharacter ds with hχdef
  set X' : Submodule ℂ (KFin N χ) := (StdSpace N ds).comap KFin.toFunLinear with hX'def
  set W' : Submodule ℂ (KFin N χ) := (W.map (StdSpace N ds).subtype).comap KFin.toFunLinear
    with hW'def
  have hX'K : IsStable (rho (n := N) (χ := χ)) X' := fun k x hx =>
    rightTranslation_mem_kFiniteFunctions_realStandardModule N ds hx k.2
  have hW'X' : W' ≤ X' := by
    rintro x ⟨w, _, hw⟩
    show KFin.toFunLinear x ∈ StdSpace N ds
    rw [← hw]
    exact w.2
  have hW'K : IsStable (rho (n := N) (χ := χ)) W' := by
    rintro k x ⟨w, hw, hwx⟩
    refine ⟨realStandardRep N ds ⟨((k : Langlands.GeneralLinear N ℝ) :
      Matrix (Fin N) (Fin N) ℝ), k.2⟩ w, hWK _ w hw, ?_⟩
    show Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℝ)
        (Unitary.toUnits ⟨((k : Langlands.GeneralLinear N ℝ) : Matrix (Fin N) (Fin N) ℝ), k.2⟩)
        (w : Langlands.GeneralLinear N ℝ → ℂ) =
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℝ) (k : Langlands.GeneralLinear N ℝ)
        x.toFun
    rw [toUnits_mk (k : Langlands.GeneralLinear N ℝ) k.2]
    exact congrArg _ hwx
  set W1 : Submodule ℂ (KFin N χ) := W' ⊔ X'ᗮ with hW1def
  have hW1K : IsStable (rho (n := N) (χ := χ)) W1 := by
    intro k x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add]
    exact Submodule.add_mem_sup (hW'K k a ha) (isStable_orthogonal rho_isometry hX'K k b hb)
  set x1' : KFin N χ := KFin.mk (x1 : Langlands.GeneralLinear N ℝ → ℂ)
    (mem_kFin_of_mem_stdSpace x1.2) with hx1'def
  have hx1'X : x1' ∈ X' := x1.2
  have hx1' : x1' ∉ W1 := by
    intro hmem
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hmem
    have hbX : b ∈ X' := by
      have : b = x1' - a := by
        rw [← hab]
        abel
      rw [this]
      exact X'.sub_mem hx1'X (hW'X' ha)
    have hb0 : b = 0 := by
      have := Submodule.mem_inf.mpr ⟨hbX, hb⟩
      rwa [X'.inf_orthogonal_eq_bot, Submodule.mem_bot] at this
    rw [hb0, add_zero] at hab
    obtain ⟨w, hw, hwa⟩ := ha
    apply hx1
    have hwx : w = x1 := by
      apply Subtype.ext
      exact hwa.trans (congrArg KFin.toFun hab)
    exact hwx ▸ hw
  obtain ⟨v, hv0, hv⟩ := exists_ne_zero_inner_eq_zero_kfin W1 hW1K hx1'
  have hvX : v ∉ X'ᗮ := by
    intro hvperp
    exact hv0 (inner_self_eq_zero.mp (hv v (Submodule.mem_sup_right hvperp)))
  rw [Submodule.mem_orthogonal'] at hvX
  push Not at hvX
  obtain ⟨x, hxX, hxv⟩ := hvX
  obtain ⟨u, hu, huc⟩ := exists_conj_mem_dual hχ v.toFun_mem
  refine ⟨u, hu, fun w hw => ?_, x.toFun, hxX, ?_⟩
  · rw [integral_mul_congr_left _ huc]
    have h := hv (KFin.mk (w : Langlands.GeneralLinear N ℝ → ℂ) (mem_kFin_of_mem_stdSpace w.2))
      (Submodule.mem_sup_left ⟨w, hw, rfl⟩)
    rw [inner_eq] at h
    exact h
  · rw [integral_mul_congr_left _ huc]
    rw [inner_eq] at hxv
    exact hxv

end Relative

end RealLeviDuality

open RealPrincipalSeriesDuality RealInducedStandardBound PartialJacquet in
attribute [local instance] measurableSpaceK in
/-- **The dual quotient of a real standard module.** Let `ds` be a list of real blocks of rank
`N`, `χ` its position characters, `X` the `O(N)`-finite functions of its standard module and
`Y^∨` the `O(N)`-finite functions of the principal series of `χ⁻¹`. If `X` is an irreducible
`(𝔤𝔩_N(ℝ), O(N))`-module, the quotient `Z = Y^∨ / N_ds` of `Y^∨` by the annihilator
`N_ds = {v | ∀ x ∈ X, ∫_{O(N)} v x = 0}`, with right translation by `O(N)` (`zRep`) and right
derivatives (`zLie`), satisfies the hypotheses of Schur's lemma and Jacobson density
(`GKModuleDensity.Hyp`: irreducible, admissible, `O(N)`-finite, continuous matrix
coefficients). For every proper `O(N)`-stable subspace `W` of `X` there is `u ∈ Y^∨` with
`∫_{O(N)} u w = 0` for all `w ∈ W` and `∫_{O(N)} u x ≠ 0` for some `x ∈ X`. -/
def RealLeviDualityStatement : Prop :=
  ∀ (N : ℕ) (ds : List RealBlock), realRank ds = N →
    (IsIrreducibleGKModule (realStandardRep N ds) (realStandardLie N ds) →
      GKModuleDensity.Hyp (RealLeviDuality.zRep N ds) (RealLeviDuality.zLie N ds)) ∧
    ∀ W : Submodule ℂ (kFiniteFunctions (realStandardModule N ds) (unitaryCompact ℝ N)),
      (∀ (k : Matrix.unitaryGroup (Fin N) ℝ), ∀ w ∈ W, realStandardRep N ds k w ∈ W) →
      W ≠ ⊤ →
      ∃ u ∈ kFiniteFunctions (principalSeries ℝ N (dualChar (realPositionCharacter ds)))
          (unitaryCompact ℝ N),
        (∀ w ∈ W, ∫ k : unitaryCompact ℝ N,
          u k * (w : Langlands.GeneralLinear N ℝ → ℂ) k ∂haarK N = 0) ∧
        ∃ x ∈ kFiniteFunctions (realStandardModule N ds) (unitaryCompact ℝ N),
          ∫ k : unitaryCompact ℝ N, u k * x k ∂haarK N ≠ 0

theorem realLeviDuality : RealLeviDualityStatement := fun N ds hN =>
  ⟨RealLeviDuality.hyp_z N ds hN, fun W hWK hW =>
    RealLeviDuality.exists_annihilator_not_null W hWK hW⟩

end Langlands.Archimedean
