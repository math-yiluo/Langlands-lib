import Langlands.AlgebraicGeometry.LangWeil.CurvePlaneFibrePoints
import Langlands.AlgebraicGeometry.LangWeil.CurvePlanePolynomial
import Langlands.AlgebraicGeometry.LangWeil.CurvePlaneZeroDimensional
import Langlands.Algebra.GenericIrreducibilityGenericFibre
import Langlands.Algebra.GenericIrreducibilityFractionTensor
import Langlands.AnthropicFLT.P2M.Sol.S_Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType

/-!
# Affine curves over a domain and plane curves over finite fields

For a finite type algebra `R` over a Noetherian domain `A` whose generic fibre is geometrically
irreducible of dimension one, away from one nonzero element of `A` the `κ`-points of `R` over
finite fields `κ` differ from the zeros of an absolutely irreducible plane polynomial of
bounded degrees by a bounded number.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.LangWeil.CurvePlane

/-- Uniform plane-model comparison for affine curves over a Noetherian domain. -/
def AffineCurvePlaneComparison : Prop :=
  ∀ (A R K : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [CommRing R] [Algebra A R] [Algebra.FiniteType A R]
    [Field K] [Algebra A K] [IsFractionRing A K],
    (nilradical (AlgebraicClosure K ⊗[A] R)).IsPrime →
    ringKrullDim (K ⊗[A] R) = 1 →
    ∃ a : A, a ≠ 0 ∧ ∃ B : ℕ,
      ∀ (κ : Type u) [Field κ] [Finite κ] [Algebra A κ],
        algebraMap A κ a ≠ 0 → B < Nat.card κ →
        ∃ p : MvPolynomial (Fin 2) κ,
          Irreducible (MvPolynomial.map (algebraMap κ (AlgebraicClosure κ)) p) ∧
          0 < p.degreeOf 0 ∧ p.degreeOf 0 ≤ B ∧
          0 < p.degreeOf 1 ∧ p.degreeOf 1 ≤ B ∧
          |(Nat.card (R →ₐ[A] κ) : ℝ) -
            (Nat.card {v : Fin 2 → κ // MvPolynomial.eval v p = 0} : ℝ)| ≤ B

open Langlands.Algebra.GenericIrreducibilitySpreading
open Langlands.Algebra.GenericIrreducibilityReduction

section Auxiliary

/-- A quotient by an ideal of nilpotent elements has the same Krull dimension. -/
theorem ringKrullDim_quotient_of_le_nilradical {S : Type*} [CommRing S] (J : Ideal S)
    (hJ : J ≤ nilradical S) : ringKrullDim (S ⧸ J) = ringKrullDim S := by
  have h : PrimeSpectrum.zeroLocus (R := S) J = Set.univ := by
    apply Set.eq_univ_of_forall
    intro P
    exact (PrimeSpectrum.mem_zeroLocus _ _).mpr fun x hx => nilradical_le_prime P.asIdeal (hJ hx)
  rw [ringKrullDim_quotient, h]
  exact Order.krullDim_eq_of_orderIso (OrderIso.Set.univ)

/-- Primality of the nilradical descends from the algebraic closure to the field. -/
theorem nilradical_tensor_isPrime_of_algebraicClosure {A B F : Type*} [CommRing A] [CommRing B]
    [Field F] [Algebra A B] [Algebra A F]
    (h : (nilradical (AlgebraicClosure F ⊗[A] B)).IsPrime) :
    (nilradical (F ⊗[A] B)).IsPrime := by
  let e := Algebra.TensorProduct.cancelBaseChange A F F (AlgebraicClosure F) B
  let i : F ⊗[A] B →ₐ[F] AlgebraicClosure F ⊗[F] (F ⊗[A] B) :=
    Algebra.TensorProduct.includeRight
  have hi : Function.Injective i :=
    Algebra.TensorProduct.includeRight_injective (algebraMap F (AlgebraicClosure F)).injective
  exact nilradical_isPrime_of_injective (e.toRingHom.comp i.toRingHom) (e.injective.comp hi) h

/-- Algebra maps from a finite type algebra to a finite ring are finite in number. -/
theorem finite_algHom_of_finiteType {A D κ : Type*} [CommRing A] [CommRing D] [CommRing κ]
    [Algebra A D] [Algebra A κ] [Algebra.FiniteType A D] [Finite κ] :
    Finite (D →ₐ[A] κ) := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType A D)
  refine Finite.of_injective (fun φ : D →ₐ[A] κ => fun i : Fin n => φ (f (MvPolynomial.X i))) ?_
  intro φ₁ φ₂ h
  have h2 : φ₁.comp f = φ₂.comp f := MvPolynomial.algHom_ext fun i => congrFun h i
  ext x
  obtain ⟨y, rfl⟩ := hf x
  exact AlgHom.congr_fun h2 y

theorem card_eq_card_subtype_add_card_subtype_not {α : Type*} [Finite α] (p : α → Prop) :
    Nat.card α = Nat.card {x // p x} + Nat.card {x // ¬p x} := by
  classical
  rw [← Nat.card_sum, Nat.card_congr (Equiv.sumCompl p)]

theorem eval_map_eq_eval_uniqueAlgEquiv {A κ : Type*} [CommRing A] [CommRing κ] (f : A →+* κ)
    (g : MvPolynomial (Fin 1) A) (t : κ) :
    MvPolynomial.eval (fun _ => t) (MvPolynomial.map f g) =
      ((MvPolynomial.uniqueAlgEquiv A (Fin 1) g).map f).eval t := by
  rw [MvPolynomial.eval_map, Polynomial.eval_map]
  exact (MvPolynomial.eval₂_uniqueAlgEquiv (a := fun _ => t)).symm

end Auxiliary

section Dimension

/-- If `C` becomes integral over a polynomial ring in `d` algebraically independent elements
after inverting `r`, and `r` is nonzero in the field `K`, then `K ⊗[A] C` has dimension `d`. -/
theorem ringKrullDim_tensor_eq_of_integral_after_away
    {A C K : Type*} [CommRing A] [CommRing C] [Field K] [Algebra A C] [Algebra A K] {d : ℕ}
    (z : Fin d → C) (hz : AlgebraicIndependent A z) (r : A) (hr : algebraMap A K r ≠ 0)
    (hint : ∀ c : C, ∃ n : ℕ, IsIntegral (Algebra.adjoin A (Set.range z)) (r ^ n • c)) :
    ringKrullDim (K ⊗[A] C) = d := by
  classical
  let T := K ⊗[A] C
  let t : C →ₐ[A] T := Algebra.TensorProduct.includeRight
  let P := MvPolynomial (Fin d) K
  let ψ : P →ₐ[K] T := MvPolynomial.aeval (fun i => t (z i))
  have hψ : Function.Injective ψ := tensor_aeval_injective_of_integral_after_away z hz r hr hint
  let _ : Algebra P T := ψ.toRingHom.toAlgebra
  have hψmap : ∀ p : MvPolynomial (Fin d) A,
      ψ (MvPolynomial.map (algebraMap A K) p) = t (MvPolynomial.aeval z p) := by
    intro p
    change MvPolynomial.aeval (fun i => t (z i)) (MvPolynomial.map (algebraMap A K) p) =
      t (MvPolynomial.aeval z p)
    rw [MvPolynomial.aeval_map_algebraMap, ← MvPolynomial.comp_aeval_apply]
  let R' := Algebra.adjoin A (Set.range z)
  let φ : R' →+* P := (MvPolynomial.map (algebraMap A K)).comp
    (hz.aevalEquiv.symm.toAlgHom : R' →+* MvPolynomial (Fin d) A)
  have hφ : (algebraMap P T).comp φ = t.toRingHom.comp (algebraMap R' C) := by
    apply RingHom.ext
    intro x
    change ψ (MvPolynomial.map (algebraMap A K) (hz.aevalEquiv.symm x)) = t (algebraMap R' C x)
    rw [hψmap, ← hz.algebraMap_aevalEquiv, AlgEquiv.apply_symm_apply]
  have hint' : ∀ c : C, IsIntegral P (t c) := by
    intro c
    obtain ⟨n, hn⟩ := hint c
    have h1 : IsIntegral P (t (r ^ n • c)) := IsIntegral.map_of_comp_eq φ t.toRingHom hφ hn
    have hk : algebraMap A K (r ^ n) ≠ 0 := by
      rw [map_pow]
      exact pow_ne_zero n hr
    have heq : t (r ^ n • c) = t c * algebraMap P T (MvPolynomial.C (algebraMap A K (r ^ n))) := by
      change t (r ^ n • c) = t c * ψ (MvPolynomial.C (algebraMap A K (r ^ n)))
      rw [MvPolynomial.aeval_C, ← IsScalarTower.algebraMap_apply, map_smul, Algebra.smul_def,
        mul_comm]
    refine IsIntegral.of_mul_unit (y := algebraMap P T (MvPolynomial.C (algebraMap A K (r ^ n))))
      (r := MvPolynomial.C (algebraMap A K (r ^ n))⁻¹) ?_ ?_
    · rw [← map_mul, ← map_mul, inv_mul_cancel₀ hk, map_one, map_one]
    · rw [← heq]
      exact h1
  have hintT : Algebra.IsIntegral P T := by
    constructor
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul k c =>
      have hkc : (k ⊗ₜ[A] c : T) = algebraMap P T (MvPolynomial.C k) * t c := by
        change _ = ψ (MvPolynomial.C k) * (1 ⊗ₜ c)
        rw [MvPolynomial.aeval_C, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul,
          one_mul, Algebra.algebraMap_self, RingHom.id_apply, mul_one]
      rw [hkc]
      exact isIntegral_algebraMap.mul (hint' c)
    | add x y hx hy => exact hx.add hy
  rw [← P2MW.S_Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType.P2mDimFormula.ringKrullDim_eq_of_isIntegral_of_injective
    (R := P) (S := T) hψ,
    P2MW.S_Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType.P2mDimFormula.ringKrullDim_mvPolynomial_fin]

end Dimension

section Count

/-- For a one-dimensional hypersurface model, the `κ`-points of `C` and the zeros of the plane
polynomial differ by at most the `κ`-points of `C ⧸ (g(z))` plus the zeros over the roots of
`g`. -/
theorem abs_card_sub_card_zeros_le
    {A C κ : Type u} [CommRing A] [IsDomain A] [CommRing C]
    [Field κ] [Finite κ] [Algebra A C] [Algebra A κ] [Algebra.FiniteType A C]
    (z : Fin 1 → C) (hz : AlgebraicIndependent A z) (w : C)
    (F : Polynomial (MvPolynomial (Fin 1) A)) (hFm : F.Monic)
    (hFroot : F.eval₂ (MvPolynomial.aeval z : MvPolynomial (Fin 1) A →ₐ[A] C).toRingHom w = 0)
    (hFirr : Irreducible (F.map (MvPolynomial.map (algebraMap A κ))))
    (g : MvPolynomial (Fin 1) A) (r : A) (hr : algebraMap A κ r ≠ 0)
    (hint : ∀ c : C, ∃ n : ℕ, IsIntegral (Algebra.adjoin A (Set.range z)) (r ^ n • c))
    (q e : ℕ) [ExpChar A q]
    (hrad : ∀ c : C, ∃ m : ℕ,
      ((MvPolynomial.aeval z g) ^ m * c) ^ q ^ e ∈ Algebra.adjoin A (insert w (Set.range z)))
    (hlc : algebraMap A κ (MvPolynomial.uniqueAlgEquiv A (Fin 1) g).leadingCoeff ≠ 0)
    (N : ℕ) (hN : Finite (C ⧸ Ideal.span {MvPolynomial.aeval z g} →ₐ[A] κ) ∧
      Nat.card (C ⧸ Ideal.span {MvPolynomial.aeval z g} →ₐ[A] κ) ≤ N) :
    |(Nat.card (C →ₐ[A] κ) : ℝ) - (Nat.card {v : Fin 2 → κ //
      MvPolynomial.eval v (planePoly (F.map (MvPolynomial.map (algebraMap A κ)))) = 0} : ℝ)| ≤
      ((N + (MvPolynomial.uniqueAlgEquiv A (Fin 1) g).natDegree * F.natDegree : ℕ) : ℝ) := by
  classical
  let h : C := MvPolynomial.aeval z g
  let Fκ := F.map (MvPolynomial.map (algebraMap A κ))
  let gκ : Polynomial κ := (MvPolynomial.uniqueAlgEquiv A (Fin 1) g).map (algebraMap A κ)
  have hlcκ : gκ.leadingCoeff ≠ 0 := by
    rw [Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hlc]
    exact hlc
  have hgκ : gκ ≠ 0 := Polynomial.leadingCoeff_ne_zero.mp hlcκ
  have hdegg : gκ.natDegree = (MvPolynomial.uniqueAlgEquiv A (Fin 1) g).natDegree :=
    Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hlc
  have hdegF : Fκ.natDegree = F.natDegree := hFm.natDegree_map _
  have : Finite (C →ₐ[A] κ) := finite_algHom_of_finiteType
  have := hN.1
  let Z := {v : Fin 2 → κ // MvPolynomial.eval v (planePoly Fκ) = 0}
  -- the points of `C` killing `h` are points of `C ⧸ (h)`
  have hbadC : Nat.card {ψ : C →ₐ[A] κ // ψ h = 0} ≤ N := by
    refine le_trans ?_ hN.2
    refine Nat.card_le_card_of_injective (fun ψ => Ideal.Quotient.liftₐ (Ideal.span {h}) ψ.1
      (fun c hc => by
        obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hc
        rw [map_mul, ψ.2, mul_zero])) ?_
    intro ψ₁ ψ₂ hψ
    apply Subtype.ext
    ext c
    have := congrArg (fun χ : C ⧸ Ideal.span {h} →ₐ[A] κ => χ (Ideal.Quotient.mk _ c)) hψ
    simpa [Ideal.Quotient.liftₐ_apply] using this
  -- the zeros over roots of `g`
  have hbadZ : Nat.card {v : Z // gκ.eval (v.1 1) = 0} ≤
      (MvPolynomial.uniqueAlgEquiv A (Fin 1) g).natDegree * F.natDegree := by
    rw [Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun v : Fin 2 → κ => MvPolynomial.eval v (planePoly Fκ) = 0)
      (fun v => gκ.eval (v 1) = 0)), ← hdegg, ← hdegF]
    exact card_zeros_planePoly_root_le Fκ (hFm.map _) gκ hgκ
  -- the good points correspond
  have hgood : Nat.card {ψ : C →ₐ[A] κ // ¬ψ h = 0} = Nat.card {v : Z // ¬gκ.eval (v.1 1) = 0} := by
    rw [card_algHom_good_eq z hz w F hFm hFroot hFirr g r hr hint q e hrad]
    apply Nat.card_congr
    refine (algHomEquivZeros Fκ).subtypeEquiv ?_
    intro χ
    rw [algHom_of_eq_eval_algHomEquivZeros, eval_map_eq_eval_uniqueAlgEquiv]
  have hC := card_eq_card_subtype_add_card_subtype_not (fun ψ : C →ₐ[A] κ => ψ h = 0)
  have hZ := card_eq_card_subtype_add_card_subtype_not (fun v : Z => gκ.eval (v.1 1) = 0)
  change |(Nat.card (C →ₐ[A] κ) : ℝ) - (Nat.card Z : ℝ)| ≤ _
  rw [hC, hZ, hgood]
  rw [abs_sub_le_iff]
  have h1 : ((Nat.card {ψ : C →ₐ[A] κ // ψ h = 0} : ℕ) : ℝ) ≤ N := by exact_mod_cast hbadC
  have h2 : ((Nat.card {v : Z // gκ.eval (v.1 1) = 0} : ℕ) : ℝ) ≤
      ((MvPolynomial.uniqueAlgEquiv A (Fin 1) g).natDegree * F.natDegree : ℕ) := by
    exact_mod_cast hbadZ
  push_cast at h1 h2 ⊢
  constructor <;> linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ (Nat.card {ψ : C →ₐ[A] κ // ψ h = 0} : ℝ)),
    (Nat.cast_nonneg _ : (0 : ℝ) ≤ (Nat.card {v : Z // gκ.eval (v.1 1) = 0} : ℝ))]

end Count

section Domain

/-- The plane-model comparison for a faithful finite type domain algebra, without a lower
bound on the size of the finite field. -/
theorem exists_bound_of_isDomain {A C K : Type u} [CommRing A] [IsDomain A]
    [CommRing C] [IsDomain C] [Algebra A C] [FaithfulSMul A C] [Algebra.FiniteType A C]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (hgen : (nilradical (AlgebraicClosure K ⊗[A] C)).IsPrime)
    (hdim : ringKrullDim (K ⊗[A] C) = 1) :
    ∃ a : A, a ≠ 0 ∧ ∃ B : ℕ, ∀ (κ : Type u) [Field κ] [Finite κ] [Algebra A κ],
      algebraMap A κ a ≠ 0 →
      ∃ p : MvPolynomial (Fin 2) κ,
        Irreducible (MvPolynomial.map (algebraMap κ (AlgebraicClosure κ)) p) ∧
        0 < p.degreeOf 0 ∧ p.degreeOf 0 ≤ B ∧ 0 < p.degreeOf 1 ∧ p.degreeOf 1 ≤ B ∧
        |(Nat.card (C →ₐ[A] κ) : ℝ) -
          (Nat.card {v : Fin 2 → κ // MvPolynomial.eval v p = 0} : ℝ)| ≤ B := by
  classical
  -- the generic fibre has no nontrivial separable constants
  let : FaithfulSMul A (AlgebraicClosure K) := FaithfulSMul.trans A K (AlgebraicClosure K)
  let : Algebra (FractionRing A) (FractionRing C) := FractionRing.liftAlgebra A (FractionRing C)
  let : IsScalarTower A (FractionRing A) (FractionRing C) :=
    FractionRing.isScalarTower_liftAlgebra A (FractionRing C)
  let : Algebra (FractionRing A) (AlgebraicClosure K) :=
    FractionRing.liftAlgebra A (AlgebraicClosure K)
  let : IsScalarTower A (FractionRing A) (AlgebraicClosure K) :=
    FractionRing.isScalarTower_liftAlgebra A (AlgebraicClosure K)
  have hsc := forall_isSeparable_mem_range_of_tensor_nilradical_isPrime
    (Langlands.Algebra.GenericIrreducibilityReduction.nilradical_tensor_fractionField_isPrime
      (F := FractionRing A) (L := FractionRing C) hgen)
  -- a hypersurface model, necessarily of dimension one
  obtain ⟨r, hr, d, z, w, F, g, hz, hFm, hFroot, hFirr, hg, ⟨q, e, hq, hrad⟩, hint⟩ :=
    exists_hypersurfaceModel_uniform_of_separablyClosed_range hsc
  have hrK : algebraMap A K r ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hr
  have hd : d = 1 := by
    have h := ringKrullDim_tensor_eq_of_integral_after_away (K := K) z hz r hrK hint
    rw [hdim] at h
    exact_mod_cast h.symm
  subst hd
  -- absolute irreducibility of the plane polynomial spreads
  let G : MvPolynomial (Fin 2) A := planePoly F
  have hGirr :
      Irreducible (MvPolynomial.map (algebraMap A (AlgebraicClosure (FractionRing A))) G) := by
    rw [map_planePoly, irreducible_planePoly_iff]
    exact hFirr
  obtain ⟨b, hb, hBN⟩ :=
    MvPolynomial.exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure.{u, 0, u}
      G hGirr
  -- the points over the zeros of `g(z)` are uniformly bounded
  let h : C := MvPolynomial.aeval z g
  have hnil : (nilradical (K ⊗[A] C)).IsPrime := nilradical_tensor_isPrime_of_algebraicClosure hgen
  have hle : Ring.KrullDimLE 1 (K ⊗[A] C) := Ring.krullDimLE_iff.mpr (by rw [hdim]; norm_cast)
  have hh : ¬IsNilpotent ((1 : K) ⊗ₜ[A] h) := by
    let t : C →ₐ[A] K ⊗[A] C := Algebra.TensorProduct.includeRight
    let ψ : MvPolynomial (Fin 1) K →ₐ[K] K ⊗[A] C := MvPolynomial.aeval (fun i => t (z i))
    have hψ : Function.Injective ψ :=
      tensor_aeval_injective_of_integral_after_away z hz r hrK hint
    have hψg : ψ (MvPolynomial.map (algebraMap A K) g) = (1 : K) ⊗ₜ[A] h := by
      change MvPolynomial.aeval (fun i => t (z i)) (MvPolynomial.map (algebraMap A K) g) =
        t (MvPolynomial.aeval z g)
      rw [MvPolynomial.aeval_map_algebraMap, ← MvPolynomial.comp_aeval_apply]
    rw [← hψg, IsNilpotent.map_iff hψ, isNilpotent_iff_eq_zero]
    intro h0
    apply hg
    apply MvPolynomial.map_injective _ (IsFractionRing.injective A K)
    rw [h0, map_zero]
  have hD : Ring.KrullDimLE 0 (K ⊗[A] (C ⧸ Ideal.span {h})) := fiber_quotient_krullDimLE_zero K hh
  obtain ⟨a₀, ha₀, N, hN⟩ := exists_card_algHom_le_of_krullDimLE_zero.{u, u, u, u}
    (A := A) (D := C ⧸ Ideal.span {h}) K
  have hĝ : (MvPolynomial.uniqueAlgEquiv A (Fin 1) g).leadingCoeff ≠ 0 := by
    rw [Ne, Polynomial.leadingCoeff_eq_zero]
    intro h0
    apply hg
    exact (MvPolynomial.uniqueAlgEquiv A (Fin 1)).injective (h0.trans (map_zero _).symm)
  refine ⟨r * b * a₀ * (MvPolynomial.uniqueAlgEquiv A (Fin 1) g).leadingCoeff,
    mul_ne_zero (mul_ne_zero (mul_ne_zero hr hb) ha₀) hĝ,
    F.natDegree + G.degreeOf 1 + N + (MvPolynomial.uniqueAlgEquiv A (Fin 1) g).natDegree * F.natDegree,
    ?_⟩
  intro κ _ _ _ ha
  simp only [map_mul] at ha
  have hrκ : algebraMap A κ r ≠ 0 :=
    left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul ha))
  have hbκ : algebraMap A κ b ≠ 0 :=
    right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul ha))
  have ha₀κ : algebraMap A κ a₀ ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul ha)
  have hlc : algebraMap A κ (MvPolynomial.uniqueAlgEquiv A (Fin 1) g).leadingCoeff ≠ 0 :=
    right_ne_zero_of_mul ha
  let Fκ := F.map (MvPolynomial.map (algebraMap A κ))
  have hmapG : MvPolynomial.map (algebraMap A κ) G = planePoly Fκ := map_planePoly _ F
  have hFκirr : Irreducible Fκ := by
    rw [← irreducible_planePoly_iff, ← hmapG]
    exact hBN κ (algebraMap A κ) hbκ
  have hirr :
      Irreducible (MvPolynomial.map (algebraMap κ (AlgebraicClosure κ)) (planePoly Fκ)) := by
    rw [← hmapG, MvPolynomial.map_map]
    apply hBN
    rw [RingHom.comp_apply]
    exact (map_ne_zero_iff _ (algebraMap κ (AlgebraicClosure κ)).injective).mpr hbκ
  have hcount := abs_card_sub_card_zeros_le z hz w F hFm hFroot hFκirr g r hrκ hint q e hrad hlc
    N (hN κ ha₀κ)
  have hdeg0 : (planePoly Fκ).degreeOf 0 = F.natDegree := by
    rw [degreeOf_zero_planePoly]
    exact hFm.natDegree_map _
  have hFpos : 0 < F.natDegree := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    have h1 : Fκ = 1 :=
      Polynomial.eq_one_of_monic_natDegree_zero (hFm.map _) ((hFm.natDegree_map _).trans h0)
    exact hFκirr.not_isUnit (h1 ▸ isUnit_one)
  have hdeg1 : (planePoly Fκ).degreeOf 1 ≤ G.degreeOf 1 := by
    rw [← hmapG]
    exact degreeOf_map_le _ G 1
  have hB : ((N + (MvPolynomial.uniqueAlgEquiv A (Fin 1) g).natDegree * F.natDegree : ℕ) : ℝ) ≤
      ((F.natDegree + G.degreeOf 1 + N +
        (MvPolynomial.uniqueAlgEquiv A (Fin 1) g).natDegree * F.natDegree : ℕ) : ℝ) := by
    exact_mod_cast (by omega)
  by_cases hd1 : (planePoly Fκ).degreeOf 1 = 0
  · -- the curve is a vertical line; use the diagonal, which has as many zeros
    refine ⟨diagonal, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [map_diagonal]
      exact irreducible_diagonal
    · rw [degreeOf_zero_diagonal]
      exact one_pos
    · rw [degreeOf_zero_diagonal]
      omega
    · rw [degreeOf_one_diagonal]
      exact one_pos
    · rw [degreeOf_one_diagonal]
      omega
    · rw [card_zeros_diagonal,
        ← card_zeros_planePoly_of_degreeOf_one_eq_zero Fκ (hFm.map _) hirr hd1]
      exact hcount.trans hB
  · refine ⟨planePoly Fκ, hirr, ?_, ?_, Nat.pos_of_ne_zero hd1, by omega, hcount.trans hB⟩
    · rw [hdeg0]
      exact hFpos
    · rw [hdeg0]
      omega

end Domain

section Main

/-- The uniform plane-model comparison for affine curves over a Noetherian domain. -/
theorem affineCurvePlaneComparison : AffineCurvePlaneComparison.{u} := by
  intro A R K _ _ _ _ _ _ _ _ _ hgen hdim
  -- pass to the quotient by the kernel to the geometric generic fibre's reduction
  let G := AlgebraicClosure K ⊗[A] R
  let j : R →ₐ[A] G := Algebra.TensorProduct.includeRight
  let I : Ideal R := (nilradical G).comap j.toRingHom
  let := hgen
  have : I.IsPrime := inferInstance
  let C := R ⧸ I
  have hinj : Function.Injective (algebraMap A C) := by
    apply (injective_iff_map_eq_zero _).mpr
    intro r hr
    by_contra hr0
    have hI : algebraMap A R r ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hr
    change j (algebraMap A R r) ∈ nilradical G at hI
    rw [j.commutes] at hI
    have hrf : algebraMap A K r ≠ 0 := by
      exact fun h => hr0 ((IsFractionRing.injective A K) (h.trans (map_zero _).symm))
    have hu : IsUnit (algebraMap A G r) := by
      rw [IsScalarTower.algebraMap_apply A K G]
      exact (isUnit_iff_ne_zero.mpr hrf).map (algebraMap K G)
    exact hgen.ne_top ((nilradical G).eq_top_of_isUnit_mem hI hu)
  let : FaithfulSMul A C := (faithfulSMul_iff_algebraMap_injective A C).mpr hinj
  have hnil : ∀ b ∈ I, IsNilpotent (1 ⊗ₜ[A] b : G) := fun b hb => mem_nilradical.mp hb
  have hgenC : (nilradical (AlgebraicClosure K ⊗[A] C)).IsPrime :=
    (nilradical_tensor_quotient_isPrime_iff I hnil).mp hgen
  have hdimC : ringKrullDim (K ⊗[A] C) = 1 := by
    let e := Algebra.TensorProduct.tensorQuotientEquiv (R := A) K R K I
    rw [ringKrullDim_eq_of_ringEquiv e.toRingEquiv, ringKrullDim_quotient_of_le_nilradical, hdim]
    apply Ideal.map_le_iff_le_comap.mpr
    intro b hb
    exact mem_nilradical.mpr (nilpotent_tensor_of_algebraicClosure b (hnil b hb))
  obtain ⟨a, ha, B, hB⟩ := exists_bound_of_isDomain (A := A) (C := C) (K := K) hgenC hdimC
  -- away from one more element, every point of `R` factors through `C`
  obtain ⟨s, hs, hsnil⟩ := exists_ne_zero_forall_tensor_nilpotent (R := A) R K
  refine ⟨a * s, mul_ne_zero ha hs, B, ?_⟩
  intro κ _ _ _ haκ _
  rw [map_mul] at haκ
  obtain ⟨p, hp1, hp2, hp3, hp4, hp5, hp6⟩ := hB κ (left_ne_zero_of_mul haκ)
  refine ⟨p, hp1, hp2, hp3, hp4, hp5, ?_⟩
  have hsκ : IsUnit (algebraMap A κ s) := isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul haκ)
  have hkill : ∀ φ : R →ₐ[A] κ, ∀ b ∈ I, φ b = 0 := by
    intro φ b hb
    have hn : IsNilpotent (1 ⊗ₜ[A] b : κ ⊗[A] R) :=
      hsnil κ hsκ b (nilpotent_tensor_of_algebraicClosure b (hnil b hb))
    have h1 : AlgHom.liftEquiv A κ R κ φ (1 ⊗ₜ[A] b) = φ b := one_smul κ (φ b)
    have h2 := hn.map (AlgHom.liftEquiv A κ R κ φ)
    rw [h1] at h2
    exact isNilpotent_iff_eq_zero.mp h2
  have hcard : Nat.card (R →ₐ[A] κ) = Nat.card (C →ₐ[A] κ) := by
    apply Nat.card_congr
    exact
      { toFun := fun φ => Ideal.Quotient.liftₐ I φ (hkill φ)
        invFun := fun ψ => ψ.comp (Ideal.Quotient.mkₐ A I)
        left_inv := fun φ => Ideal.Quotient.liftₐ_comp I φ (hkill φ)
        right_inv := fun ψ => Ideal.Quotient.algHom_ext A
          (Ideal.Quotient.liftₐ_comp I _ (hkill _)) }
  rw [hcard]
  exact hp6

end Main

end Langlands.AlgebraicGeometry.LangWeil.CurvePlane
