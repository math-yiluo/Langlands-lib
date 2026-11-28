import Langlands.Global.AdelicNormalizedPairingCorootPolynomial
import Langlands.Global.AdelicSquareIntegrableInducedSubmodule

/-! # Finite Weyl labels and the normalized weak pairing -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme GroupScheme.RealTorusSpace AdelicGroupPoints Automorphic.GroupSchemeFunctions

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

local notation "Idx" => StandardIndex F G fam.i fam.ν
local notation "Param[" J "]" => ComplexCharacterParameter F (fam.P J)
local notation "Fun" => (AdelicGroupPoints F G → ℂ)

attribute [local instance] isClosedImmersion_p

private def pairingIntegrandLeft (Q : Idx) (K : Subgroup (AdelicGroupPoints F G))
    (x : AdelicGroupPoints F (fam.P Q)) (g : Fun) :
    Fun →ₗ[ℂ] (K × NormOneRationalQuotient F (fam.M Q) → ℂ) where
  toFun f := fam.squareIntegrablePairingIntegrand K Q x f g
  map_add' f h := by
    funext z
    simp only [squareIntegrablePairingIntegrand, Pi.add_apply, add_mul]
  map_smul' a f := by
    funext z
    simp only [squareIntegrablePairingIntegrand, Pi.smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply]

local notation "Integ[" Q "," K "]" => fam.squareIntegrablePairingIntegrand K Q
local notation "Slice[" Q "," K "," hc "]" => fam.squareIntegrablePairingMeasure K hc Q
local notation "Pair[" Q "," K "," hc "]" => fam.normalizedPairing K hc Q

private theorem integrable_normalizedPairing_sum_right {Ix : Type*}
    (Q : Idx) (K : Subgroup (AdelicGroupPoints F G)) (hc : IsCompact (K : Set (AdelicGroupPoints F G)))
    (s : Finset Ix) (x : AdelicGroupPoints F (fam.P Q)) (f : Fun) (g : Ix → Fun)
    (h : ∀ i ∈ s, Integrable (Integ[Q,K] x f (g i)) Slice[Q,K,hc]) :
    Integrable (Integ[Q,K] x f (∑ i ∈ s, g i)) Slice[Q,K,hc] ∧
      Pair[Q,K,hc] x f (∑ i ∈ s, g i) = ∑ i ∈ s, Pair[Q,K,hc] x f (g i) := by
  have he : Integ[Q,K] x f (∑ i ∈ s, g i) = ∑ i ∈ s, Integ[Q,K] x f (g i) := by
    funext z
    simp only [squareIntegrablePairingIntegrand, Finset.sum_apply, map_sum, Finset.mul_sum]
  refine ⟨?_, ?_⟩
  · rw [he]
    convert integrable_finsetSum s h using 1
    funext z
    simp only [Finset.sum_apply]
  · simp only [normalizedPairing, he, Finset.sum_apply, integral_finsetSum s h, Finset.mul_sum]

private theorem integrable_normalizedPairing_sum_smul_left {Ix : Type*}
    (Q : Idx) (K : Subgroup (AdelicGroupPoints F G)) (hc : IsCompact (K : Set (AdelicGroupPoints F G)))
    (s : Finset Ix) (x : AdelicGroupPoints F (fam.P Q)) (a : Ix → ℂ) (f : Ix → Fun) (g : Fun)
    (h : ∀ i ∈ s, Integrable (Integ[Q,K] x (f i) g) Slice[Q,K,hc]) :
    Integrable (Integ[Q,K] x (∑ i ∈ s, a i • f i) g) Slice[Q,K,hc] ∧
      Pair[Q,K,hc] x (∑ i ∈ s, a i • f i) g = ∑ i ∈ s, a i * Pair[Q,K,hc] x (f i) g := by
  have he : Integ[Q,K] x (∑ i ∈ s, a i • f i) g = ∑ i ∈ s, a i • Integ[Q,K] x (f i) g := by
    change fam.pairingIntegrandLeft Q K x g (∑ i ∈ s, a i • f i) = _
    simp only [map_sum, map_smul]
    rfl
  have hI (i : Ix) (hi : i ∈ s) : Integrable (fun z => a i * Integ[Q,K] x (f i) g z) Slice[Q,K,hc] :=
    (h i hi).const_mul _
  refine ⟨?_, ?_⟩
  · rw [he]
    convert integrable_finsetSum s hI using 1
    funext z
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  · simp only [normalizedPairing, he, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, integral_finsetSum s hI,
      integral_const_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

private def regularizedOrthantLinear {σ : Type*} [Fintype σ] (z : σ → ℂ) :
    MvPolynomial σ ℂ →ₗ[ℂ] ℂ :=
  (Finsupp.linearCombination ℂ fun k : σ →₀ ℕ => ∏ α, orthantFactor (k α) (z α)).comp
    (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

private theorem sum_polynomial_fibres {Ix Ex σ : Type*} [Fintype Ix] [DecidableEq Ex]
    (e : Ix → Ex) (q : Ix → MvPolynomial σ ℂ) (B : Ex → MvPolynomial σ ℂ →ₗ[ℂ] ℂ) :
    (∑ b ∈ Finset.univ.image e, B b (∑ i ∈ Finset.univ.filter (fun i => e i = b), q i)) =
      ∑ i, B (e i) (q i) := by
  simp_rw [map_sum]
  calc
    _ = ∑ b ∈ Finset.univ.image e, ∑ i ∈ Finset.univ.filter (fun i => e i = b), B (e i) (q i) := by
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i hi => ?_
      rw [(Finset.mem_filter.mp hi).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem e hi) _

/-- Finite normalized twists with fixed inducing vectors and a fixed unitary test decomposition
produce the exact affine difference labels and a normalized pairing expansion at each unitary
parameter. An orthogonal remainder after subtracting the twists gives the square-integrable
part of the extended pairing. Before grouping equal labels, the normalized pairing and its
regularized cone integral both use the same fixed polynomial for each pair of terms. -/
def WeakPairingFiniteAssemblyStatement (I Q : Idx) {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsIwasawaCompact (fam.p Q) K) : Prop :=
  ∀ {N d r m : ℕ} (rho : MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (hcalc : AdelicDifferentialCommutator F G hsmooth)
    (A : Fin r → Param[I] →ₗ[ℂ] Param[Q]) (coef : Fin r → Param[I] → ℂ) (v : Fin r → Fun)
    (mu : Fin m → Param[Q]) (w : Fin m → Fun) (Ew : Param[I] → Fun),
    (∀ i, IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc (fam.p Q) (fam.iU Q) (fam.l Q) (v i)) →
    (∀ j, fam.HasExponent Q (mu j) (w j) ∧ parameterRealPart F (fam.P Q) (mu j) = 0) →
    (∀ i j x, x ∈ fam.positiveSplitComponent Q →
      Integrable (fam.squareIntegrablePairingIntegrand K Q x (v i) (w j))
        (fam.squareIntegrablePairingMeasure K hK.isCompact Q)) →
    ∃ (L : fam.AffineExponentLabels I Q)
      (p : Fin r → Fin m → MvPolynomial (fam.relativeSimpleRoots Q) ℂ),
      (∀ k : Fin L.size, ∃ (i : Fin r) (j : Fin m), L.linear k = A i ∧ L.offset k = -mu j) ∧
      (∀ (i : Fin r) (j : Fin m), ∃ k : Fin L.size, L.linear k = A i ∧ L.offset k = -mu j) ∧
      ∀ lam, (∀ i, parameterRealPart F (fam.P Q) (A i lam) = 0) →
        fam.IsSquareIntegrableOrthogonal K hK.isCompact rho hsmooth hcalc Q
          (Ew lam - ∑ i, coef i lam • hK.parameterTwist (v i) (A i lam)) →
        ∃ (s : Finset (Param[Q])) (φ : Param[Q] → Fun) (e : fam.UnitaryPairingExpansion Q),
          fam.IsSquareIntegrableTwistDecomposition rho hsmooth hcalc hK (Ew lam) s φ ∧
          fam.IsNormalizedPairingExpansion K hK.isCompact Q s
            (fun a => hK.parameterTwist (φ a) a) (∑ j, w j) e ∧
          e.IsLabelledBy L lam ∧
          (∀ c : fam.relativeSimpleRoots Q → ℝ,
            e.eval c = ∑ i, ∑ j, coef i lam *
              (Complex.exp (∑ α, (c α : ℂ) * fam.corootValue Q (A i lam - mu j) α) *
                (p i j).eval (fun α => (c α : ℂ)))) ∧
          ∀ T : V fam.T,
            e.regularizedConeIntegral T = ∑ i, ∑ j, coef i lam *
              (Complex.exp (∑ α, (fam.weightCoordinate Q T α : ℂ) * fam.corootValue Q (A i lam - mu j) α) *
                negativeOrthantRegularizedIntegral (fam.corootValue Q (A i lam - mu j))
                  (polynomialShift (fam.weightCoordinate Q T) (p i j)))

set_option maxHeartbeats 2800000 in
theorem weakPairingFiniteAssembly (I Q : Idx) {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsIwasawaCompact (fam.p Q) K) : fam.WeakPairingFiniteAssemblyStatement I Q hK := by
  classical
  intro N d r m rho hsmooth hcalc A coef v mu w Ew hv hw hI
  let ix := (Fintype.equivFin (Fin r × Fin m)).symm
  let L : fam.AffineExponentLabels I Q :=
    ⟨Fintype.card (Fin r × Fin m), fun k => A (ix k).1, fun k => -mu (ix k).2⟩
  choose p hp using fun i j => fam.normalizedPairingCorootPolynomial Q hK
    (hv i).2.1 (hw j).1 (hw j).2 (hI i j)
  refine ⟨L, p, ?_, ?_, fun lam hu hOrth => ?_⟩
  · intro k
    exact ⟨(ix k).1, (ix k).2, rfl, rfl⟩
  · intro i j
    refine ⟨ix.symm (i, j), ?_, ?_⟩ <;> simp only [L, Equiv.apply_symm_apply]
  let eta (i : Fin r) := A i lam
  let s := Finset.univ.image eta
  let fibre (a : Param[Q]) := Finset.univ.filter (fun i => eta i = a)
  let φ (a : Param[Q]) := ∑ i ∈ fibre a, coef i lam • v i
  let u (i : Fin r) := hK.parameterTwist (v i) (eta i)
  have ht (a : Param[Q]) : hK.parameterTwist (φ a) a = ∑ i ∈ fibre a, coef i lam • u i := by
    funext g
    simp only [IsIwasawaCompact.parameterTwist, φ, u, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.mp hi).2, mul_assoc]
  have hsum {B : Type} [AddCommMonoid B] (f : Fin r → B) :
      ∑ a ∈ s, ∑ i ∈ fibre a, f i = ∑ i, f i :=
    Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem eta hi) f
  have hSq : fam.IsSquareIntegrableTwistDecomposition rho hsmooth hcalc hK (Ew lam) s φ := by
    refine ⟨fun a _ => ?_, ?_⟩
    · apply (squareIntegrableInducedForms (fam.p Q) (fam.l Q) hK.isCompact rho hsmooth hcalc
        (fam.iU Q)).sum_mem
      exact fun i _ => (squareIntegrableInducedForms (fam.p Q) (fam.l Q) hK.isCompact rho hsmooth hcalc
        (fam.iU Q)).smul_mem _ (hv i)
    · simp_rw [ht]
      rw [hsum (fun i => coef i lam • u i)]
      exact hOrth
  let ex (k : Fin r × Fin m) := eta k.1 - mu k.2
  let t := Finset.univ.image ex
  let poly (b : Param[Q]) := ∑ k ∈ Finset.univ.filter (fun k => ex k = b), coef k.1 lam • p k.1 k.2
  have hunit (b : Param[Q]) (hb : b ∈ t) : parameterRealPart F (fam.P Q) b = 0 := by
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hb
    change parameterRealPart F (fam.P Q) (A k.1 lam - mu k.2) = 0
    rw [map_sub, hu k.1, (hw k.2).2, sub_zero]
  let e : fam.UnitaryPairingExpansion Q := ⟨t, poly, hunit⟩
  have hgroup (B : Param[Q] → MvPolynomial (fam.relativeSimpleRoots Q) ℂ →ₗ[ℂ] ℂ) :
      (∑ b ∈ e.exponents, B b (e.coefficient b)) =
        ∑ i : Fin r, ∑ j : Fin m, coef i lam * B (eta i - mu j) (p i j) := by
    rw [show (∑ b ∈ e.exponents, B b (e.coefficient b)) = ∑ k : Fin r × Fin m,
        B (ex k) (coef k.1 lam • p k.1 k.2) from sum_polynomial_fibres ex _ B, Fintype.sum_prod_type]
    simp only [ex, map_smul, smul_eq_mul]
  have heval (c : fam.relativeSimpleRoots Q → ℝ) :
      e.eval c = ∑ i : Fin r, ∑ j : Fin m, coef i lam *
        (Complex.exp (∑ α, (c α : ℂ) * fam.corootValue Q (eta i - mu j) α) *
          (p i j).eval (fun α => (c α : ℂ))) :=
    hgroup fun b => (Complex.exp (∑ α, (c α : ℂ) * fam.corootValue Q b α)) •
      (MvPolynomial.aeval (fun α => (c α : ℂ))).toLinearMap
  refine ⟨s, φ, e, hSq, ?_, ?_, heval, ?_⟩
  · intro x hx c hc
    let g : Fun := ∑ j, w j
    let B (f : Fun) (g : Fun) := fam.normalizedPairing K hK.isCompact Q x f g
    have hr (i : Fin r) : Integrable (fam.squareIntegrablePairingIntegrand K Q x (u i) g)
        (fam.squareIntegrablePairingMeasure K hK.isCompact Q) ∧ B (u i) g = ∑ j, B (u i) (w j) :=
      fam.integrable_normalizedPairing_sum_right Q K hK.isCompact Finset.univ x (u i) w
        (fun j _ => (hp i j (eta i) ⟨x, hx⟩).1)
    have hl (a : Param[Q]) :
        Integrable (fam.squareIntegrablePairingIntegrand K Q x (hK.parameterTwist (φ a) a) g)
          (fam.squareIntegrablePairingMeasure K hK.isCompact Q) ∧
        B (hK.parameterTwist (φ a) a) g = ∑ i ∈ fibre a, coef i lam * B (u i) g := by
      rw [ht]
      exact fam.integrable_normalizedPairing_sum_smul_left Q K hK.isCompact (fibre a) x
        (fun i => coef i lam) u g (fun i _ => (hr i).1)
    refine ⟨fun a _ => (hl a).1, ?_⟩
    change (∑ a ∈ s, B (hK.parameterTwist (φ a) a) g) = e.eval c
    simp_rw [(hl _).2]
    rw [hsum, heval]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(hr i).2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show B (u i) (w j) = _ from (hp i j (eta i) ⟨x, hx⟩).2 c hc]
  · intro b hb
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp (show b ∈ t from hb)
    refine ⟨ix.symm k, ?_⟩
    simp only [AffineExponentLabels.label, L, ex, eta, Equiv.apply_symm_apply, sub_eq_add_neg]
  · intro T
    let c := fam.weightCoordinate Q T
    let tr := (MvPolynomial.aeval (R := ℂ) (fun α =>
      MvPolynomial.X α + MvPolynomial.C (c α : ℂ))).toLinearMap
    exact hgroup fun b => (Complex.exp (∑ α, (c α : ℂ) * fam.corootValue Q b α)) •
      (regularizedOrthantLinear (fam.corootValue Q b)).comp tr

end Langlands.Global.StandardParabolicFamily
