import Langlands.Analysis.Meromorphic.ScalarIdentity
import Langlands.Global.AdelicEisensteinTwistComparison
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Continuation of the Eisenstein comparison across a change of compact -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry Set
open scoped CategoryTheory.MonObj Manifold

set_option autoImplicit false

namespace Langlands.Global

open AdelicGroupPoints Langlands.Analysis.Meromorphic Langlands.GroupScheme

private theorem meromorphicOn_of_differentiable {n : ℕ} {f : (Fin n → ℂ) → ℂ}
    {D : Set (Fin n → ℂ)} (ho : IsOpen D) (hd : Dense D) (hf : Differentiable ℂ f) :
    IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) f D := by
  have h1 : DifferentiableOn ℂ (fun _ : Fin n → ℂ => (1 : ℂ)) univ := differentiableOn_const 1
  refine ⟨ho, hd, isHolomorphicOn_iff_differentiableOn_scalar.mpr hf.differentiableOn,
    fun x => ⟨univ, isOpen_univ, isConnected_univ, mem_univ x, fun _ => 1, f,
      h1.mdifferentiableOn, ⟨x, mem_univ x, one_ne_zero⟩,
      isHolomorphicOn_iff_differentiableOn_scalar.mpr hf.differentiableOn, ?_⟩⟩
  exact fun _ _ => one_smul _ _

private theorem differentiable_exp_parameterPairing {F : Type u} [Field F] [NumberField F]
    {Q : GroupScheme (Spec (CommRingCat.of F))} {n : ℕ}
    (b : (Fin n → ℂ) →ₗ[ℂ] ComplexCharacterParameter F Q) (H : RealCharacterDual F Q) :
    Differentiable ℂ (fun x => Complex.exp (complexParameterPairing F Q (b x) H)) := by
  let ev : ComplexCharacterParameter F Q →ₗ[ℂ] ℂ :=
    { toFun := fun lam => complexParameterPairing F Q lam H
      map_add' := fun _ _ => by simp only [map_add, LinearMap.add_apply]
      map_smul' := fun _ _ => by simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply] }
  exact Complex.differentiable_exp.comp (ev.comp b).toContinuousLinearMap.differentiable

/-- Exponential height coefficients are entire in the linear chart. -/
theorem isMeromorphicOn_exp_parameterPairing {F : Type u} [Field F] [NumberField F]
    {Q : GroupScheme (Spec (CommRingCat.of F))} {n : ℕ}
    (b : (Fin n → ℂ) →ₗ[ℂ] ComplexCharacterParameter F Q) (H : RealCharacterDual F Q)
    {D : Set (Fin n → ℂ)} (ho : IsOpen D) (hd : Dense D) :
    IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ)
      (fun x => Complex.exp (complexParameterPairing F Q (b x) H)) D :=
  meromorphicOn_of_differentiable ho hd (differentiable_exp_parameterPairing b H)

private theorem meromorphicOn_sum_apply {n : ℕ} {D : Set (Fin n → ℂ)}
    {I : Type v} [Fintype I] {f : I → (Fin n → ℂ) → ℂ}
    (ho : IsOpen D) (hd : Dense D)
    (hf : ∀ i, IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) (f i) D) :
    IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) (fun x => ∑ i, f i x) D := by
  convert IsMeromorphicOn.sum Finset.univ ho hd (fun i _ => hf i) using 1
  funext x
  simp only [Finset.sum_apply]

private theorem meromorphicOn_mul_apply {n : ℕ} {D : Set (Fin n → ℂ)}
    {f g : (Fin n → ℂ) → ℂ}
    (hf : IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) f D)
    (hg : IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) g D) :
    IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) (fun x => f x * g x) D := by
  have h := hf.mul hg
  rw [inter_self] at h
  exact h

/-- Scalar continuation transports a finite compact comparison from a source
patch to the points where the target series converge. The source-series
agreement and the agreement of the target-twisted intertwining expansions
are supplied on the same nonempty open patch of the chart. -/
def EisensteinCompactContinuationComparisonStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (G Q : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [IsAffine Q.X.left]
    (q : Q ⟶ G) [IsClosedImmersion q.hom.hom.left]
    (K L : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact q K) (hL : IsIwasawaCompact q L)
    (n : ℕ) (b : (Fin n → ℂ) →ₗ[ℂ] ComplexCharacterParameter F Q)
    (D O : Set (Fin n → ℂ)) (I : Type v) [Fintype I] (k : ℕ) (m : I → ℕ)
    (EP : (Fin n → ℂ) → AdelicGroupPoints F G → ℂ)
    (EL : I → (Fin n → ℂ) → AdelicGroupPoints F G → ℂ)
    (a : I → (Fin n → ℂ) → ℂ)
    (cK : Fin k → (Fin n → ℂ) → ℂ) (cL : (i : I) → Fin (m i) → (Fin n → ℂ) → ℂ)
    (ψK : Fin k → AdelicGroupPoints F G → ℂ) (ψL : (i : I) → Fin (m i) → AdelicGroupPoints F G → ℂ),
    IsOpen O → O.Nonempty →
    (∀ g, IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) (fun x => EP x g) D) →
    (∀ i g, IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) (fun x => EL i x g) D) →
    (∀ i, IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) (a i) D) →
    (∀ j, IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) (cK j) D) →
    (∀ i j, IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) (cL i j) D) →
    (∀ x ∈ O, ∀ g, EP x g = ∑ i, a i x * EL i x g) →
    (∀ x ∈ O, ∀ g, ∑ j, cK j x * hK.parameterTwist (ψK j) (b x) g =
      ∑ i, a i x * ∑ j, cL i j x * hL.parameterTwist (ψL i j) (b x) g) →
    ∀ x ∈ D,
      (∀ i g, EL i x g = ∑ j, cL i j x * hL.eisensteinSeries (ψL i j) (b x) g) →
      (∀ j g, Summable (hK.eisensteinTerm (ψK j) (b x) g)) →
      (∀ i j g, Summable (hL.eisensteinTerm (ψL i j) (b x) g)) →
      ∀ g, EP x g = ∑ j, cK j x * hK.eisensteinSeries (ψK j) (b x) g

/-- The scalar identity theorem continues both agreements. Finite linearity
then passes the continued equality of target twists through the convergent
Eisenstein sums. -/
theorem eisensteinCompactContinuationComparison : EisensteinCompactContinuationComparisonStatement.{u, v} := by
  classical
  intro F _ _ G Q _ _ q _ K L hK hL n b D O I _ k m EP EL a cK cL ψK ψL
    hO hOne hEP hEL ha hcK hcL hsource htwists
  have hD := (hEP 1).1
  have hd := (hEP 1).2.1
  have hsource' (g : AdelicGroupPoints F G) :
      EqOn (fun x => EP x g) (fun x => ∑ i, a i x * EL i x g) D := by
    have hsum := meromorphicOn_sum_apply hD hd (f := fun i x => a i x * EL i x g)
      (fun i => meromorphicOn_mul_apply (ha i) (hEL i g))
    have hagree := (hEP g).eqOn_of_eqOn_open hsum hO hOne
      (fun x hx => hsource x hx.1 g)
    simpa only [inter_self] using hagree
  have htwist (g : AdelicGroupPoints F G) (ψ : AdelicGroupPoints F G → ℂ)
      {C : Subgroup (AdelicGroupPoints F G)} (hC : IsIwasawaCompact q C) :
      IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) (fun x => hC.parameterTwist ψ (b x) g) D := by
    apply meromorphicOn_of_differentiable hD hd
    exact (differentiable_const (c := ψ g)).mul (differentiable_exp_parameterPairing b (hC.height g))
  have htwists' (g : AdelicGroupPoints F G) :
      EqOn (fun x => ∑ j, cK j x * hK.parameterTwist (ψK j) (b x) g)
        (fun x => ∑ i, a i x * ∑ j, cL i j x * hL.parameterTwist (ψL i j) (b x) g) D := by
    have hsumK := meromorphicOn_sum_apply hD hd
      (f := fun j x => cK j x * hK.parameterTwist (ψK j) (b x) g)
      (fun j => meromorphicOn_mul_apply (hcK j) (htwist g (ψK j) hK))
    have hsumL (i : I) := meromorphicOn_sum_apply hD hd
      (f := fun j x => cL i j x * hL.parameterTwist (ψL i j) (b x) g)
      (fun j => meromorphicOn_mul_apply (hcL i j) (htwist g (ψL i j) hL))
    have hsum := meromorphicOn_sum_apply hD hd
      (f := fun i x => a i x * ∑ j, cL i j x * hL.parameterTwist (ψL i j) (b x) g)
      (fun i => meromorphicOn_mul_apply (ha i) (hsumL i))
    have hagree := hsumK.eqOn_of_eqOn_open hsum hO hOne (fun x hx => htwists x hx.1 g)
    simpa only [inter_self] using hagree
  intro x hx hcomp hsumK hsumL g
  let ψ : AdelicGroupPoints F G → ℂ := ∑ j, cK j x • ψK j
  have hcomb (z : AdelicGroupPoints F G) :
      hK.parameterTwist ψ (b x) z = ∑ j, cK j x * hK.parameterTwist (ψK j) (b x) z := by
    simp only [ψ, IsIwasawaCompact.parameterTwist, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_mul, mul_assoc]
  let J := Σ i : I, Fin (m i)
  let coeff (j : J) := a j.1 x * cL j.1 j.2 x
  have hcombL (z : AdelicGroupPoints F G) :
      hK.parameterTwist ψ (b x) z =
        ∑ j : J, coeff j * hL.parameterTwist (ψL j.1 j.2) (b x) z := by
    calc
      _ = ∑ j, cK j x * hK.parameterTwist (ψK j) (b x) z := hcomb z
      _ = ∑ i, a i x * ∑ j, cL i j x * hL.parameterTwist (ψL i j) (b x) z := htwists' z hx
      _ = _ := by simp only [J, coeff, Fintype.sum_sigma, Finset.mul_sum, mul_assoc]
  calc
    EP x g = ∑ i, a i x * EL i x g := hsource' g hx
    _ = ∑ i, a i x * ∑ j, cL i j x * hL.eisensteinSeries (ψL i j) (b x) g := by
      simp only [hcomp]
    _ = ∑ j : J, coeff j * hL.eisensteinSeries (ψL j.1 j.2) (b x) g := by
      simp only [J, coeff, Fintype.sum_sigma, Finset.mul_sum, mul_assoc]
    _ = hK.eisensteinSeries ψ (b x) g :=
      (hK.eisensteinSeries_eq_finset_sum_of_twist hL Finset.univ coeff ψ
        (fun j => ψL j.1 j.2) (b x) hcombL g (fun j _ => hsumL j.1 j.2 g)).symm
    _ = ∑ j, cK j x * hK.eisensteinSeries (ψK j) (b x) g :=
      hK.eisensteinSeries_eq_finset_sum_of_twist hK Finset.univ (fun j => cK j x) ψ ψK
        (b x) hcomb g (fun j _ => hsumK j g)

end Langlands.Global
