import Langlands.Global.AdelicIntertwiningDifferenceStatement
import Langlands.Global.AdelicIntertwiningContinuationReduction
import Langlands.Global.AdelicEisensteinContinuationStatement
import Langlands.Global.RepresentedAdelicSubgroupQuotient
import Langlands.Automorphic.GroupSchemeUniformGrowthConstantTerm
import Langlands.Analysis.Meromorphic.PointwiseValues
import Langlands.GroupScheme.Rational.ParabolicCharacterLattice

/-! # Bernstein–Lapid §8.5: the weak continuation of intertwining operators from that of
Eisenstein series

`intertwiningWeakMeromorphicContinuation_of_difference` proves the published
`IntertwiningWeakMeromorphicContinuationStatement` from two premises: the meromorphic
continuation of Eisenstein series (`EisensteinMeromorphicContinuationStatement`) and the
difference-operator input `IntertwiningConstantTermDifferenceStatement`. The argument is BL's:
polynomials in a translation operator recover `M(w, λ)φ` from the twisted constant term of the
continued Eisenstein series, up to an entire scalar denominator. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct Polynomial Set
open scoped CategoryTheory.MonObj TensorProduct Manifold

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

section Translation

variable {Γ : Type*} [Group Γ]

/-- Left translation `ψ ↦ (x ↦ ψ(t x))` as a linear endomorphism of the functions on a
group. -/
def leftTranslationEnd (t : Γ) : Module.End ℂ (Γ → ℂ) :=
  LinearMap.funLeft ℂ ℂ (fun x => t * x)

theorem leftTranslationEnd_pow_apply (t : Γ) (k : ℕ) (ψ : Γ → ℂ) (x : Γ) :
    (leftTranslationEnd t ^ k) ψ x = ψ (t ^ k * x) := by
  induction k generalizing ψ with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih]
    change ψ (t * (t ^ k * x)) = ψ (t ^ (k + 1) * x)
    rw [← mul_assoc, ← pow_succ']

/-- A polynomial in left translation, evaluated pointwise, with any degree bound. -/
theorem aeval_leftTranslationEnd_apply (t : Γ) (p : ℂ[X]) {B : ℕ} (hB : p.natDegree < B)
    (ψ : Γ → ℂ) (x : Γ) :
    aeval (leftTranslationEnd t) p ψ x = ∑ k ∈ Finset.range B, p.coeff k * ψ (t ^ k * x) := by
  rw [aeval_eq_sum_range' hB, LinearMap.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.smul_apply, Pi.smul_apply, leftTranslationEnd_pow_apply, smul_eq_mul]

end Translation

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}

/-- `IsTranslationPolynomialSolution t p ψ` says that the polynomial `p` in left translation by
`t` annihilates `ψ`. -/
theorem isTranslationPolynomialSolution_iff (t : AdelicGroupPoints F G) (p : ℂ[X])
    (ψ : AdelicGroupPoints F G → ℂ) :
    IsTranslationPolynomialSolution t p ψ ↔ aeval (leftTranslationEnd t) p ψ = 0 := by
  refine ⟨fun h => funext fun x => ?_, fun h x => ?_⟩
  · rw [aeval_leftTranslationEnd_apply t p (Nat.lt_succ_self _), h x, Pi.zero_apply]
  · rw [← aeval_leftTranslationEnd_apply t p (Nat.lt_succ_self _), h, Pi.zero_apply]

section Recovery

/-- The recovery polynomial `∏ j (f(r j) - f)`: it is congruent to the constant
`∏ j f(r j)` modulo `f` and divisible by `∏ j (X - r j)`. -/
theorem recoveryPolynomial_spec {k : ℕ} (f : ℂ[X]) (r : Fin k → ℂ) :
    (∃ h : ℂ[X], ∏ j, (C (f.eval (r j)) - f) = C (∏ j, f.eval (r j)) + h * f) ∧
      ∃ h : ℂ[X], ∏ j, (C (f.eval (r j)) - f) = h * ∏ j, (X - C (r j)) := by
  constructor
  · have hmk : Ideal.Quotient.mk (Ideal.span {f}) (∏ j, (C (f.eval (r j)) - f)) =
        Ideal.Quotient.mk (Ideal.span {f}) (C (∏ j, f.eval (r j))) := by
      have hf : Ideal.Quotient.mk (Ideal.span {f}) f = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self f)
      rw [map_prod, map_prod C, map_prod]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [map_sub, hf, sub_zero]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at hmk
    obtain ⟨h, hh⟩ := hmk
    exact ⟨h, by linear_combination hh⟩
  · have hdvd : ∏ j, (X - C (r j)) ∣ ∏ j, (C (f.eval (r j)) - f) :=
      Finset.prod_dvd_prod_of_dvd _ _ fun j _ => by
        have e : C (f.eval (r j)) - f = -(f - C (f.eval (r j))) := (neg_sub _ _).symm
        rw [e]
        exact (dvd_neg).2 X_sub_C_dvd_sub_C_eval
    obtain ⟨h, hh⟩ := hdvd
    exact ⟨h, by rw [hh, mul_comm]⟩

variable {Γ : Type*} [Group Γ]

/-- BL's recovery identity: if `f(T)ψ = 0` and `∏ j (T - r j)(Φ - ψ) = 0` for the left
translation `T` by `t`, then `∏ j (f(r j) - f)(T) Φ = (∏ j f(r j)) ψ`. -/
theorem aeval_recoveryPolynomial {k : ℕ} (t : Γ) (f : ℂ[X]) (r : Fin k → ℂ)
    {ψ Φ : Γ → ℂ} (hψ : aeval (leftTranslationEnd t) f ψ = 0)
    (hΦ : aeval (leftTranslationEnd t) (∏ j, (X - C (r j))) (Φ - ψ) = 0) :
    aeval (leftTranslationEnd t) (∏ j, (C (f.eval (r j)) - f)) Φ =
      (∏ j, f.eval (r j)) • ψ := by
  obtain ⟨⟨h₁, hh₁⟩, ⟨h₂, hh₂⟩⟩ := recoveryPolynomial_spec f r
  have e₁ : aeval (leftTranslationEnd t) (∏ j, (C (f.eval (r j)) - f)) ψ =
      (∏ j, f.eval (r j)) • ψ := by
    rw [hh₁, map_add, aeval_C, map_mul, LinearMap.add_apply, Module.algebraMap_end_apply,
      Module.End.mul_apply, hψ, map_zero, add_zero]
  have e₂ : aeval (leftTranslationEnd t) (∏ j, (C (f.eval (r j)) - f)) (Φ - ψ) = 0 := by
    rw [hh₂, map_mul, Module.End.mul_apply, hΦ, map_zero]
  have hsplit : Φ = ψ + (Φ - ψ) := by abel
  rw [hsplit, map_add, e₁, e₂, add_zero]

end Recovery

section Coefficients

variable (m : ℕ)

/-- The entire functions on `ℂᵐ`, as a subalgebra of all functions. -/
def entireSubalgebra : Subalgebra ℂ ((Fin m → ℂ) → ℂ) where
  carrier := {g | Differentiable ℂ g}
  mul_mem' := Differentiable.mul
  add_mem' := Differentiable.add
  algebraMap_mem' z := differentiable_const z

variable {m}

/-- The coefficients of `∏ j (f(r j s) - f)` are entire functions of `s` when every `r j` is
entire. -/
theorem differentiable_coeff_recoveryPolynomial {k : ℕ} (f : ℂ[X])
    {r : Fin k → (Fin m → ℂ) → ℂ} (hr : ∀ j, Differentiable ℂ (r j)) (n : ℕ) :
    Differentiable ℂ fun s => (∏ j, (C (f.eval (r j s)) - f)).coeff n := by
  let A := entireSubalgebra m
  let rA : Fin k → A := fun j => ⟨fun s => f.eval (r j s), f.differentiable.comp (hr j)⟩
  let WA : A[X] := ∏ j, (C (rA j) - f.map (algebraMap ℂ A))
  have hmap : ∀ s, WA.map ((Pi.evalAlgHom ℂ (fun _ => ℂ) s).comp A.val).toRingHom =
      ∏ j, (C (f.eval (r j s)) - f) := by
    intro s
    rw [Polynomial.map_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Polynomial.map_sub, Polynomial.map_C, Polynomial.map_map, AlgHom.toRingHom_eq_coe,
      AlgHom.comp_algebraMap, Algebra.algebraMap_self, Polynomial.map_id]
    rfl
  have hcoeff : (fun s => (∏ j, (C (f.eval (r j s)) - f)).coeff n) =
      ((WA.coeff n : A) : (Fin m → ℂ) → ℂ) := by
    funext s
    rw [← hmap s, Polynomial.coeff_map]
    rfl
  rw [hcoeff]
  exact (WA.coeff n).property

end Coefficients

section ZeroRank

variable {P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine P.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {K : Subgroup (AdelicGroupPoints F G)}

/-- If `G(𝔸)` is trivial, every height power is `1`. -/
theorem IsIwasawaCompact.heightPower_eq_one_of_subsingleton
    [Subsingleton (AdelicGroupPoints F G)] (hK : IsIwasawaCompact p K)
    (lam : ComplexCharacterParameter F P) (g : AdelicGroupPoints F G) :
    hK.heightPower lam g = 1 := by
  rw [IsIwasawaCompact.heightPower, Subsingleton.elim g 1, hK.height_of_mem K.one_mem, map_zero,
    Complex.exp_zero]

end ZeroRank

/-- A closed subgroup of `GL_0` has trivial adelic points (universe-polymorphic form of
`subsingleton_adelicGroupPoints_of_rank_zero`). -/
theorem subsingleton_adelicGroupPoints_of_rank_zero' [IsAffine G.X.left]
    (rho : MatrixRepresentation G (Fin 0)) (hrho : IsClosedSubgroup rho) :
    Subsingleton (AdelicGroupPoints F G) :=
  ⟨fun _ _ => (RepresentationGrowth.isClosedEmbedding_adelicMatrix F G rho hrho).injective
    (Units.ext (Matrix.ext fun i => Fin.elim0 i))⟩

/-- A constant function on a finite-dimensional complex vector space is meromorphic in
coordinates with domain of holomorphy the whole space. -/
theorem isMeromorphicInCoordinatesOn_const {X : Type*} [AddCommGroup X] [Module ℂ X]
    [FiniteDimensional ℂ X] {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    (v : V) : IsMeromorphicInCoordinatesOn (fun _ : X => v) univ := by
  refine ⟨inferInstance, fun n e => ?_⟩
  have hc : (fun _ : X => v) ∘ e = fun _ => v := rfl
  rw [preimage_univ, hc]
  exact ⟨isOpen_univ, dense_univ, fun ν => mdifferentiableOn_const, fun s₀ =>
    ⟨univ, isOpen_univ, isConnected_univ, mem_univ _, fun _ => 1, fun _ => v,
      mdifferentiableOn_const, ⟨s₀, mem_univ _, one_ne_zero⟩, fun ν => mdifferentiableOn_const,
      fun s _ => one_smul ℂ v⟩⟩

/-- The conditional statement proved here: the meromorphic continuation of Eisenstein series and
the difference-operator input of BL §8.5 imply the weak meromorphic continuation of intertwining
operators. -/
def IntertwiningWeakContinuationReductionStatement : Prop :=
  EisensteinMeromorphicContinuationStatement.{u} →
    IntertwiningConstantTermDifferenceStatement.{u} →
      IntertwiningWeakMeromorphicContinuationStatement.{u}

/-- Bernstein–Lapid §8.5: `IntertwiningWeakMeromorphicContinuationStatement` from the
meromorphic continuation of Eisenstein series and the difference-operator input. -/
theorem intertwiningWeakMeromorphicContinuation_of_difference :
    IntertwiningWeakContinuationReductionStatement.{u} := by
  intro hE hD F _ _ G P M U Q M' V A _ _ _ _ _ _ p _ iU l a r _ _ _ hA hT q _ iV l' _ π' w c
    hG hU hQ hV hl' hiso hπ hW K hK hK' N d rho hsmooth hcalc φ hmax hrho hφ
  classical
  have hfin : FiniteDimensional ℂ (ComplexCharacterParameter F P) := by
    have := (r.rationalCharacters_free_finite hG).2
    exact Module.Finite.base_change ℤ ℂ _
  set op : ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ :=
    fun lam => hK.intertwiningOperator hK' iU l iV c π' w φ lam with hop
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · -- `N = 0`: `G(𝔸)` is trivial and `M(w, λ)φ` does not depend on `λ`.
    subst hN0
    have := subsingleton_adelicGroupPoints_of_rank_zero' rho hrho
    have hconst : op = fun _ => op 0 := by
      funext lam g
      simp only [hop, IsIwasawaCompact.intertwiningOperator,
        IsIwasawaCompact.intertwiningIntegral, IsIwasawaCompact.intertwiningIntegrand,
        IsIwasawaCompact.parameterTwist, IsIwasawaCompact.heightPower_eq_one_of_subsingleton]
    refine ⟨op, univ, ?_, 0, fun lam _ => rfl⟩
    rw [hconst]
    exact isMeromorphicInCoordinatesOn_const _
  · -- `N > 0`
    obtain ⟨E', ⟨R₁, hR₁⟩, hloc⟩ :=
      hE F G P M U A p iU l a r hA hT hG hU K hK rho hN hrho hsmooth hcalc φ hmax hφ
    obtain ⟨t, f, k, root, hroot, ⟨lam₀, hlam₀⟩, R₂, hR₂⟩ :=
      hD F G P M U Q M' V A p iU l a r hA hT q iV l' π' w c hG hU hQ hV hl' hiso hπ hW K hK
        hK' rho hsmooth hcalc φ hmax hrho hφ
    have : CompactSpace (AdelicSubgroupPoints.RationalQuotient F G
        (SubgroupFunctor.range (iV ≫ q))) :=
      AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent F (iV ≫ q)
        hV.1.smooth hV.1.connectedSpace hV.1.isUnipotent
    set m := Module.finrank ℂ (ComplexCharacterParameter F P)
    set e₀ : (Fin m → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P :=
      (Module.finBasis ℂ (ComplexCharacterParameter F P)).equivFun.symm with he₀
    -- the twisted constant term of the continuation, the recovery polynomial and denominator
    set hp : (Fin m → ℂ) → AdelicGroupPoints F G → ℂ :=
      fun s y => hK'.heightPower (-weylParameter l c π' (e₀ s)) y with hhp
    set Φ : (Fin m → ℂ) → AdelicGroupPoints F G → ℂ :=
      fun s y => hp s y * subgroupConstantTerm F (iV ≫ q) (E' (e₀ s)) y with hΦ
    set Wp : (Fin m → ℂ) → ℂ[X] :=
      fun s => ∏ j, (C (f.eval (root j (e₀ s))) - f) with hWp
    set den : (Fin m → ℂ) → ℂ := fun s => ∏ j, f.eval (root j (e₀ s)) with hden
    set B : ℕ := k * f.natDegree + 1 with hB
    have hWdeg : ∀ s, (Wp s).natDegree < B := by
      intro s
      refine lt_of_le_of_lt ?_ (Nat.lt_succ_self _)
      refine (natDegree_prod_le _ _).trans ?_
      refine (Finset.sum_le_sum fun j _ => (natDegree_sub_le _ _).trans
        (by rw [natDegree_C, Nat.zero_max])).trans ?_
      simp
    set Ψ : AdelicGroupPoints F G → (Fin m → ℂ) → ℂ :=
      fun x s => (den s)⁻¹ * aeval (leftTranslationEnd t) (Wp s) (Φ s) x with hΨ
    -- analytic properties of the ingredients
    have hrootd : ∀ j, Differentiable ℂ fun s => root j (e₀ s) := fun j => hroot j m e₀
    have hdend : Differentiable ℂ den := by
      have h := (entireSubalgebra m).prod_mem (t := Finset.univ)
        (f := fun j => fun s => f.eval (root j (e₀ s)))
        fun j _ => f.differentiable.comp (hrootd j)
      have he : (∏ j ∈ Finset.univ, fun s => f.eval (root j (e₀ s))) = den := by
        funext s
        simp only [hden, Finset.prod_apply]
      rw [he] at h
      exact h
    have hden₀ : den (e₀.symm lam₀) ≠ 0 := by
      simp only [hden, LinearEquiv.apply_symm_apply]
      exact Finset.prod_ne_zero_iff.2 fun j _ => hlam₀ j
    have hhpd : ∀ y, Differentiable ℂ fun s => hp s y := by
      intro y
      let ℓ : (Fin m → ℂ) →ₗ[ℂ] ℂ :=
        { toFun := fun s => complexParameterPairing F Q (-weylParameter l c π' (e₀ s))
            (hK'.height y)
          map_add' := fun s s' => by
            simp only [map_add, neg_add, LinearMap.add_apply]
          map_smul' := fun z s => by
            simp only [map_smul, RingHom.id_apply]
            rw [← smul_neg, map_smul, LinearMap.smul_apply, smul_eq_mul] }
      have h : (fun s => hp s y) = fun s => Complex.exp (LinearMap.toContinuousLinearMap ℓ s) :=
        rfl
      rw [h]
      exact (LinearMap.toContinuousLinearMap ℓ).differentiable.cexp
    have hcoefd : ∀ n, Differentiable ℂ fun s => (Wp s).coeff n :=
      differentiable_coeff_recoveryPolynomial f hrootd
    -- local meromorphic data of the constant terms of the continuation
    have hCT : ∀ s₀, HasLocalMeromorphicData
        (fun y s => subgroupConstantTerm F (iV ≫ q) (E' (e₀ s)) y) s₀ := by
      intro s₀
      obtain ⟨W, hs₀, R, L, -, floc, D, hf, hfD⟩ := hloc m e₀ s₀
      refine hasLocalMeromorphicData_of_isMeromorphicOn hf
        (fun y => UniformGrowthFrechetSpace.constantTermEvaluation F G rho hsmooth hcalc hN hrho
          R L (iV ≫ q) y) (fun s hs y => ?_) hs₀
      rw [UniformGrowthFrechetSpace.constantTermEvaluation_apply, (hfD s hs).1]
    have hΨloc : ∀ s₀, HasLocalMeromorphicData Ψ s₀ := by
      intro s₀
      refine (hCT s₀).combination hdend hden₀ B
        (fun x n s => (Wp s).coeff n * hp s (t ^ n * x))
        (fun x n => (hcoefd n).mul (hhpd _)) (fun x n => t ^ n * x) fun x s => ?_
      rw [hΨ]
      dsimp only
      rw [aeval_leftTranslationEnd_apply t (Wp s) (hWdeg s)]
      congr 1
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [hΦ]
      ring
    obtain ⟨U₀, hU₀⟩ := exists_isMeromorphicOn_pi_of_local hΨloc
    -- the continuation: `M(w, λ)φ` on the regular region, the recovered function elsewhere
    set R₀ := max R₁ R₂ with hR₀
    set E : ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ := fun lam =>
      if r.IsRegularParameter hA hT R₀ lam then op lam else fun x => Ψ x (e₀.symm lam) with hEdef
    set Z : Set (Fin m → ℂ) := {s | den s ≠ 0} with hZ
    have hZo : IsOpen Z := isOpen_ne_fun hdend.continuous continuous_const
    have hZd : Dense Z := by
      refine dense_iff_inter_open.2 fun O hO hOne => ?_
      obtain ⟨s, hsO, hs⟩ := exists_ne_zero_of_differentiable hdend hden₀ hO hOne
      exact ⟨s, hsO, hs⟩
    refine ⟨E, e₀ '' (U₀ ∩ Z), ?_, R₀, fun lam hlam => by simp only [hEdef, hop, hlam, ↓reduceIte]⟩
    apply isMeromorphicInCoordinatesOn_of_coordinates e₀
    rw [e₀.injective.preimage_image]
    refine hU₀.congr_mono (hU₀.1.inter hZo) (hU₀.2.1.inter_of_isOpen_left hZd hU₀.1)
      inter_subset_left fun s hs => ?_
    funext x
    simp only [Function.comp_apply, hEdef]
    split_ifs with hreg
    · -- on the regular region the recovered function is `M(w, λ)φ`
      have hreg₁ : r.IsRegularParameter hA hT R₁ (e₀ s) :=
        fun α hα => lt_of_le_of_lt (le_max_left _ _) (hreg α hα)
      have hreg₂ : r.IsRegularParameter hA hT R₂ (e₀ s) :=
        fun α hα => lt_of_le_of_lt (le_max_right _ _) (hreg α hα)
      obtain ⟨hf₀, hg₀⟩ := hR₂ (e₀ s) hreg₂
      rw [isTranslationPolynomialSolution_iff] at hf₀ hg₀
      have hΦs : Φ s = fun y => hK'.heightPower (-weylParameter l c π' (e₀ s)) y *
          subgroupConstantTerm F (iV ≫ q) (hK.eisensteinSeries φ (e₀ s)) y := by
        simp only [hΦ, hhp, hR₁ (e₀ s) hreg₁]
      have hrec := aeval_recoveryPolynomial t f (fun j => root j (e₀ s)) (ψ := op (e₀ s))
        (Φ := Φ s) hf₀ (by rw [hΦs]; exact hg₀)
      have hds : den s ≠ 0 := hs.2
      simp only [hΨ, hWp, hrec, Pi.smul_apply, smul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hds, one_mul]
    · simp only [LinearEquiv.symm_apply_apply]

end Langlands.Global
