import Langlands.Representation.Plancherel.ParabolicRepresentedComparison
import Langlands.Global.AdelicSelfWeylParameters
import Langlands.Global.AdelicLocalWavePacketStatement
import Langlands.Global.AdelicIntertwiningSquareIntegrableExpansionStatement
import Langlands.Global.AdelicIntertwiningImaginaryUnitarityStatement
import Langlands.Global.AdelicInducedInnerProductGramStatement
import Langlands.Global.AdelicImaginaryIntertwiningExistence
import Langlands.Global.AdelicWavePacketIsometryReduction
import Langlands.Global.AdelicInducedInnerProductIntegrableProof
import Langlands.Global.BoundedWavePacketReduction
import Langlands.GroupScheme.Rational.ParabolicRootRadicals
import Langlands.GroupScheme.Rational.LeviMultiplication

/-! # The bound (19) of Lapid's Lemma 10 for smooth wave packets, from four premises

Lapid 2011, Lemma 10, bound (19) (p.329) for `φ ∈ W_P`: `LocalWavePacketNormBoundStatement`
follows from Lapid's formula (4) for smooth wave packets (`LocalWavePacketInnerProductStatement`),
finite square-integrable expansions of the intertwining operators
(`IntertwiningSquareIntegrableExpansionStatement`), their unitarity on the imaginary axis
(`IntertwiningImaginaryUnitarityStatement`) and the positivity of `(·,·)_P` in Gram form
(`InducedInnerProductGramStatement`). Finiteness of `Ω(P, P)` and invariance of the spectral
measure under `Ω(P, P)` are proved in `Langlands.Global.AdelicSelfWeylParameters`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct Set
open scoped CategoryTheory.MonObj TensorProduct ComplexOrder ComplexConjugate

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

namespace LocalWavePacketNormBound

/-! ### Algebra of Gram forms -/

/-- If a sesquilinear Gram form on a family indexed by `Ia ⊕ Ib` is positive, then twice the real
part of the mixed term is at most the sum of the two diagonal terms. -/
theorem two_mul_re_cross_le {Ia Ib : Type*} [Fintype Ia] [Fintype Ib] (Q : Ia ⊕ Ib → Ia ⊕ Ib → ℂ)
    (hpos : ∀ z : Ia ⊕ Ib → ℂ, 0 ≤ ∑ a, ∑ b, z a * conj (z b) * Q a b) (u : Ia → ℂ)
    (v : Ib → ℂ) :
    2 * (∑ a, ∑ b, u a * conj (v b) * Q (.inl a) (.inr b)).re ≤
      (∑ a, ∑ a', u a * conj (u a') * Q (.inl a) (.inl a')).re +
        (∑ b, ∑ b', v b * conj (v b') * Q (.inr b) (.inr b')).re := by
  set A := ∑ a, ∑ a', u a * conj (u a') * Q (.inl a) (.inl a') with hA
  set B := ∑ a, ∑ b, u a * conj (v b) * Q (.inl a) (.inr b) with hB
  set B' := ∑ b, ∑ a, v b * conj (u a) * Q (.inr b) (.inl a) with hB'
  set C := ∑ b, ∑ b', v b * conj (v b') * Q (.inr b) (.inr b') with hC
  have hexp : ∀ s t : ℂ, ∑ a, ∑ b, Sum.elim (fun i => s * u i) (fun j => t * v j) a *
      conj (Sum.elim (fun i => s * u i) (fun j => t * v j) b) * Q a b =
      s * conj s * A + s * conj t * B + (t * conj s * B' + t * conj t * C) := by
    intro s t
    have h1 : ∑ a, ∑ a', s * u a * conj (s * u a') * Q (.inl a) (.inl a') = s * conj s * A := by
      rw [hA, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a' _ => ?_
      rw [map_mul]
      ring
    have h2 : ∑ a, ∑ b, s * u a * conj (t * v b) * Q (.inl a) (.inr b) = s * conj t * B := by
      rw [hB, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [map_mul]
      ring
    have h3 : ∑ b, ∑ a, t * v b * conj (s * u a) * Q (.inr b) (.inl a) = t * conj s * B' := by
      rw [hB', Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_mul]
      ring
    have h4 : ∑ b, ∑ b', t * v b * conj (t * v b') * Q (.inr b) (.inr b') = t * conj t * C := by
      rw [hC, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b' _ => ?_
      rw [map_mul]
      ring
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.sum_add_distrib]
    rw [h1, h2, h3, h4]
    ring
  have hA0 := hpos (Sum.elim (fun i => (1 : ℂ) * u i) (fun j => (0 : ℂ) * v j))
  have hC0 := hpos (Sum.elim (fun i => (0 : ℂ) * u i) (fun j => (1 : ℂ) * v j))
  have hI := hpos (Sum.elim (fun i => (1 : ℂ) * u i) (fun j => Complex.I * v j))
  have hm := hpos (Sum.elim (fun i => (1 : ℂ) * u i) (fun j => (-1 : ℂ) * v j))
  rw [hexp] at hA0 hC0 hI hm
  rw [Complex.nonneg_iff] at hA0 hC0 hI hm
  simp only [map_one, map_zero, map_neg, Complex.conj_I, one_mul, mul_one, zero_mul, mul_zero,
    zero_add, add_zero, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im, Complex.I_re,
    Complex.I_im] at hA0 hC0 hI hm
  linarith [hA0.2, hC0.2, hI.2, hm.1]

/-- Positivity of a Gram form on finite families indexed by `Fin m` gives positivity on finite
families indexed by any finite type. -/
theorem gram_nonneg_of_fin {X ν : Type*} [Fintype ν] (Pred : X → Prop) (IP : X → X → ℂ)
    (h : ∀ (m : ℕ) (f : Fin m → X), (∀ i, Pred (f i)) → ∀ z : Fin m → ℂ,
      0 ≤ ∑ i, ∑ i', z i * conj (z i') * IP (f i) (f i'))
    (fam : ν → X) (hfam : ∀ a, Pred (fam a)) (z : ν → ℂ) :
    0 ≤ ∑ a, ∑ b, z a * conj (z b) * IP (fam a) (fam b) := by
  classical
  let eq := (Fintype.equivFin ν).symm
  have h0 := h _ (fam ∘ eq) (fun i => hfam _) (z ∘ eq)
  calc (0 : ℂ) ≤ _ := h0
    _ = ∑ a, ∑ b, z a * conj (z b) * IP (fam a) (fam b) := by
      rw [← Equiv.sum_comp eq (fun a => ∑ b, z a * conj (z b) * IP (fam a) (fam b))]
      exact Finset.sum_congr rfl fun i _ =>
        Equiv.sum_comp eq (fun b => z (eq i) * conj (z b) * IP (fam (eq i)) (fam b))

/-- Padding a finite sum by zeros. -/
theorem sum_fin_dite_eq {m k : ℕ} (hk : k ≤ m) (g : Fin k → ℂ) :
    ∑ i : Fin m, (if h : (i : ℕ) < k then g ⟨i, h⟩ else 0) = ∑ i : Fin k, g i := by
  classical
  let G : ℕ → ℂ := fun i => if h : i < k then g ⟨i, h⟩ else 0
  have h1 : ∑ i : Fin m, (if h : (i : ℕ) < k then g ⟨i, h⟩ else 0) = ∑ i ∈ Finset.range m, G i :=
    Fin.sum_univ_eq_sum_range G m
  have h2 : ∑ i : Fin k, g i = ∑ i ∈ Finset.range k, G i := by
    rw [← Fin.sum_univ_eq_sum_range G k]
    exact Finset.sum_congr rfl fun i _ => by simp [G, i.2]
  rw [h1, h2]
  refine (Finset.sum_subset (Finset.range_subset_range.mpr hk) fun i _ hi => ?_).symm
  simp only [Finset.mem_range, not_lt] at hi
  simp [G, not_lt.mpr hi]

/-- Meromorphy in coordinates survives a finite intersection with domains that preserve it. -/
theorem isMeromorphicInCoordinatesOn_inter_biInter {X Ia : Type*} [AddCommGroup X] [Module ℂ X]
    (s : Finset Ia) (Dq : Ia → Set X)
    (hq : ∀ q (f : X → ℂ) (U : Set X), IsMeromorphicInCoordinatesOn f U →
      IsMeromorphicInCoordinatesOn f (U ∩ Dq q))
    {f : X → ℂ} {U : Set X} (hf : IsMeromorphicInCoordinatesOn f U) :
    IsMeromorphicInCoordinatesOn f (U ∩ ⋂ q ∈ s, Dq q) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hf
  | insert a s _ ih =>
    have h := hq a f _ ih
    have he : U ∩ ⋂ q ∈ insert a s, Dq q = (U ∩ ⋂ q ∈ s, Dq q) ∩ Dq a := by
      rw [Finset.set_biInter_insert]
      ext x
      simp only [mem_inter_iff]
      tauto
    rw [he]
    exact h

/-- A product `f · g` is continuous when `f` is continuous and vanishes off a closed set `S`, and
`g` is continuous on an open neighbourhood of `S`. -/
theorem continuous_mul_of_eq_zero {X : Type*} [TopologicalSpace X] {f g : X → ℂ} {S V : Set X}
    (hS : IsClosed S) (hV : IsOpen V) (hSV : S ⊆ V) (hf : Continuous f)
    (hf0 : ∀ x ∉ S, f x = 0) (hg : ContinuousOn g V) : Continuous (fun x => f x * g x) := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  by_cases hx : x ∈ V
  · exact hf.continuousAt.mul (hg.continuousAt (hV.mem_nhds hx))
  · have hxS : x ∉ S := fun h => hx (hSV h)
    have hev : (fun x => f x * g x) =ᶠ[nhds x] fun _ => 0 := by
      filter_upwards [hS.isOpen_compl.mem_nhds hxS] with y hy
      rw [hf0 y hy, zero_mul]
    exact continuousAt_const.congr hev.symm

theorem spectralMeasure_const_ne_top (n : ℕ) :
    (ENNReal.ofReal (2 * Real.pi))⁻¹ ^ n ≠ ⊤ :=
  ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (by simp [Real.pi_pos]))

/-- A continuous function vanishing off a compact set is integrable for Lebesgue measure and for
`spectralMeasure`. -/
theorem integrable_of_continuous_of_eq_zero {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    {f : (Fin n → ℝ) → E} {S : Set (Fin n → ℝ)} (hf : Continuous f) (hS : IsCompact S)
    (h0 : ∀ x ∉ S, f x = 0) : Integrable f volume ∧ Integrable f (spectralMeasure n) := by
  have hv : Integrable f volume := hf.integrable_of_hasCompactSupport (HasCompactSupport.intro hS h0)
  exact ⟨hv, hv.smul_measure (spectralMeasure_const_ne_top n)⟩

/-! ### Transport of a signed weight along a Weyl coordinate change -/

/-- Transport of coordinates along a Lebesgue-measure-preserving coordinate change, for a signed
weight: if `x ↦ e'⁻¹(L(e x))` preserves Lebesgue measure, then `e'' = L ∘ e` are coordinates on
`X^*(P') ⊗ ℝ`, and the weight `β'` in the coordinates `e'` is a weight `β''` in the coordinates
`e''`, continuous, compactly supported, of integral `1`, with the same values at every
`H ∈ Hom(X^*(P'), ℝ)`. -/
theorem exists_transported_weight {F : Type} [Field F] [NumberField F]
    {P P' : GroupScheme (Spec (CommRingCat.of F))} {n : ℕ}
    (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P)
    (e' : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P')
    (L : RealCharacterParameter F P →ₗ[ℝ] RealCharacterParameter F P') (β' : (Fin n → ℝ) → ℝ)
    (hβ' : Continuous β' ∧ HasCompactSupport β' ∧ ∫ y, β' y = 1)
    (hmp : MeasurePreserving (fun x => e'.symm (L (e x))) volume volume) :
    ∃ (e'' : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P') (β'' : (Fin n → ℝ) → ℝ),
      (∀ x, e'' x = L (e x)) ∧ Continuous β'' ∧ HasCompactSupport β'' ∧ ∫ y, β'' y = 1 ∧
      ∀ H, β'' (parameterCoordinates F P' e'' H) = β' (parameterCoordinates F P' e' H) := by
  set τ : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) := e'.symm.toLinearMap ∘ₗ L ∘ₗ e.toLinearMap with hτdef
  have hτ : MeasurePreserving τ volume volume := hmp
  have hsurj := Langlands.Analysis.surjective_of_measurePreserving_linearMap τ hτ
  have hinj : Function.Injective τ := LinearMap.injective_iff_surjective.2 hsurj
  set τe : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) := LinearEquiv.ofBijective τ ⟨hinj, hsurj⟩ with hτe
  set e'' : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P' := τe.trans e' with he''def
  have he'' : ∀ x, e'' x = L (e x) := fun x => by
    show e' (e'.symm (L (e x))) = _
    exact e'.apply_symm_apply _
  set ρ : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    Matrix.toLin' (LinearMap.toMatrix' (τe.symm : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))).transpose
    with hρdef
  have hτeτ : (τe : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) = τ := by
    ext x : 1
    rfl
  have hdetρ : |LinearMap.det ρ| = 1 := by
    rw [hρdef, Langlands.Analysis.det_toLin'_transpose_toMatrix', LinearEquiv.det_coe_symm,
      abs_inv, hτeτ, Langlands.Analysis.abs_det_eq_one_of_measurePreserving τ hτ, inv_one]
  have hdet0 : LinearMap.det ρ ≠ 0 := by
    intro h
    rw [h, abs_zero] at hdetρ
    exact zero_ne_one hdetρ
  have hpc : ∀ H, parameterCoordinates F P' e' H = ρ (parameterCoordinates F P' e'' H) := by
    intro H
    have key := Langlands.Analysis.linearForm_comp_single_eq_transpose
      ((realParameterPairing F P').flip H ∘ₗ e''.toLinearMap)
      (τe.symm : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    have h1 : (fun j => ((realParameterPairing F P').flip H ∘ₗ e''.toLinearMap)
        ((τe.symm : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) (Pi.single j 1))) =
        parameterCoordinates F P' e' H := by
      funext j
      simp [parameterCoordinates, e'']
    have h2 : (fun i => ((realParameterPairing F P').flip H ∘ₗ e''.toLinearMap)
        (Pi.single i 1)) = parameterCoordinates F P' e'' H := by
      funext i
      simp [parameterCoordinates]
    rw [← h1, key, h2]
  set ρc : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ) :=
    (LinearMap.equivOfDetNeZero ρ hdet0).toContinuousLinearEquiv with hρc
  have hρcρ : (ρc : (Fin n → ℝ) → (Fin n → ℝ)) = ρ := by
    ext x : 1
    simp [ρc, LinearMap.equivOfDetNeZero]
  refine ⟨e'', fun y => β' (ρ y), he'', hβ'.1.comp ρ.continuous_of_finiteDimensional, ?_, ?_,
    fun H => by rw [hpc H]⟩
  · have := hβ'.2.1.comp_isClosedEmbedding ρc.toHomeomorph.isClosedEmbedding
    rwa [ContinuousLinearEquiv.coe_toHomeomorph, hρcρ] at this
  · rw [Langlands.Analysis.integral_comp_linearMap_of_abs_det_eq_one ρ hdetρ
      hβ'.1.aestronglyMeasurable, hβ'.2.2]

/-! ### Geometry of the presented parabolic -/

end LocalWavePacketNormBound

/-- The bound (19) of Lapid's Lemma 10 for smooth wave packets (`LocalWavePacketNormBoundStatement`)
follows from Lapid's formula (4) for smooth wave packets, finite square-integrable expansions of
the intertwining operators, their unitarity on the imaginary axis and the positivity of `(·,·)_P`
in Gram form. -/
def LocalWavePacketNormBoundReductionStatement : Prop :=
  LocalWavePacketInnerProductStatement → IntertwiningSquareIntegrableExpansionStatement →
    IntertwiningImaginaryUnitarityStatement → InducedInnerProductGramStatement →
    LocalWavePacketNormBoundStatement

set_option maxHeartbeats 4000000 in
/-- Proof of `LocalWavePacketNormBoundReductionStatement`: Lapid's argument for (19), formula (4)
with `φ' = φ`, unitarity, Gram positivity and the invariance of the spectral measure under
`Ω(P, P)`. -/
theorem localWavePacketNormBoundReduction : LocalWavePacketNormBoundReductionStatement := by
  intro hA1 hEx hUn hGr F _ _ G P M U A _ _ _ _ _ _ _ p _ iU l _ a r _ _ _ hA hT π hG hUR hπ K hK
    N d rho hsmooth hcalc hKmax hrho μM _ hμM n e β hβc hβs hβ1 k v c S E D hv hS hc hD hEm hEis
    Θ φ μG
  classical
  have : LocallyOfFiniteType P.X.hom :=
    IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
  have hpar := r.isCompatible.parabolic
  have hlevi := r.isCompatible.levi
  have hMul := Langlands.Plancherel.parabolicRadical_isIso_subgroupMultiplication r hG hUR
  -- sesquilinearity of `(·,·)_P` on finite families in `A^2_P`
  have hInt := inducedInnerProductIntegrable F G P M U A p iU l a r hA hT π hG hUR hπ K hK rho
    hsmooth hcalc hKmax hrho μM hμM e β hβc hβs
  have sesq : ∀ {X Y : Type} [Fintype X] [Fintype Y] (a' : X → ℂ)
      (f : X → AdelicGroupPoints F G → ℂ) (b : Y → ℂ) (g : Y → AdelicGroupPoints F G → ℂ),
      (∀ x, IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l (f x)) →
      (∀ y, IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l (g y)) →
      inducedInnerProduct K hK.isCompact p l μM e β (fun z => ∑ x, a' x * f x z)
          (fun z => ∑ y, b y * g y z) =
        ∑ x, ∑ y, a' x * conj (b y) * inducedInnerProduct K hK.isCompact p l μM e β (f x) (g y) := by
    intro X Y _ _ a' f b g hf hg
    exact inducedInnerProduct_sum_sum K hK.isCompact p l μM e β a' f b g
      (fun x y => hInt (f x) (g y) (hf x) (hg y))
  -- the self Weyl set and an enumeration of it
  have hfin := finite_weylParameterSet_self r π
  let T := ↥(weylParameterSet p l p l π)
  let _ : Fintype T := hfin.fintype
  have hmemT : ∀ t : T, ∃ (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (c' : M ⟶ M),
      IsWeylConjugation p l p l w c' ∧ weylParameter l c' π = t.1 := fun t => t.2
  choose w cw hW hwp using hmemT
  have hinj : Function.Injective (fun t : T => weylParameter l (cw t) π) := by
    intro t t' h
    apply Subtype.ext
    rw [← hwp t, ← hwp t']
    exact h
  have hsurj : ∀ s ∈ weylParameterSet p l p l π, ∃ t : T, weylParameter l (cw t) π = s :=
    fun s hs => ⟨⟨s, hs⟩, hwp _⟩
  -- finite square-integrable expansions of `M(w_t, λ) v j`
  have hEt : ∀ (t : T) (j : Fin k), ∃ (kk : ℕ) (ψ' : Fin kk → AdelicGroupPoints F G → ℂ)
      (cf : Fin kk → ComplexCharacterParameter F P → ℂ) (Dd : Set (ComplexCharacterParameter F P)),
      (∀ i, IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l (ψ' i)) ∧
      Set.range (imaginaryParameter F P) ⊆ Dd ∧
      (∀ i, IsMeromorphicInCoordinatesOn (cf i) Dd) ∧
      ∃ R₀ : ℝ, ∀ lam : ComplexCharacterParameter F P, r.IsRegularParameter hA hT R₀ lam →
        ∀ g : AdelicGroupPoints F G,
          hK.intertwiningOperator hK iU l iU (cw t) π (w t) (v j) lam g =
            ∑ i, cf i lam * ψ' i g :=
    fun t j => hEx F G P M U P M U A A p iU l a r hA hT p iU l a r π (w t) (cw t) hG hUR hUR hMul
      hπ (hW t) K hK hK rho hsmooth hcalc (v j) hKmax hrho (hv j)
  choose kk ψ' cf Dd hψ' hDd hcf hexp' using hEt
  -- padding to a common length `m`
  let m : ℕ := ∑ t, ∑ j, kk t j
  have hkm : ∀ t j, kk t j ≤ m := fun t j =>
    (Finset.single_le_sum (f := fun j => kk t j) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun t => ∑ j, kk t j) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ t))
  let ψ : T → Fin k → Fin m → AdelicGroupPoints F G → ℂ := fun t j i =>
    if h : (i : ℕ) < kk t j then ψ' t j ⟨i, h⟩ else v j
  let coeff : T → Fin k → Fin m → ComplexCharacterParameter F P → ℂ := fun t j i =>
    if h : (i : ℕ) < kk t j then cf t j ⟨i, h⟩ else fun _ => 0
  have hψ : ∀ t j i,
      IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l (ψ t j i) := by
    intro t j i
    simp only [ψ]
    split_ifs with h
    · exact hψ' t j _
    · exact hv j
  have hterm : ∀ t j (i : Fin m) lam g, coeff t j i lam * ψ t j i g =
      if h : (i : ℕ) < kk t j then cf t j ⟨i, h⟩ lam * ψ' t j ⟨i, h⟩ g else 0 := by
    intro t j i lam g
    simp only [coeff, ψ]
    split_ifs <;> simp
  have hexp : ∀ t j, ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → ∀ g,
      hK.intertwiningOperator hK iU l iU (cw t) π (w t) (v j) lam g =
        ∑ i, coeff t j i lam * ψ t j i g := by
    intro t j
    obtain ⟨R₀, hR₀⟩ := hexp' t j
    refine ⟨R₀, fun lam hlam g => ?_⟩
    rw [hR₀ lam hlam g]
    simp only [hterm]
    exact (LocalWavePacketNormBound.sum_fin_dite_eq (hkm t j)
      (fun i => cf t j i lam * ψ' t j i g)).symm
  -- a common domain of meromorphy
  choose Dd' hDsub hcf' hinter using fun t j =>
    exists_domain_of_isMeromorphicInCoordinatesOn (hcf t j)
  let DM : Set (ComplexCharacterParameter F P) :=
    D ∩ ⋂ q ∈ (Finset.univ : Finset (T × Fin k)), Dd' q.1 q.2
  have hDM : (fun x => imaginaryParameter F P (e x)) '' S ⊆ DM := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨hD ⟨x, hx, rfl⟩, ?_⟩
    simp only [Set.mem_iInter]
    intro q _
    exact hDsub q.1 q.2 (hDd q.1 q.2 ⟨e x, rfl⟩)
  have hinterDM : ∀ (f : ComplexCharacterParameter F P → ℂ) (V : Set _),
      IsMeromorphicInCoordinatesOn f V → IsMeromorphicInCoordinatesOn f
        (V ∩ ⋂ q ∈ (Finset.univ : Finset (T × Fin k)), Dd' q.1 q.2) :=
    fun f V hf => LocalWavePacketNormBound.isMeromorphicInCoordinatesOn_inter_biInter _
      (fun q : T × Fin k => Dd' q.1 q.2)
      (fun (q : T × Fin k) f U hfU => hinter q.1 q.2 f U hfU) hf
  have hcoeff : ∀ t j i, IsMeromorphicInCoordinatesOn (coeff t j i) DM := by
    intro t j i
    simp only [coeff]
    split_ifs with h
    · have h2 := hinterDM _ _ (isMeromorphicInCoordinatesOn_inter_of (hcf' t j ⟨i, h⟩) (hEm j 1))
      have heq : (Dd' t j ∩ D) ∩ ⋂ q ∈ (Finset.univ : Finset (T × Fin k)), Dd' q.1 q.2 = DM := by
        ext x
        simp only [DM, Set.mem_inter_iff, Set.mem_iInter]
        constructor
        · rintro ⟨⟨_, hxD⟩, hx⟩
          exact ⟨hxD, hx⟩
        · rintro ⟨hxD, hx⟩
          exact ⟨⟨hx (t, j) (Finset.mem_univ _), hxD⟩, hx⟩
      rwa [heq] at h2
    · exact hinterDM _ _ (isMeromorphicInCoordinatesOn_zero_of (hEm j 1))
  -- Weyl coordinate changes preserve Lebesgue measure; transported coordinates and weights
  have hmp : ∀ t : T, MeasurePreserving
      (fun x => e.symm (realWeylParameter l (cw t) π (e x))) volume volume :=
    fun t => measurePreserving_realWeylParameter r hπ (hW t) e
  choose e'' β'' he'' hβ''c hβ''s hβ''1 hβ'' using fun t : T =>
    LocalWavePacketNormBound.exists_transported_weight e e (realWeylParameter l (cw t) π) β
      ⟨hβc, hβs, hβ1⟩ (hmp t)
  have hIP'' : ∀ (t : T) (f g : AdelicGroupPoints F G → ℂ),
      inducedInnerProduct K hK.isCompact p l μM (e'' t) (β'' t) f g =
        inducedInnerProduct K hK.isCompact p l μM e β f g := by
    intro t f g
    unfold inducedInnerProduct
    simp only [hβ'' t]
  -- unitarity of `M(w_t, λ)` on the imaginary axis
  have hUt := fun t : T => hUn F G P M U P M U A p iU l a r hA hT p iU l π (w t) (cw t) hG hUR hpar
    hUR hlevi hMul hπ (hW t) K hK hK rho hsmooth hcalc hKmax hrho μM μM hμM hμM e (e'' t)
    (he'' t) β (β'' t) hβc hβs hβ1 (hβ''c t) (hβ''s t) (hβ''1 t) k m v (ψ t) (coeff t) DM hv
    (hψ t) (hcoeff t) (hexp t)
  choose coeff'' DM'' hDM'' _hmero hagree hgram using hUt
  -- formula (4) with `φ' = φ`
  have h4 := hA1 F G P M U P M U A A p iU l a r hA hT p iU l a r hA hT π hG hUR hUR hπ K hK hK rho
    hsmooth hcalc hKmax hrho μM hμM e e β hβc hβs hβ1 k v c S E D hv hS hc hD hEm hEis k v c S
    E D hv hS hc hD hEm hEis T w cw hW hinj hsurj m ψ coeff DM hψ hDM hcoeff hexp
  obtain ⟨hL2, -, h4eq⟩ := h4
  -- the diagonal `‖φ(x)‖²_P` and the Weyl terms of (4), as functions of the coordinates
  obtain ⟨Ncf, hNcf⟩ : ∃ f : (Fin n → ℝ) → ℂ, ∀ x, f x = ∑ j, ∑ j', c j x * conj (c j' x) *
      inducedInnerProduct K hK.isCompact p l μM e β (v j) (v j') := ⟨_, fun _ => rfl⟩
  obtain ⟨Bt, hBt⟩ : ∃ f : T → (Fin n → ℝ) → ℂ, ∀ t x, f t x = ∑ j, ∑ i, ∑ j',
      c j x * coeff t j i (imaginaryParameter F P (e x)) *
        conj (c j' (e.symm (realWeylParameter l (cw t) π (e x)))) *
        inducedInnerProduct K hK.isCompact p l μM e β (ψ t j i) (v j') := ⟨_, fun _ _ => rfl⟩
  -- the pointwise estimate `2 Re (M(s, λ)φ(λ), φ(sλ))_P ≤ ‖φ(λ)‖²_P + ‖φ(sλ)‖²_P`
  have hpt : ∀ (t : T) (x : Fin n → ℝ), 2 * (Bt t x).re ≤ (Ncf x).re +
      (Ncf (e.symm (realWeylParameter l (cw t) π (e x)))).re := by
    intro t x
    have hpos : ∀ z : (Fin k × Fin m) ⊕ Fin k → ℂ, 0 ≤ ∑ a, ∑ b, z a * conj (z b) *
        inducedInnerProduct K hK.isCompact p l μM e β
          (Sum.elim (fun a : Fin k × Fin m => ψ t a.1 a.2) v a)
          (Sum.elim (fun a : Fin k × Fin m => ψ t a.1 a.2) v b) :=
      LocalWavePacketNormBound.gram_nonneg_of_fin
        (IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l)
        (inducedInnerProduct K hK.isCompact p l μM e β)
        (fun m' f hf z => (hGr F G P M U p iU l hG hpar hUR hlevi hMul K hK rho hsmooth hcalc μM
          e β hβc hβs hβ1 m' f hf z).1)
        (Sum.elim (fun a : Fin k × Fin m => ψ t a.1 a.2) v)
        (fun a => by
          cases a with
          | inl a => exact hψ t a.1 a.2
          | inr b => exact hv b)
    have key := LocalWavePacketNormBound.two_mul_re_cross_le
      (fun a b => inducedInnerProduct K hK.isCompact p l μM e β
        (Sum.elim (fun a : Fin k × Fin m => ψ t a.1 a.2) v a)
        (Sum.elim (fun a : Fin k × Fin m => ψ t a.1 a.2) v b)) hpos
      (fun a : Fin k × Fin m => c a.1 x * coeff t a.1 a.2 (imaginaryParameter F P (e x)))
      (fun b => c b (e.symm (realWeylParameter l (cw t) π (e x))))
    simp only [Sum.elim_inl, Sum.elim_inr] at key
    have hB : (∑ a : Fin k × Fin m, ∑ b : Fin k,
        c a.1 x * coeff t a.1 a.2 (imaginaryParameter F P (e x)) *
          conj (c b (e.symm (realWeylParameter l (cw t) π (e x)))) *
          inducedInnerProduct K hK.isCompact p l μM e β (ψ t a.1 a.2) (v b)) = Bt t x := by
      rw [hBt, Fintype.sum_prod_type]
    have hC : (∑ b : Fin k, ∑ b' : Fin k,
        c b (e.symm (realWeylParameter l (cw t) π (e x))) *
          conj (c b' (e.symm (realWeylParameter l (cw t) π (e x)))) *
          inducedInnerProduct K hK.isCompact p l μM e β (v b) (v b')) =
        Ncf (e.symm (realWeylParameter l (cw t) π (e x))) := by
      rw [hNcf]
    have hA' : (∑ a : Fin k × Fin m, ∑ a' : Fin k × Fin m,
        c a.1 x * coeff t a.1 a.2 (imaginaryParameter F P (e x)) *
          conj (c a'.1 x * coeff t a'.1 a'.2 (imaginaryParameter F P (e x))) *
          inducedInnerProduct K hK.isCompact p l μM e β (ψ t a.1 a.2) (ψ t a'.1 a'.2)) =
        Ncf x := by
      have e1 := sesq
        (fun a : Fin k × Fin m => c a.1 x * coeff t a.1 a.2 (imaginaryParameter F P (e x)))
        (fun a => ψ t a.1 a.2)
        (fun a : Fin k × Fin m => c a.1 x * coeff t a.1 a.2 (imaginaryParameter F P (e x)))
        (fun a => ψ t a.1 a.2) (fun a => hψ t a.1 a.2) (fun a => hψ t a.1 a.2)
      have e2 := sesq
        (fun a : Fin k × Fin m => c a.1 x * coeff'' t a.1 a.2 (imaginaryParameter F P (e x)))
        (fun a => ψ t a.1 a.2)
        (fun a : Fin k × Fin m => c a.1 x * coeff'' t a.1 a.2 (imaginaryParameter F P (e x)))
        (fun a => ψ t a.1 a.2) (fun a => hψ t a.1 a.2) (fun a => hψ t a.1 a.2)
      have hfun : (fun z => ∑ a : Fin k × Fin m,
            c a.1 x * coeff t a.1 a.2 (imaginaryParameter F P (e x)) * ψ t a.1 a.2 z) =
          fun z => ∑ a : Fin k × Fin m,
            c a.1 x * coeff'' t a.1 a.2 (imaginaryParameter F P (e x)) * ψ t a.1 a.2 z := by
        funext z
        simp only [Fintype.sum_prod_type, mul_assoc, ← Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hx : x ∈ S
        · rw [hagree t j _ ⟨hDM ⟨x, hx, rfl⟩, hDM'' t ⟨e x, rfl⟩⟩ z]
        · rw [(hc j).2 x hx, zero_mul, zero_mul]
      rw [← e1, hfun, e2, hNcf]
      simp only [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j' _ => ?_
      rw [← hgram t (e x) j j', Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i' _ => ?_
      rw [hIP'' t, map_mul]
      ring
    rw [hB, hC, hA'] at key
    exact key
  -- integrability
  have hcs : ∀ j, Continuous (c j) := fun j => (hc j).1.continuous
  have hy : ∀ t : T, Continuous (fun x => e.symm (realWeylParameter l (cw t) π (e x))) :=
    fun t => (e.symm.toLinearMap ∘ₗ realWeylParameter l (cw t) π ∘ₗ
      e.toLinearMap).continuous_of_finiteDimensional
  have hcu : ∀ t j i,
      Continuous (fun x => c j x * coeff t j i (imaginaryParameter F P (e x))) := by
    intro t j i
    obtain ⟨hopen, hcont⟩ :=
      BoundedWavePacket.isOpen_and_continuousOn_of_isMeromorphicInCoordinatesOn
        ((imaginaryParameter F P).comp e.toLinearMap) (hcoeff t j i)
    exact LocalWavePacketNormBound.continuous_mul_of_eq_zero hS.isClosed hopen
      (fun x hx => hDM ⟨x, hx, rfl⟩) (hcs j) (fun x hx => (hc j).2 x hx) hcont
  have hNcf_cont : Continuous Ncf ∧ ∀ x ∉ S, Ncf x = 0 := by
    refine ⟨?_, fun x hx => ?_⟩
    · rw [show Ncf = fun x => ∑ j, ∑ j', c j x * conj (c j' x) *
          inducedInnerProduct K hK.isCompact p l μM e β (v j) (v j') from funext hNcf]
      exact continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun j' _ =>
        ((hcs j).mul (Complex.continuous_conj.comp (hcs j'))).mul continuous_const
    · rw [hNcf]
      simp [(hc _).2 x hx]
  have hNint := LocalWavePacketNormBound.integrable_of_continuous_of_eq_zero hNcf_cont.1 hS
    hNcf_cont.2
  have hBt_cont : ∀ t, Continuous (Bt t) ∧ ∀ x ∉ S, Bt t x = 0 := by
    intro t
    refine ⟨?_, fun x hx => ?_⟩
    · rw [show Bt t = fun x => ∑ j, ∑ i, ∑ j',
          c j x * coeff t j i (imaginaryParameter F P (e x)) *
            conj (c j' (e.symm (realWeylParameter l (cw t) π (e x)))) *
            inducedInnerProduct K hK.isCompact p l μM e β (ψ t j i) (v j') from funext (hBt t)]
      exact continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun i _ =>
        continuous_finsetSum _ fun j' _ =>
          ((hcu t j i).mul (Complex.continuous_conj.comp ((hcs j').comp (hy t)))).mul
            continuous_const
    · rw [hBt]
      simp [(hc _).2 x hx]
  have hBint : ∀ t, Integrable (Bt t) (spectralMeasure n) := fun t =>
    (LocalWavePacketNormBound.integrable_of_continuous_of_eq_zero (hBt_cont t).1 hS
      (hBt_cont t).2).2
  have hre_int : ∀ {f : (Fin n → ℝ) → ℂ}, Integrable f (spectralMeasure n) →
      ∫ x, (f x).re ∂(spectralMeasure n) = (∫ x, f x ∂(spectralMeasure n)).re :=
    fun hf => integral_re hf
  have hreI : ∀ {f : (Fin n → ℝ) → ℂ}, Integrable f (spectralMeasure n) →
      Integrable (fun x => (f x).re) (spectralMeasure n) := fun hf => hf.re
  have hNy : ∀ t : T, Integrable (fun x => Ncf (e.symm (realWeylParameter l (cw t) π (e x))))
      (spectralMeasure n) :=
    fun t => integrable_comp_spectralMeasure _ (hmp t) Ncf hNint.1
  -- each Weyl term is at most `‖φ‖²_*`
  have hterm_le : ∀ t : T, ∫ x, (Bt t x).re ∂(spectralMeasure n) ≤
      ∫ x, (Ncf x).re ∂(spectralMeasure n) := by
    intro t
    have h1 : ∫ x, (Bt t x).re ∂(spectralMeasure n) ≤
        ∫ x, ((Ncf x).re + (Ncf (e.symm (realWeylParameter l (cw t) π (e x)))).re) / 2
          ∂(spectralMeasure n) :=
      integral_mono (hreI (hBint t)) (((hreI hNint.2).add (hreI (hNy t))).div_const 2)
        fun x => by linarith [hpt t x]
    have h2 : ∫ x, ((Ncf x).re + (Ncf (e.symm (realWeylParameter l (cw t) π (e x)))).re) / 2
          ∂(spectralMeasure n) =
        (∫ x, (Ncf x).re ∂(spectralMeasure n) +
          ∫ x, (Ncf (e.symm (realWeylParameter l (cw t) π (e x)))).re ∂(spectralMeasure n)) / 2 := by
      rw [integral_div, integral_add (hreI hNint.2) (hreI (hNy t))]
    have h3 : ∫ x, (Ncf (e.symm (realWeylParameter l (cw t) π (e x)))).re ∂(spectralMeasure n) =
        ∫ x, (Ncf x).re ∂(spectralMeasure n) := by
      rw [hre_int (hNy t), hre_int hNint.2,
        integral_comp_spectralMeasure rfl _ (hmp t) Ncf hNcf_cont.1]
    linarith
  have hNc : ∀ x, inducedInnerProduct K hK.isCompact p l μM e β (φ x) (φ x) = Ncf x := fun x => by
    rw [hNcf]
    exact sesq (fun j => c j x) v (fun j => c j x) v hv hv
  have hlhs : ∫ y, ‖Θ y.out‖ ^ 2 ∂μG = (∫ y, Θ y.out * conj (Θ y.out) ∂μG).re := by
    have : (fun y : RationalQuotient F G => Θ y.out * conj (Θ y.out)) =
        fun y => ((‖Θ y.out‖ ^ 2 : ℝ) : ℂ) := by
      funext z
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [this, integral_complex_ofReal, Complex.ofReal_re]
  have h4eq' : ∫ y, Θ y.out * conj (Θ y.out) ∂μG = ∫ x, ∑ t, Bt t x ∂(spectralMeasure n) := by
    simp only [hBt]
    exact h4eq
  refine ⟨hfin, hL2, ?_⟩
  rw [hlhs, h4eq', ← hre_int (integrable_finsetSum _ fun t _ => hBint t)]
  simp only [Complex.re_sum]
  rw [integral_finsetSum _ fun t _ => hreI (hBint t)]
  calc ∑ t, ∫ x, (Bt t x).re ∂(spectralMeasure n) ≤
        ∑ t : T, ∫ x, (Ncf x).re ∂(spectralMeasure n) := Finset.sum_le_sum fun t _ => hterm_le t
    _ = (Nat.card ↥(weylParameterSet p l p l π) : ℝ) *
        ∫ x, (inducedInnerProduct K hK.isCompact p l μM e β (φ x) (φ x)).re
          ∂(spectralMeasure n) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
      congr 2
      funext x
      rw [hNc x]

end Langlands.Global
