import Langlands.Representation.Plancherel.DynamicOppositeHermitianAdjunctionStatement
import Langlands.Representation.Plancherel.DynamicOppositeUnitaryScalarStatement

/-! # Nonnegativity of `j_P` at unitary points from the Hermitian adjunction

Derived from the proof of Waldspurger IV.3 (6) (printed p.287): for unitary `χ`,
`j(π ⊗ χ) (e, e) = (e, J_{P|P̄} J_{P̄|P} e) = (J_{P̄|P} e, J_{P̄|P} e) ≥ 0`.

* `unramifiedDagger` is `f ↦ f†`, `f†(z) = conj (f (z†))`, on the regular functions of
  unramified characters, with `z† = z̄⁻¹`.
* `compactPictureInnerCore` shows that the compact-picture pairing
  `(φ, ψ) = ∫_K b(φ(k), ψ(k)) dk` is a positive definite Hermitian form, and
  `compactPictureSesq` packages it as a sesquilinear form.
* `continuedOperator_adjoint` (generic): if two operator families are adjoint,
  `sW (A w v) w' = sV v (B w† w')`, on a nonempty open set of parameters, then so are their
  rational continuations wherever both sides are regular. The proof uses the identity theorem
  `rationalUnramifiedRegular_eq_zero_of_isOpen`.
* `continuedCompositeRationalScalar_nonnegAt` (generic): the coefficient of the continued
  composite extracted by `v` and `(sV v v)⁻¹ sV v` is regular and nonnegative at self-dual
  common regular points.
* `ConditionalDynamicOppositeUnitaryNonnegStatement` is the target: `j_P` is regular with a
  nonnegative real value at every unitary common regular point.
* `conditionalDynamicOppositeUnitaryNonneg_of_hermitianAdjunction` proves the target from the
  Hermitian adjunction target `ConditionalDynamicOppositeHermitianAdjunctionStatement`.
-/

noncomputable section

universe u uV uW uG uI

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ComplexConjugate
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

/-! ### The dagger of a regular function -/

section Dagger

variable {G : Type uG} [Group G] [TopologicalSpace G] {I : Type uI} (ν : I → (G →* ℝ≥0ˣ))

/-- `f†(z) = conj (f (z†))` for a function `f` on unramified characters. -/
def unramifiedDaggerFun (f : unramifiedCharacters ν → ℂ) : unramifiedCharacters ν → ℂ :=
  fun z => conj (f (unramifiedConjInv ν z))

theorem unramifiedDaggerFun_evaluation (g : G) :
    unramifiedDaggerFun ν (unramifiedEvaluation ν g) = unramifiedEvaluation ν g⁻¹ := by
  funext z
  simp only [unramifiedDaggerFun, unramifiedEvaluation, unramifiedConjInv_val,
    characterConjInv_apply_coe, map_inv₀, Complex.conj_conj, map_inv, Units.val_inv_eq_inv_val]

/-- The dagger preserves the regular functions. -/
theorem unramifiedDaggerFun_mem {f : unramifiedCharacters ν → ℂ}
    (hf : f ∈ unramifiedRegularFunctions ν) :
    unramifiedDaggerFun ν f ∈ unramifiedRegularFunctions ν := by
  unfold unramifiedRegularFunctions at hf ⊢
  induction hf using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    rw [unramifiedDaggerFun_evaluation]
    exact Algebra.subset_adjoin ⟨g⁻¹, rfl⟩
  | algebraMap r =>
    have he : unramifiedDaggerFun ν (algebraMap ℂ (unramifiedCharacters ν → ℂ) r) =
        algebraMap ℂ (unramifiedCharacters ν → ℂ) (conj r) := by
      funext z
      simp [unramifiedDaggerFun]
    rw [he]
    exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy =>
    have he : unramifiedDaggerFun ν (x + y) =
        unramifiedDaggerFun ν x + unramifiedDaggerFun ν y := by
      funext z
      simp [unramifiedDaggerFun]
    rw [he]
    exact Subalgebra.add_mem _ hx hy
  | mul x y _ _ hx hy =>
    have he : unramifiedDaggerFun ν (x * y) =
        unramifiedDaggerFun ν x * unramifiedDaggerFun ν y := by
      funext z
      simp [unramifiedDaggerFun]
    rw [he]
    exact Subalgebra.mul_mem _ hx hy

/-- The dagger `f ↦ f†` on regular functions. -/
def unramifiedDagger (f : unramifiedRegularFunctions ν) : unramifiedRegularFunctions ν :=
  ⟨unramifiedDaggerFun ν f.val, unramifiedDaggerFun_mem ν f.property⟩

@[simp]
theorem unramifiedDagger_apply (f : unramifiedRegularFunctions ν) (z : unramifiedCharacters ν) :
    (unramifiedDagger ν f).val z = conj (f.val (unramifiedConjInv ν z)) := rfl

/-- Evaluation of regular functions at a point, as an algebra homomorphism. -/
def unramifiedRegularEval (z : unramifiedCharacters ν) : unramifiedRegularFunctions ν →ₐ[ℂ] ℂ :=
  (Pi.evalAlgHom ℂ (fun _ => ℂ) z).comp (unramifiedRegularFunctions ν).val

@[simp]
theorem unramifiedRegularEval_apply (z : unramifiedCharacters ν)
    (f : unramifiedRegularFunctions ν) : unramifiedRegularEval ν z f = f.val z := rfl

end Dagger

/-! ### The compact-picture pairing is a positive definite Hermitian form -/

section PairingCore

open Aubert.General

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (A : SmoothRep.{0, uG, uV} ℂ M) (b : InvariantPositiveForm A.representation)

omit [LocallyCompactSpace G] [SecondCountableTopology G] in
theorem compactPictureHermitianPairing_integrable (φ ψ : CompactInductionPicture h K A) :
    Integrable (fun k : K => b.inner (Induction.eval _ _ φ k) (Induction.eval _ _ ψ k))
      (CompactInduction.measure K hK) := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hc : Continuous
      (fun k : K => b.inner (Induction.eval _ _ φ k) (Induction.eval _ _ ψ k)) :=
    (Induction.pairing_isLocallyConstant _ _ b.toInnerProductCore φ ψ).continuous
  exact hc.integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact

set_option warn.classDefReducibility false in
/-- The compact-picture pairing as an inner product core. -/
def compactPictureInnerCore : InnerProductSpace.Core ℂ (CompactInductionPicture h K A) where
  inner φ ψ := compactPictureHermitianPairing h K hK A b φ ψ
  conj_inner_symm φ ψ := by
    unfold compactPictureHermitianPairing
    rw [← integral_conj]
    exact integral_congr_ae (Filter.Eventually.of_forall fun k =>
      b.conj_inner_symm (Induction.eval _ _ φ k) (Induction.eval _ _ ψ k))
  re_inner_nonneg φ := by
    unfold compactPictureHermitianPairing
    rw [← integral_re (compactPictureHermitianPairing_integrable h K hK A b φ φ)]
    exact integral_nonneg fun k => b.re_inner_nonneg (Induction.eval _ _ φ k)
  add_left φ ψ χ := by
    unfold compactPictureHermitianPairing
    change (∫ k : K, b.inner (Induction.eval _ _ φ k + Induction.eval _ _ ψ k)
      (Induction.eval _ _ χ k) ∂CompactInduction.measure K hK) = _
    simp_rw [b.add_left]
    exact integral_add (compactPictureHermitianPairing_integrable h K hK A b φ χ)
      (compactPictureHermitianPairing_integrable h K hK A b ψ χ)
  smul_left φ ψ c := by
    unfold compactPictureHermitianPairing
    change (∫ k : K, b.inner (c • Induction.eval _ _ φ k)
      (Induction.eval _ _ ψ k) ∂CompactInduction.measure K hK) = _
    simp_rw [b.smul_left]
    exact integral_const_mul _ _
  definite φ hφ := by
    let : IsTopologicalGroup K := inferInstanceAs (IsTopologicalGroup (K : Subgroup G))
    let hmK : Measure.IsHaarMeasure (CompactInduction.measure K hK) :=
      CompactInduction.measure_isHaar K hK
    let : (CompactInduction.measure K hK).IsOpenPosMeasure := hmK.toIsOpenPosMeasure
    let : InnerProductSpace.Core ℂ A := b.toInnerProductCore
    have hzero : (∫ k : K, (b.inner (Induction.eval _ _ φ k)
        (Induction.eval _ _ φ k)).re ∂CompactInduction.measure K hK) = 0 := by
      change (∫ k : K, RCLike.re (b.inner (Induction.eval _ _ φ k)
        (Induction.eval _ _ φ k)) ∂CompactInduction.measure K hK) = 0
      rw [integral_re (compactPictureHermitianPairing_integrable h K hK A b φ φ)]
      change RCLike.re (compactPictureHermitianPairing h K hK A b φ φ) = 0
      rw [hφ]
      rfl
    have hae : (fun k : K => (b.inner (Induction.eval _ _ φ k)
        (Induction.eval _ _ φ k)).re) =ᵐ[CompactInduction.measure K hK] 0 :=
      (integral_eq_zero_iff_of_nonneg
        (fun k : K => b.re_inner_nonneg (Induction.eval _ _ φ k))
        (compactPictureHermitianPairing_integrable h K hK A b φ φ).re).mp hzero
    have hcont : Continuous
        (fun k : K => (b.inner (Induction.eval _ _ φ k) (Induction.eval _ _ φ k)).re) :=
      ((Induction.pairing_isLocallyConstant _ _ b.toInnerProductCore φ φ).comp
        Complex.re).continuous
    have heq := Measure.eq_of_ae_eq hae hcont continuous_const
    have hkzero (k : K) : Induction.eval _ _ φ k = 0 := by
      apply (InnerProductSpace.Core.normSq_eq_zero (𝕜 := ℂ)).mp
      exact congrFun heq k
    apply Subtype.ext
    apply Subtype.ext
    funext k
    exact hkzero k

omit [LocallyCompactSpace G] [SecondCountableTopology G] in
theorem compactPictureHermitianPairing_add_right (φ ψ ψ' : CompactInductionPicture h K A) :
    compactPictureHermitianPairing h K hK A b φ (ψ + ψ') =
      compactPictureHermitianPairing h K hK A b φ ψ +
        compactPictureHermitianPairing h K hK A b φ ψ' := by
  let c := compactPictureInnerCore h K hK A b
  have h1 := c.conj_inner_symm φ (ψ + ψ')
  have h2 := c.conj_inner_symm φ ψ
  have h3 := c.conj_inner_symm φ ψ'
  change conj (compactPictureHermitianPairing h K hK A b (ψ + ψ') φ) =
    compactPictureHermitianPairing h K hK A b φ (ψ + ψ') at h1
  change conj (compactPictureHermitianPairing h K hK A b ψ φ) =
    compactPictureHermitianPairing h K hK A b φ ψ at h2
  change conj (compactPictureHermitianPairing h K hK A b ψ' φ) =
    compactPictureHermitianPairing h K hK A b φ ψ' at h3
  have h4 : compactPictureHermitianPairing h K hK A b (ψ + ψ') φ =
      compactPictureHermitianPairing h K hK A b ψ φ +
        compactPictureHermitianPairing h K hK A b ψ' φ := c.add_left ψ ψ' φ
  rw [← h1, ← h2, ← h3, h4, map_add]

omit [LocallyCompactSpace G] [SecondCountableTopology G] in
theorem compactPictureHermitianPairing_smul_right (c : ℂ) (φ ψ : CompactInductionPicture h K A) :
    compactPictureHermitianPairing h K hK A b φ (c • ψ) =
      c * compactPictureHermitianPairing h K hK A b φ ψ := by
  let C := compactPictureInnerCore h K hK A b
  have h1 := C.conj_inner_symm φ (c • ψ)
  have h2 := C.conj_inner_symm φ ψ
  change conj (compactPictureHermitianPairing h K hK A b (c • ψ) φ) =
    compactPictureHermitianPairing h K hK A b φ (c • ψ) at h1
  change conj (compactPictureHermitianPairing h K hK A b ψ φ) =
    compactPictureHermitianPairing h K hK A b φ ψ at h2
  have h4 : compactPictureHermitianPairing h K hK A b (c • ψ) φ =
      conj c * compactPictureHermitianPairing h K hK A b ψ φ := C.smul_left ψ φ c
  rw [← h1, ← h2, h4, map_mul, Complex.conj_conj]

/-- The compact-picture pairing as a sesquilinear form, conjugate-linear in the first
argument. -/
def compactPictureSesq :
    CompactInductionPicture h K A →ₗ⋆[ℂ] CompactInductionPicture h K A →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (compactPictureHermitianPairing h K hK A b)
    (fun φ φ' ψ => (compactPictureInnerCore h K hK A b).add_left φ φ' ψ)
    (fun c φ ψ => (compactPictureInnerCore h K hK A b).smul_left φ ψ c)
    (fun φ ψ ψ' => compactPictureHermitianPairing_add_right h K hK A b φ ψ ψ')
    (fun c φ ψ => compactPictureHermitianPairing_smul_right h K hK A b c φ ψ)

omit [LocallyCompactSpace G] [SecondCountableTopology G] in
@[simp]
theorem compactPictureSesq_apply (φ ψ : CompactInductionPicture h K A) :
    compactPictureSesq h K hK A b φ ψ = compactPictureHermitianPairing h K hK A b φ ψ := rfl

omit [LocallyCompactSpace G] [SecondCountableTopology G] in
/-- On the diagonal the pairing is a nonnegative real number. -/
theorem compactPictureHermitianPairing_self (φ : CompactInductionPicture h K A) :
    ∃ r : ℝ, 0 ≤ r ∧ compactPictureHermitianPairing h K hK A b φ φ = (r : ℂ) := by
  let C := compactPictureInnerCore h K hK A b
  have hsymm : conj (compactPictureHermitianPairing h K hK A b φ φ) =
      compactPictureHermitianPairing h K hK A b φ φ := C.conj_inner_symm φ φ
  refine ⟨(compactPictureHermitianPairing h K hK A b φ φ).re, C.re_inner_nonneg φ, ?_⟩
  exact (Complex.conj_eq_iff_re.mp hsymm).symm

omit [LocallyCompactSpace G] [SecondCountableTopology G] in
/-- The pairing is definite. -/
theorem compactPictureHermitianPairing_self_ne_zero {φ : CompactInductionPicture h K A}
    (hφ : φ ≠ 0) : compactPictureHermitianPairing h K hK A b φ φ ≠ 0 :=
  fun h0 => hφ ((compactPictureInnerCore h K hK A b).definite φ h0)

end PairingCore

/-! ### Adjoint pairs of continued operators -/

section ContinuedAdjoint

open UnramifiedOperatorFamily

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (L : GroupScheme (Spec (CommRingCat.of F)))
  [TopologicalSpace (GroupScheme.rationalPoints L)]
  (hp : Continuous (rationalValuationImageProjection L))
  (hL : GroupScheme.IsConnectedReductive L)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {Ω Λ : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}
  {A : Ω → V →ₗ[ℂ] W} {B : Λ → W →ₗ[ℂ] V}

/-- `u ↦ conj (s u w')`, a linear functional for a form `s` conjugate-linear in its first
argument. -/
def conjLeftFunctional (s : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (w' : W) : W →ₗ[ℂ] ℂ where
  toFun u := conj (s u w')
  map_add' u u' := by simp
  map_smul' c u := by simp

@[simp]
theorem conjLeftFunctional_apply (s : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (w' u : W) :
    conjLeftFunctional s w' u = conj (s u w') := rfl

/-- The continued operator only depends on the underlying parameter. -/
theorem continuedOperator_congr (q : RationalOperatorContinuationData Λ B)
    {x y : unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul)}
    (hx : x ∈ q.regularRegion) (hy : y ∈ q.regularRegion) (h : x = y) :
    q.continuedOperator ⟨x, hx⟩ = q.continuedOperator ⟨y, hy⟩ := by
  subst h
  rfl

include hp hL in
/-- **Adjointness persists under continuation.** Let `p` and `q` continue operator families
`A` on `Ω` and `B` on `Λ`, and let `sV`, `sW` be forms conjugate-linear in the first argument.
If `sW (A w v) w' = sV v (B w† w')` for all `w` in a nonempty open `D ⊆ Ω` with `D† ⊆ Λ`, then
the same identity holds for the continued operators at every regular `z` with `z†` regular for
`q`. -/
theorem continuedOperator_adjoint
    (sV : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (sW : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ)
    (p : RationalOperatorContinuationData Ω A) (q : RationalOperatorContinuationData Λ B)
    {D : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}
    (hD : IsOpen D) (hne : D.Nonempty) (hDΩ : D ⊆ Ω)
    (hdag : ∀ w ∈ D, unramifiedConjInv _ w ∈ Λ)
    (hadj : ∀ (w) (hw : w ∈ D) (v : V) (w' : W),
      sW (A ⟨w, hDΩ hw⟩ v) w' = sV v (B ⟨unramifiedConjInv _ w, hdag w hw⟩ w'))
    (z : p.regularRegion) (hz : unramifiedConjInv _ z.val ∈ q.regularRegion)
    (v : V) (w' : W) :
    sW (p.continuedOperator z v) w' = sV v (q.continuedOperator ⟨_, hz⟩ w') := by
  obtain ⟨a1, ha1⟩ := (isPolynomialOn_scalar_iff _).mp
    ((p.polynomial v).linearMap (conjLeftFunctional sW w'))
  obtain ⟨a2, ha2⟩ := (isPolynomialOn_scalar_iff _).mp
    ((q.polynomial w').linearMap (sV v))
  have hr : unramifiedDagger _ q.denominator * a1 -
      p.denominator * unramifiedDagger _ a2 = 0 := by
    apply rationalUnramifiedRegular_eq_zero_of_isOpen L hp hL _ hD hne
    intro w hw
    have h1 : conj (sW (p.numerator w v) w') = a1.val w := ha1 ⟨w, Set.mem_univ _⟩
    have h2 : sV v (q.numerator (unramifiedConjInv _ w) w') =
        a2.val (unramifiedConjInv _ w) := ha2 ⟨_, Set.mem_univ _⟩
    have hc1 : p.numerator w v = p.denominator.val w • A ⟨w, hDΩ hw⟩ v :=
      LinearMap.congr_fun (p.clears ⟨w, hDΩ hw⟩) v
    have hc2 : q.numerator (unramifiedConjInv _ w) w' =
        q.denominator.val (unramifiedConjInv _ w) •
          B ⟨unramifiedConjInv _ w, hdag w hw⟩ w' :=
      LinearMap.congr_fun (q.clears ⟨unramifiedConjInv _ w, hdag w hw⟩) w'
    have hadj' := hadj w hw v w'
    simp only [Subalgebra.coe_sub, Subalgebra.coe_mul, Pi.sub_apply, Pi.mul_apply,
      unramifiedDagger_apply]
    rw [← h1, ← h2, hc1, hc2]
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, map_smul,
      map_mul, Complex.conj_conj, hadj']
    ring
  have hz0 := congrArg (fun f : unramifiedRegularFunctions _ => f.val z.val) hr
  simp only [Subalgebra.coe_sub, Subalgebra.coe_mul, Pi.sub_apply, Pi.mul_apply,
    unramifiedDagger_apply, ZeroMemClass.coe_zero, Pi.zero_apply] at hz0
  have h1 : conj (sW (p.numerator z.val v) w') = a1.val z.val := ha1 ⟨z.val, Set.mem_univ _⟩
  have h2 : sV v (q.numerator (unramifiedConjInv _ z.val) w') =
      a2.val (unramifiedConjInv _ z.val) := ha2 ⟨_, Set.mem_univ _⟩
  rw [← h1, ← h2] at hz0
  have hX := congrArg conj hz0
  simp only [map_sub, map_mul, Complex.conj_conj, map_zero] at hX
  have hd : p.denominator.val z.val ≠ 0 := z.property
  have he : q.denominator.val (unramifiedConjInv _ z.val) ≠ 0 := hz
  have hd' : conj (p.denominator.val z.val) ≠ 0 := (map_ne_zero _).mpr hd
  change sW ((p.denominator.val z.val)⁻¹ • p.numerator z.val v) w' =
    sV v ((q.denominator.val (unramifiedConjInv _ z.val))⁻¹ •
      q.numerator (unramifiedConjInv _ z.val) w')
  simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, map_smul, map_inv₀]
  field_simp
  linear_combination hX

include hp hL in
/-- **Nonnegativity of the extracted coefficient at self-dual points.** In the situation of
`continuedOperator_adjoint`, let `sV` and `sW` be nonnegative on the diagonal, `v` a vector with
`sV v v ≠ 0` and `z` a common regular point with `z† = z`. Then the coefficient of
`q.continuedOperator ∘ p.continuedOperator` extracted by `v` and `(sV v v)⁻¹ sV v` is regular at
`z` with a nonnegative real value. -/
theorem continuedCompositeRationalScalar_nonnegAt
    (sV : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (sW : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ)
    (hsV : ∀ u : V, ∃ r : ℝ, 0 ≤ r ∧ sV u u = (r : ℂ))
    (hsW : ∀ u : W, ∃ r : ℝ, 0 ≤ r ∧ sW u u = (r : ℂ))
    (p : RationalOperatorContinuationData Ω A) (q : RationalOperatorContinuationData Λ B)
    {D : Set (unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))}
    (hD : IsOpen D) (hne : D.Nonempty) (hDΩ : D ⊆ Ω)
    (hdag : ∀ w ∈ D, unramifiedConjInv _ w ∈ Λ)
    (hadj : ∀ (w) (hw : w ∈ D) (v : V) (w' : W),
      sW (A ⟨w, hDΩ hw⟩ v) w' = sV v (B ⟨unramifiedConjInv _ w, hdag w hw⟩ w'))
    (hΩ : Ω.Nonempty) (hΛ : Λ.Nonempty) (v : V) (hv : sV v v ≠ 0)
    (f : rationalUnramifiedFunctionField L hp hL)
    (hf : f = continuedCompositeRationalScalar L hp hL p q hΩ hΛ v ((sV v v)⁻¹ • sV v))
    (z : unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))
    (hz : z ∈ p.regularRegion ∩ q.regularRegion) (hzdag : unramifiedConjInv _ z = z) :
    RationalFunctionNonnegAt L hp hL f z := by
  obtain ⟨a, b, -, hbreg, hab, hval⟩ :=
    continuedCompositeRationalScalar_spec L hp hL p q hΩ hΛ v ((sV v v)⁻¹ • sV v)
  refine ⟨a, b, hbreg ⟨z, hz⟩, hf.trans hab, ?_⟩
  have hz' : unramifiedConjInv _ (⟨z, hz.1⟩ : p.regularRegion).val ∈ q.regularRegion := by
    change unramifiedConjInv _ z ∈ q.regularRegion
    rw [hzdag]
    exact hz.2
  have hadjz := continuedOperator_adjoint L hp hL sV sW p q hD hne hDΩ hdag hadj
    ⟨z, hz.1⟩ hz' v (p.continuedOperator ⟨z, hz.1⟩ v)
  have hcongr : q.continuedOperator ⟨unramifiedConjInv _ z, hz'⟩ =
      q.continuedOperator ⟨z, hz.2⟩ := continuedOperator_congr L q hz' hz.2 hzdag
  rw [hcongr] at hadjz
  obtain ⟨r1, hr1, he1⟩ := hsV v
  obtain ⟨r2, hr2, he2⟩ := hsW (p.continuedOperator ⟨z, hz.1⟩ v)
  have hr1' : r1 ≠ 0 := by
    rintro rfl
    exact hv (he1.trans (by simp))
  refine ⟨r1⁻¹ * r2, mul_nonneg (inv_nonneg.mpr hr1) hr2, ?_⟩
  rw [← hval ⟨z, hz⟩]
  change (sV v v)⁻¹ * sV v (q.continuedOperator ⟨z, hz.2⟩
    (p.continuedOperator ⟨z, hz.1⟩ v)) = _
  rw [← hadjz, he1, he2]
  push_cast
  rfl

end ContinuedAdjoint

/-! ### The target and its reduction to the Hermitian adjunction -/

open Aubert.General UnramifiedOperatorFamily
open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicOppositeCanonicalScalar.centralizerClosedImmersion
  DynamicOppositeCanonicalScalar.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup2
  hermitianAdjunctionPointMeasurable
  hermitianAdjunctionPointBorel

/-- **Target (nonnegativity of `j_P` at unitary points).** Let `χ` be a cocharacter of `G`,
`P = P_G(χ)`, `P̄ = P_G(χ⁻¹)` and `M = Z_G(χ)`. Let `K` be a compact open subgroup with
`G = P K = P̄ K` whose intersections with `P` and `P̄` factor through `M`, and let `A` be a
unitarizable smooth representation of `M(F)`. Take the conditional data of the canonical scalar
`j_P` of `J_{P|P̄} J_{P̄|P}`, and assume that `z ↦ z† = z̄⁻¹` maps the open set `DForward` of
the data, inside the full convergence domain of `J_{P̄|P}`, into the full convergence domain of
`J_{P|P̄}`. Then at every unitary unramified character `z` where both
continuations are regular, `j_P` is regular with a nonnegative real value. -/
def ConditionalDynamicOppositeUnitaryNonnegStatement : Prop :=
  ∀ {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (hRefl : RelativeRootReflectionExistenceStatement.{u})
    (hCST : CentralSplitTorusCharacterStatement.{u}) (hG : IsConnectedReductive G)
    (K : OpenSubgroup (RationalPoint F G.X))
    (hK : IsCompact (K : Set (RationalPoint F G.X)))
    (hPK : ∀ g : RationalPoint F G.X,
      ∃ p : parabolic χ, ∃ k : K, g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (hOppK : ∀ g : RationalPoint F G.X,
      ∃ p : oppositeParabolic χ, ∃ k : K,
        g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
    (_hKsplit : ∀ p : parabolic χ, (p : RationalPoint F G.X) ∈ K →
      ((decomposition χ).projection p : RationalPoint F G.X) ∈ K)
    (_hOppKsplit : ∀ p : oppositeParabolic χ, (p : RationalPoint F G.X) ∈ K →
      ((oppositeDecomposition χ).projection p : RationalPoint F G.X) ∈ K)
    (A : SmoothRep.{0, u, uV} ℂ (levi χ)) (_hA : IsUnitarizable A.representation)
    (p : ForwardContinuation χ hRefl hCST hG K hK hPK hOppK A)
    (q : ReverseContinuation χ hRefl hCST hG K hK hPK hOppK A)
    {DForward DReverse : Set (unramifiedCharacters (normCharacters χ))}
    (_hDForward : IsOpen DForward) (hneForward : DForward.Nonempty)
    (hDForwardΩ : DForward ⊆ forwardFullDomainRegion χ K hK A)
    (_hDReverse : IsOpen DReverse) (hneReverse : DReverse.Nonempty)
    (hDReverseΩ : DReverse ⊆ reverseFullDomainRegion χ K hK A)
    {D : Set (unramifiedCharacters (normCharacters χ))}
    (_hD : IsOpen D) (hne : D.Nonempty)
    (hi : ∀ z ∈ D,
      (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
        (leviNormCharacters χ) (parameterTransport χ z) A).IsIrreducible)
    (_hdag : ∀ z ∈ DForward,
      unramifiedConjInv (normCharacters χ) z ∈ reverseFullDomainRegion χ K hK A)
    (z : unramifiedCharacters (normCharacters χ)),
    z ∈ p.regularRegion ∩ q.regularRegion →
    z.val ∈ unitaryUnramifiedCharacters (normCharacters χ) →
      RationalFunctionNonnegAt (parameterScheme χ) (parameterProjection_continuous χ)
        (parameterScheme_isConnectedReductive χ hG)
        (conditionalCanonicalRationalScalar χ hRefl hCST hG K hK hPK hOppK A
          p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hi) z

/-- **Reduction.** The Hermitian adjunction of IV.1 (11) on the convergence domains implies the
nonnegativity of `j_P` at unitary common regular points. -/
theorem conditionalDynamicOppositeUnitaryNonneg_of_hermitianAdjunction
    (H : ConditionalDynamicOppositeHermitianAdjunctionStatement.{u, uV}) :
    ConditionalDynamicOppositeUnitaryNonnegStatement.{u, uV} := by
  intro F _ _ _ _ G _ _ χ hRefl hCST hG K hK hPK hOppK hKsplit hOppKsplit A hA p q
    DForward DReverse hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ
    D hD hne hi hdag z hz hzu
  exact hA.elim fun b =>
    (exists_normalized_compactCoefficient (χ := χ) (hG := hG) (K := K) (hK := hK)
      (hPK := hPK) (A := A) (hne := hne) (hi := hi)).elim fun v hv =>
    hv.elim fun ℓ0 hℓ0 =>
    have hv0 : v ≠ 0 := fun h0 => by
      rw [h0, map_zero] at hℓ0
      exact zero_ne_one hℓ0
    continuedCompositeRationalScalar_nonnegAt (parameterScheme χ)
      (parameterProjection_continuous χ) (parameterScheme_isConnectedReductive χ hG)
      (compactPictureSesq (decomposition χ) K hK A b)
      (compactPictureSesq (oppositeDecomposition χ) K hK A b)
      (compactPictureHermitianPairing_self (decomposition χ) K hK A b)
      (compactPictureHermitianPairing_self (oppositeDecomposition χ) K hK A b)
      p q hDForward hneForward hDForwardΩ
      hdag
      (fun w hw φ φ' => H χ hRefl hCST hG K hK hPK hOppK hKsplit hOppKsplit A b
        ⟨w, hDForwardΩ hw⟩ (hdag w hw) φ φ')
      (hneForward.mono hDForwardΩ) (hneReverse.mono hDReverseΩ) v
      (compactPictureHermitianPairing_self_ne_zero (decomposition χ) K hK A b hv0)
      _
      (conditionalCanonicalRationalScalar_eq_extraction χ hRefl hCST hG K hK hPK hOppK A
        p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hi v
        ((compactPictureSesq (decomposition χ) K hK A b v v)⁻¹ •
          compactPictureSesq (decomposition χ) K hK A b v)
        (inv_mul_cancel₀
          (compactPictureHermitianPairing_self_ne_zero (decomposition χ) K hK A b hv0)))
      z hz (unramifiedConjInv_eq_self_of_mem_unitary _ hzu)

end Langlands.Plancherel
