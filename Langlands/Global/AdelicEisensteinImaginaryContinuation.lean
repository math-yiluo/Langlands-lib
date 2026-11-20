import Langlands.Global.AdelicSpectralTransformInputs
import Langlands.Global.AdelicEisensteinContinuationStatement
import Langlands.Global.AdelicEisensteinImaginaryHolomorphyStatement
import Langlands.Global.AdelicEisensteinConvergenceStatement
import Langlands.Global.AdelicRepresentationHeightPropernessProof
import Langlands.Analysis.Meromorphic.CoordinateGluing
import Langlands.GroupScheme.Rational.ParabolicCharacterLattice

/-! # Eisenstein continuations holomorphic on the imaginary axis

The meromorphic continuation of Eisenstein series (`EisensteinMeromorphicContinuationStatement`;
Bernstein–Lapid, Theorem 2.3 (1)), their holomorphy on the imaginary axis
(`EisensteinImaginaryAxisHolomorphyStatement`; Lapid 2011, Proposition 6) and their absolute
convergence (`EisensteinAbsoluteConvergenceStatement`; Mœglin–Waldspurger II.1.5) imply
`EisensteinImaginaryContinuationStatement`: finitely many forms `φ ∈ A^2_P` have Eisenstein
series continuations with one domain of holomorphy containing `i(X^*(P) ⊗ ℝ)`, which agree with
the Eisenstein series for `Re λ` sufficiently regular. -/

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct Manifold

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

section Evaluation

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] {N d : ℕ} {rho : MatrixRepresentation G (Fin N)}
  {hsmooth : SmoothOfRelativeDimension d G.X.hom} {hcalc : AdelicDifferentialCommutator F G hsmooth}
  {hN : 0 < N} {hrho : IsClosedSubgroup rho} {R : ℝ} {L : Subgroup (FiniteAdelicGroupPoints F G)}

/-- Evaluation at a point `g ∈ G(𝔸)` is a continuous linear form on the Fréchet space `𝔉^R_L`
of uniform moderate growth: it is the evaluation at `g` of the weighted derivative of order
zero, times `‖g‖^R`. -/
def uniformGrowthEvalCLM (g : AdelicGroupPoints F G) :
    UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L →L[ℂ] ℂ where
  toFun f := UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L f g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by
    have hpos : 0 < RepresentationGrowth.adelicSourceNorm F G rho g ^ R :=
      Real.rpow_pos_of_pos (RepresentationGrowth.adelicSourceNorm_pos F G rho hN g) R
    have h : (fun f : UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L =>
        UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L f g) =
        fun f => lp.evalCLM ℂ (fun _ : AdelicGroupPoints F G => ℂ) ⊤ g
          (weightedDerivative F G rho hsmooth hcalc hN hrho R L 1 f) *
          ((RepresentationGrowth.adelicSourceNorm F G rho g ^ R : ℝ) : ℂ) := by
      funext f
      change _ = evaluate F G (adelicEnvelopingAction F G hsmooth hcalc 1
        (f : uniformGrowthLevelSubmodule F G rho hsmooth hcalc R L).val).val g *
          ((RepresentationGrowth.adelicSourceNorm F G rho g ^ R : ℝ) : ℂ)⁻¹ * _
      rw [map_one, Module.End.one_apply,
        inv_mul_cancel_right₀ (by exact_mod_cast hpos.ne')]
      rfl
    rw [h]
    exact ((lp.evalCLM ℂ (fun _ : AdelicGroupPoints F G => ℂ) ⊤ g).continuous.comp
      (continuous_iInf_dom (i := (1 : AdelicEnvelopingAlgebra F G hsmooth))
        continuous_induced_dom)).mul continuous_const

end Evaluation

section Parameters

variable {F : Type} [Field F] [NumberField F]
  {G P M : GroupScheme (Spec (CommRingCat.of F))} {A : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine P.X.left]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}

omit [NumberField F] [IsAffineHom G.X.hom] [IsAffine P.X.left] in
/-- Imaginary parameters have real part zero. -/
theorem parameterRealPart_imaginaryParameter (x : RealCharacterParameter F P) :
    parameterRealPart F P (imaginaryParameter F P x) = 0 := by
  induction x using TensorProduct.inductionOn with
  | tmul s χ =>
    simp [imaginaryParameter, AlgebraTensorModule.map_tmul, parameterRealPart_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

omit [NumberField F] in
/-- The complex parameter space `X^*(P) ⊗ ℂ` of a presented parabolic of a connected reductive
group is finite-dimensional. -/
theorem finiteDimensional_complexCharacterParameter (r : ParabolicRootPresentation p l a)
    (hG : IsConnectedReductive G) :
    FiniteDimensional ℂ (ComplexCharacterParameter F P) := by
  have := (r.rationalCharacters_free_finite hG).2
  exact Module.Finite.base_change ℤ ℂ _

variable (r : ParabolicRootPresentation p l a)
  [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
  [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
  (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)

omit [NumberField F] [IsAffine P.X.left] in
/-- `R'`-regularity implies `R`-regularity for `R ≤ R'`. -/
theorem isRegularParameter_mono {R R' : ℝ} (hRR' : R ≤ R') {lam : ComplexCharacterParameter F P}
    (h : r.IsRegularParameter hA hT R' lam) : r.IsRegularParameter hA hT R lam :=
  fun α hα => hRR'.trans_lt (h α hα)

omit [NumberField F] [IsAffine P.X.left] in
/-- In linear coordinates, the parameters with `B(Re λ|_A, α) < R` form an open set. -/
theorem isOpen_preimage_regularityForm_lt (α : characterLattice A) (R : ℝ) {n : ℕ}
    (e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P) :
    IsOpen (e ⁻¹' {lam | Langlands.Plancherel.weylInducedCharacterForm hA hT r.data.f r.data.i
      (realParameterRestriction (a ≫ l) (parameterRealPart F P lam)) ((1 : ℝ) ⊗ₜ[ℤ] α) < R}) := by
  let ℓ : (Fin n → ℂ) →ₗ[ℝ] ℝ :=
    ((Langlands.Plancherel.weylInducedCharacterForm hA hT r.data.f r.data.i).flip
      ((1 : ℝ) ⊗ₜ[ℤ] α)) ∘ₗ (realParameterRestriction (a ≫ l)) ∘ₗ (parameterRealPart F P) ∘ₗ
        (e.toLinearMap.restrictScalars ℝ)
  have h : e ⁻¹' {lam | Langlands.Plancherel.weylInducedCharacterForm hA hT r.data.f r.data.i
      (realParameterRestriction (a ≫ l) (parameterRealPart F P lam)) ((1 : ℝ) ⊗ₜ[ℤ] α) < R} =
      {s | ℓ s < R} := rfl
  rw [h]
  exact isOpen_lt ℓ.continuous_of_finiteDimensional continuous_const

end Parameters

section Series

variable {F : Type} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [IsAffine P.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left]
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)

omit [IsAffineHom G.X.hom] [IsAffine G.X.left] [IsAffine P.X.left]
  [IsClosedImmersion p.hom.hom.left] in
/-- Each term `φ(γ g) exp ⟨λ, H_P(γ g)⟩` of the Eisenstein series is entire in linear coordinates
of `λ`. -/
theorem differentiable_eisensteinTerm (φ : AdelicGroupPoints F G → ℂ) {n : ℕ}
    (e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P) (g : AdelicGroupPoints F G)
    (c : ParabolicRationalCosets F p) :
    Differentiable ℂ fun s => hK.eisensteinTerm φ (e s) g c := by
  let H := hK.height (((Quotient.out c : rationalSubgroup F G) : AdelicGroupPoints F G) * g)
  let ℓ : (Fin n → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun s => complexParameterPairing F P (e s) H
      map_add' := fun s t => by simp only [map_add, LinearMap.add_apply]
      map_smul' := fun z s => by
        simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply] }
  have h : (fun s => hK.eisensteinTerm φ (e s) g c) = fun s =>
      φ (((Quotient.out c : rationalSubgroup F G) : AdelicGroupPoints F G) * g) *
        Complex.exp (LinearMap.toContinuousLinearMap ℓ s) := rfl
  rw [h]
  exact (differentiable_const _).mul (LinearMap.toContinuousLinearMap ℓ).differentiable.cexp

omit [IsAffineHom G.X.hom] [IsAffine G.X.left] [IsAffine P.X.left]
  [IsClosedImmersion p.hom.hom.left] in
/-- If `G(𝔸)` is trivial, the Eisenstein series has a single term, so it is entire in linear
coordinates. -/
theorem differentiable_eisensteinSeries_of_subsingleton [Subsingleton (AdelicGroupPoints F G)]
    (φ : AdelicGroupPoints F G → ℂ) {n : ℕ} (e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P)
    (g : AdelicGroupPoints F G) :
    Differentiable ℂ fun s => hK.eisensteinSeries φ (e s) g := by
  have hsub : ∀ c c' : ParabolicRationalCosets F p, c = c' := fun c c' =>
    Quotient.inductionOn₂ c c' fun x y => congrArg _ (Subtype.ext (Subsingleton.elim _ _))
  have h : (fun s => hK.eisensteinSeries φ (e s) g) =
      fun s => hK.eisensteinTerm φ (e s) g (Quotient.mk _ 1) := by
    funext s
    exact tsum_eq_single _ fun c hc => absurd (hsub c _) hc
  rw [h]
  exact differentiable_eisensteinTerm hK φ e g _

end Series

/-- A closed subgroup of `GL_0` has trivial adelic points. -/
theorem subsingleton_adelicGroupPoints_of_rank_zero {F : Type} [Field F] [NumberField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
    (rho : MatrixRepresentation G (Fin 0)) (hrho : IsClosedSubgroup rho) :
    Subsingleton (AdelicGroupPoints F G) :=
  ⟨fun _ _ => (RepresentationGrowth.isClosedEmbedding_adelicMatrix F G rho hrho).injective
    (Units.ext (Matrix.ext fun i => Fin.elim0 i))⟩

section PerForm

variable {F : Type} [Field F] [NumberField F]
  {G P M U : GroupScheme (Spec (CommRingCat.of F))}
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {iU : U ⟶ P} {l : M ⟶ P}
  {a : A.toGrp ⟶ M} (r : ParabolicRootPresentation p l a)
  [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
  [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
  (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)

omit [LocallyOfFiniteType G.X.hom] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] in
/-- Gluing the local Fréchet-valued continuations of `EisensteinMeromorphicContinuationStatement`:
for `N > 0`, the Eisenstein series of an automorphic form on `P(F) U(𝔸) \ G(𝔸)` has a
continuation `E'` such that every `λ ↦ E'(λ)(g)` is meromorphic in coordinates with one domain
of holomorphy `D₀` independent of `g`. -/
theorem exists_glued_eisensteinContinuation
    (hMero : EisensteinMeromorphicContinuationStatement.{0}) (hG : IsConnectedReductive G)
    (hUR : LeviSubgroup.IsGeometricUnipotentRadical iU) {N d : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N) (hrho : IsClosedSubgroup rho)
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) (hKmax : IsMaximalCompactSubgroup F G K)
    (φ : AdelicGroupPoints F G → ℂ)
    (hφ : IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
      (K.comap (ofInfinite F G).toMonoidHom) rho φ) :
    ∃ (E' : ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ)
      (D₀ : Set (ComplexCharacterParameter F P)) (R₀ : ℝ),
      (∀ lam, r.IsRegularParameter hA hT R₀ lam → E' lam = hK.eisensteinSeries φ lam) ∧
      ∀ g, IsMeromorphicInCoordinatesOn (fun lam => E' lam g) D₀ := by
  have := finiteDimensional_complexCharacterParameter r hG
  obtain ⟨E', ⟨R₀, hR₀⟩, hloc⟩ :=
    hMero F G P M U A p iU l a r hA hT hG hUR K hK rho hN hrho hsmooth hcalc φ hKmax hφ
  let m := Module.finrank ℂ (ComplexCharacterParameter F P)
  let e₀ : (Fin m → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P :=
    (Module.finBasis ℂ (ComplexCharacterParameter F P)).equivFun.symm
  have hdata : ∀ s₀ : Fin m → ℂ,
      HasLocalMeromorphicData (fun (g : AdelicGroupPoints F G) s => E' (e₀ s) g) s₀ := by
    intro s₀
    obtain ⟨W, hs₀, R, L, -, f, D, hf, hfD⟩ := hloc m e₀ s₀
    refine hasLocalMeromorphicData_of_isMeromorphicOn hf (fun g => uniformGrowthEvalCLM g)
      (fun t ht g => ?_) hs₀
    change UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L (f t) g = _
    rw [(hfD t ht).1]
  obtain ⟨U₀, hU₀⟩ := exists_isMeromorphicOn_of_local hdata
  refine ⟨E', e₀ '' U₀, R₀, hR₀, fun g => isMeromorphicInCoordinatesOn_of_coordinates e₀ ?_⟩
  rw [e₀.injective.preimage_image]
  exact hU₀ g

omit [LocallyOfFiniteType G.X.hom] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] in
include hA hT in
/-- If no root of `A` occurs in the unipotent radical, the Eisenstein series converges at every
parameter, locally uniformly (`EisensteinAbsoluteConvergenceStatement`), so it is continuous in
linear coordinates. -/
theorem continuous_eisensteinSeries_of_unipotentRoots_eq_empty
    (hConv : EisensteinAbsoluteConvergenceStatement.{0}) (hroots : r.unipotentRoots = ∅)
    (hG : IsConnectedReductive G) (hUR : LeviSubgroup.IsGeometricUnipotentRadical iU) {N d : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) (hKmax : IsMaximalCompactSubgroup F G K)
    (hrho : IsClosedSubgroup rho) (φ : AdelicGroupPoints F G → ℂ)
    (hφ : IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
      (K.comap (ofInfinite F G).toMonoidHom) rho φ) {n : ℕ}
    (e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P) (g : AdelicGroupPoints F G) :
    Continuous fun s => hK.eisensteinSeries φ (e s) g := by
  obtain ⟨R, hR⟩ := hConv F G P M U A p iU l a r hA hT hG hUR K hK rho hsmooth hcalc φ hKmax hrho hφ
  refine continuous_iff_continuousAt.2 fun s₀ => ?_
  obtain ⟨b, hb, hbd⟩ := hR {g} isCompact_singleton n e (Metric.closedBall s₀ 1)
    (isCompact_closedBall s₀ 1) fun s _ α hα => by simp [hroots] at hα
  have hc : ContinuousOn (fun s => ∑' c, hK.eisensteinTerm φ (e s) g c) (Metric.closedBall s₀ 1) :=
    continuousOn_tsum (fun c => (differentiable_eisensteinTerm hK φ e g c).continuous.continuousOn)
      hb fun c s hs => hbd c g (Set.mem_singleton g) s hs
  exact hc.continuousAt (Metric.closedBall_mem_nhds s₀ one_pos)

variable [LocallyOfFiniteType P.X.hom]

/-- One form: the Eisenstein series of `φ ∈ A^2_P` has a continuation with a domain of
holomorphy containing `i(X^*(P) ⊗ ℝ)`, equal to the Eisenstein series for `Re λ` sufficiently
regular. -/
theorem exists_imaginary_eisensteinContinuation
    (hMero : EisensteinMeromorphicContinuationStatement.{0})
    (hHolo : EisensteinImaginaryAxisHolomorphyStatement)
    (hConv : EisensteinAbsoluteConvergenceStatement.{0})
    (hG : IsConnectedReductive G) (hUR : LeviSubgroup.IsGeometricUnipotentRadical iU) {N d : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) (hKmax : IsMaximalCompactSubgroup F G K)
    (hrho : IsClosedSubgroup rho) (φ : AdelicGroupPoints F G → ℂ)
    (hφ : IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l φ) :
    ∃ (E : ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ)
      (D : Set (ComplexCharacterParameter F P)),
      Set.range (imaginaryParameter F P) ⊆ D ∧
      (∀ g, IsMeromorphicInCoordinatesOn (fun lam => E lam g) D) ∧
      ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → E lam = hK.eisensteinSeries φ lam := by
  classical
  have := finiteDimensional_complexCharacterParameter r hG
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · -- `N = 0`: `G(𝔸)` is trivial and the Eisenstein series is entire
    have := subsingleton_adelicGroupPoints_of_rank_zero rho hrho
    exact ⟨hK.eisensteinSeries φ, Set.univ, Set.subset_univ _, fun g =>
      isMeromorphicInCoordinatesOn_univ fun n e =>
        differentiable_eisensteinSeries_of_subsingleton hK φ e g, 0, fun _ _ => rfl⟩
  obtain ⟨E', D₀, R₀, hE'reg, hE'⟩ :=
    exists_glued_eisensteinContinuation r hA hT hK hMero hG hUR rho hN hrho hsmooth hcalc hKmax φ
      hφ.1
  obtain ⟨E'', D', himag, hE'', hE''eq⟩ :=
    hHolo F G P M U A p iU l a r hA hT hG hUR K hK rho hsmooth hcalc φ hKmax hrho hφ E' D₀ hE'
      ⟨R₀, hE'reg⟩
  rcases Set.eq_empty_or_nonempty r.unipotentRoots with hroots | ⟨α₀, hα₀⟩
  · -- no roots in the unipotent radical: every parameter is regular, and the series is
    -- continuous, so it agrees with `E''` on all of `D'`
    have hreg : ∀ R lam, r.IsRegularParameter hA hT R lam := fun R lam α hα => by
      simp [hroots] at hα
    refine ⟨hK.eisensteinSeries φ, D', himag, fun g => ?_, 0, fun _ _ => rfl⟩
    refine (hE'' g).congr_mono (hE'' g).isOpenDenseInCoordinates subset_rfl ?_
    let m := Module.finrank ℂ (ComplexCharacterParameter F P)
    let e₀ : (Fin m → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P :=
      (Module.finBasis ℂ (ComplexCharacterParameter F P)).equivFun.symm
    have hcont := continuous_eisensteinSeries_of_unipotentRoots_eq_empty r hA hT hK hConv hroots
      hG hUR rho hsmooth hcalc hKmax hrho φ hφ.1 e₀ g
    have hD'o : IsOpen (e₀ ⁻¹' D') := ((hE'' g).2 m e₀).1
    have hD₀d : Dense (e₀ ⁻¹' D₀) := ((hE' g).2 m e₀).2.1
    have hE''c : ContinuousOn (fun s => E'' (e₀ s) g) (e₀ ⁻¹' D') :=
      (differentiableOn_of_isHolomorphicOn ((hE'' g).2 m e₀).2.2.1).continuousOn
    have heq : Set.EqOn (fun s => hK.eisensteinSeries φ (e₀ s) g) (fun s => E'' (e₀ s) g)
        (e₀ ⁻¹' D' ∩ e₀ ⁻¹' D₀) := fun s hs => by
      simp only
      rw [hE''eq _ ⟨hs.2, hs.1⟩, hE'reg _ (hreg _ _)]
    have hall := Set.EqOn.of_subset_closure heq hcont.continuousOn hE''c Set.inter_subset_left
      (hD₀d.open_subset_closure_inter hD'o)
    intro lam hlam
    have := hall (show e₀.symm lam ∈ e₀ ⁻¹' D' by simpa using hlam)
    simpa using this
  · -- a root `α₀`: use the Eisenstein series where `λ` is `R₁`-regular and `E''` elsewhere
    set R₁ : ℝ := max R₀ 0 + 1 with hR₁
    have hR₀₁ : R₀ ≤ R₁ := by have := le_max_left R₀ 0; linarith
    have hR₁pos : 0 < R₁ := by have := le_max_right R₀ 0; linarith
    let O : Set (ComplexCharacterParameter F P) :=
      {lam | Langlands.Plancherel.weylInducedCharacterForm hA hT r.data.f r.data.i
        (realParameterRestriction (a ≫ l) (parameterRealPart F P lam)) ((1 : ℝ) ⊗ₜ[ℤ] α₀) < R₁}
    refine ⟨fun lam => if r.IsRegularParameter hA hT R₁ lam then hK.eisensteinSeries φ lam
      else E'' lam, D' ∩ (D₀ ∪ O), ?_, fun g => ?_, R₁, fun lam hlam => ite_eq_left hlam⟩
    · rintro _ ⟨x, rfl⟩
      refine ⟨himag ⟨x, rfl⟩, Or.inr ?_⟩
      show Langlands.Plancherel.weylInducedCharacterForm hA hT r.data.f r.data.i
        (realParameterRestriction (a ≫ l) (parameterRealPart F P (imaginaryParameter F P x)))
          ((1 : ℝ) ⊗ₜ[ℤ] α₀) < R₁
      rw [parameterRealPart_imaginaryParameter, map_zero, map_zero, LinearMap.zero_apply]
      exact hR₁pos
    · refine (hE'' g).congr_mono ((hE'' g).isOpenDenseInCoordinates.inter
        ((hE' g).isOpenDenseInCoordinates.union_isOpen fun n e =>
          isOpen_preimage_regularityForm_lt r hA hT α₀ R₁ e)) Set.inter_subset_left ?_
      rintro lam ⟨hD', hlam⟩
      by_cases hreg : r.IsRegularParameter hA hT R₁ lam
      · have hD₀ : lam ∈ D₀ := hlam.resolve_right fun hO => lt_asymm (hreg α₀ hα₀) hO
        simp only [ite_eq_left hreg]
        rw [hE''eq lam ⟨hD₀, hD'⟩, hE'reg lam (isRegularParameter_mono r hA hT hR₀₁ hreg)]
      · simp only [ite_eq_right hreg]

end PerForm

/-- The meromorphic continuation of Eisenstein series, their holomorphy on the imaginary axis
and their absolute convergence imply `EisensteinImaginaryContinuationStatement`. -/
def EisensteinImaginaryContinuationBridgeStatement : Prop :=
  EisensteinMeromorphicContinuationStatement.{0} → EisensteinImaginaryAxisHolomorphyStatement →
    EisensteinAbsoluteConvergenceStatement.{0} → EisensteinImaginaryContinuationStatement

theorem eisensteinImaginaryContinuationBridge : EisensteinImaginaryContinuationBridgeStatement := by
  intro hMero hHolo hConv F _ _ G P M U A _ _ _ _ _ _ p _ iU l a r _ _ _ hA hT hG hUR K hK N d rho
    hsmooth hcalc hKmax hrho k v hv
  have : LocallyOfFiniteType P.X.hom :=
    IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
  have hj := fun j => exists_imaginary_eisensteinContinuation r hA hT hK hMero hHolo hConv hG hUR
    rho hsmooth hcalc hKmax hrho (v j) (hv j)
  choose E D himag hmero hreg using hj
  refine ⟨E, ⋂ j, D j, Set.subset_iInter himag, fun j g => (hmero j g).congr_mono
    (isOpenDenseInCoordinates_iInter fun j' => (hmero j' 1).isOpenDenseInCoordinates)
    (Set.iInter_subset _ j) fun _ _ => rfl, hreg⟩

end Langlands.Global
