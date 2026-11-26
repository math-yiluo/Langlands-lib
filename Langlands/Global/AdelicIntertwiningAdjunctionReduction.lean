import Langlands.Global.AdelicIntertwiningAdjunctionStatement
import Langlands.Global.AdelicIntertwiningImaginaryIsometryReduction
import Langlands.Global.AdelicRootHyperplaneReduction
import Langlands.Global.AdelicEisensteinRegularRegion
import Langlands.Global.AdelicIntertwiningIdentity
import Langlands.Global.AdelicWeylSetAssociation
import Langlands.Analysis.Meromorphic.IdentityTheorem

/-! # Reduction of the adjunction of continued intertwining operators

Mœglin–Waldspurger II.1.8 and IV.1.9 (e): the adjunction
`(M(w, λ)φ, φ')_{P'} = (φ, M(w⁻¹, -wλ̄)φ')_P` of the intertwining integrals for `Re λ` in a
region of convergence, together with the agreement of the continued expansion of an intertwining
operator with its integral on the region where `-wλ` is regular, implies
`IntertwiningContinuedAdjunctionStatement`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct Set Filter
open scoped CategoryTheory.MonObj TensorProduct Topology Manifold

set_option autoImplicit false

/-! ## Conjugation `s ↦ -s̄` and meromorphic functions -/

namespace Langlands.Analysis.Meromorphic

/-- If `f` is complex differentiable at `-s̄`, then `s ↦ conj (f (-s̄))` is complex differentiable
at `s`. -/
theorem differentiableAt_conj_comp_negConj {n : ℕ} {f : (Fin n → ℂ) → ℂ} {s : Fin n → ℂ}
    (hf : DifferentiableAt ℂ f (negConjHomeomorph n s)) :
    DifferentiableAt ℂ (fun s => (starRingEnd ℂ) (f (negConjHomeomorph n s))) s := by
  obtain ⟨L, hL⟩ := hf
  let Cₗ : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) :=
    { toFun := fun v t => -(starRingEnd ℂ) (v t)
      map_add' := fun u v => by
        funext t
        simp only [Pi.add_apply, map_add, neg_add]
      map_smul' := fun c v => by
        funext t
        simp only [Pi.smul_apply, RingHom.id_apply, Complex.real_smul, map_mul,
          Complex.conj_ofReal, mul_neg] }
  let C : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) := LinearMap.toContinuousLinearMap Cₗ
  have hCapp : ∀ v, C v = negConjHomeomorph n v := fun v => rfl
  have hρ : HasFDerivAt (fun s => negConjHomeomorph n s) C s := by
    have h : (fun s => negConjHomeomorph n s) = C := funext fun v => (hCapp v).symm
    rw [h]
    exact C.hasFDerivAt
  have h1 : HasFDerivAt (fun s => f (negConjHomeomorph n s)) ((L.restrictScalars ℝ).comp C) s :=
    (hL.restrictScalars ℝ).comp s hρ
  have h2 : HasFDerivAt (fun s => (starRingEnd ℂ) (f (negConjHomeomorph n s)))
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp ((L.restrictScalars ℝ).comp C)) s :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp s h1
  have hCsmul : ∀ (z : ℂ) (v : Fin n → ℂ), C (z • v) = (starRingEnd ℂ) z • C v := by
    intro z v
    funext t
    simp only [hCapp, negConjHomeomorph_apply, Pi.smul_apply, smul_eq_mul, map_mul, mul_neg]
  let L'ₗ : (Fin n → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun v => (starRingEnd ℂ) (L (C v))
      map_add' := fun u v => by simp only [map_add]
      map_smul' := fun z v => by
        simp only [hCsmul, map_smul, smul_eq_mul, map_mul, Complex.conj_conj, RingHom.id_apply] }
  refine ⟨LinearMap.toContinuousLinearMap L'ₗ, hasFDerivAt_of_restrictScalars ℝ h2 ?_⟩
  ext v
  rfl

/-- If `f` is meromorphic on `ℂⁿ` with domain `U`, then `s ↦ conj (f (-s̄))` is meromorphic with
domain the preimage of `U` under `s ↦ -s̄`. -/
theorem IsMeromorphicOn.conj_comp_negConj {n : ℕ} {f : (Fin n → ℂ) → ℂ} {U : Set (Fin n → ℂ)}
    (hf : IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) f U) :
    IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) (fun s => (starRingEnd ℂ) (f (negConjHomeomorph n s)))
      (negConjHomeomorph n ⁻¹' U) := by
  set ρ := negConjHomeomorph n with hρdef
  have hρρ : ∀ s, ρ (ρ s) = s := fun s => by
    funext t
    simp [hρdef, negConjHomeomorph_apply]
  have hdiff : ∀ {g : (Fin n → ℂ) → ℂ} {W : Set (Fin n → ℂ)}, IsOpen W →
      DifferentiableOn ℂ g W →
        DifferentiableOn ℂ (fun s => (starRingEnd ℂ) (g (ρ s))) (ρ ⁻¹' W) := by
    intro g W hWo hg s hs
    exact (differentiableAt_conj_comp_negConj
      ((hg (ρ s) hs).differentiableAt (hWo.mem_nhds hs))).differentiableWithinAt
  rw [isMeromorphicOn_iff] at hf ⊢
  obtain ⟨hUo, hUd, hfd, hloc⟩ := hf
  refine ⟨hUo.preimage ρ.continuous, hUd.preimage ρ.isOpenMap, hdiff hUo hfd, fun s₀ => ?_⟩
  obtain ⟨W, hWo, hWc, hs₀, g, h, hg, ⟨s₁, hs₁W, hs₁⟩, hh, he⟩ := hloc (ρ s₀)
  refine ⟨ρ ⁻¹' W, hWo.preimage ρ.continuous, ρ.isConnected_preimage.2 hWc, hs₀,
    fun s => (starRingEnd ℂ) (g (ρ s)), fun s => (starRingEnd ℂ) (h (ρ s)), hdiff hWo hg,
    ⟨ρ s₁, by simpa [Set.mem_preimage, hρρ] using hs₁W, by simpa [hρρ] using hs₁⟩,
    hdiff hWo hh, ?_⟩
  rintro s ⟨hsU, hsW⟩
  rw [← map_mul, he (ρ s) ⟨hsU, hsW⟩]

variable {X : Type*} [AddCommGroup X] [Module ℂ X]

/-- A finite family of functions meromorphic with domain `D` is meromorphic with domain
`⋂ _ : J, D`, which is open and dense in coordinates; for empty `J` it is the whole space. -/
theorem isMeromorphicInCoordinatesOn_iInter_finite [FiniteDimensional ℂ X] {J : Type*} [Finite J]
    {D : Set X} {f : J → X → ℂ} (hf : ∀ i, IsMeromorphicInCoordinatesOn (f i) D) :
    IsOpenDenseInCoordinates (⋂ _ : J, D) ∧
      ∀ i, IsMeromorphicInCoordinatesOn (f i) (⋂ _ : J, D) := by
  rcases isEmpty_or_nonempty J with hJ | hJ
  · rw [iInter_of_empty]
    exact ⟨fun n e => by simp only [preimage_univ]; exact ⟨isOpen_univ, dense_univ⟩,
      fun i => isEmptyElim i⟩
  · rw [iInter_const]
    exact ⟨(hf hJ.some).isOpenDenseInCoordinates, hf⟩

end Langlands.Analysis.Meromorphic

/-! ## Real parts of parameters in a real chart -/

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme

variable {F : Type u} [Field F] {P : GroupScheme (Spec (CommRingCat.of F))}

/-- The real part of `z • y` for real `y` is `Re z • y`. -/
theorem parameterRealPart_smul_realToComplexParameter (z : ℂ) (y : RealCharacterParameter F P) :
    parameterRealPart F P (z • realToComplexParameter P y) = z.re • y := by
  induction y using TensorProduct.inductionOn with
  | tmul t χ =>
    rw [realToComplexParameter_tmul, TensorProduct.smul_tmul', parameterRealPart_tmul,
      TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, Complex.re_mul_ofReal]
  | add x y hx hy => rw [map_add, smul_add, map_add, hx, hy, smul_add]

/-- The real part of `realChart e z` is `e (Re z)`. -/
theorem parameterRealPart_realChart {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P)
    (z : Fin n → ℂ) : parameterRealPart F P (realChart e z) = e (fun t => (z t).re) := by
  rw [realChart_apply, map_sum]
  simp only [parameterRealPart_smul_realToComplexParameter]
  have hx : (fun t => (z t).re) = ∑ t, (z t).re • (Pi.single t 1 : Fin n → ℝ) := by
    ext t'
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hx, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [LinearEquiv.map_smul]

end Langlands.Global.AdelicGroupPoints

namespace Langlands.GroupScheme.ParabolicRootPresentation

open Langlands.Global.AdelicGroupPoints

variable {F : Type u} [Field F]
  {G P M : GroupScheme (Spec (CommRingCat.of F))} {A : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)
  [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
  [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
  (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)

/-- Regularity of a parameter depends only on its real part. -/
theorem isRegularParameter_of_parameterRealPart_eq {R : ℝ}
    {lam lam' : Langlands.Global.AdelicGroupPoints.ComplexCharacterParameter F P}
    (h : parameterRealPart F P lam = parameterRealPart F P lam')
    (hlam : r.IsRegularParameter hA hT R lam) : r.IsRegularParameter hA hT R lam' := by
  intro α hα
  have := hlam α hα
  rwa [h] at this

end Langlands.GroupScheme.ParabolicRootPresentation

/-! ## Inverse Weyl parameters -/

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme

variable {F : Type u} [Field F] {G P M P' M' : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M} {p' : P' ⟶ G} {l' : M' ⟶ P'}
  [Mono p]

/-- If `(w, cw)` presents an element of `W(P, P')` and `(w⁻¹, cw')` its inverse, then
`λ ↦ w⁻¹λ` inverts `λ ↦ wλ` on `X^*(P) ⊗ ℂ`. -/
theorem weylParameter_weylParameter_of_inv (r : ParabolicRootPresentation p l a) {π : P ⟶ M}
    {π' : P' ⟶ M'} (hπ : l ≫ π = 𝟙 M) (hπ' : l' ≫ π' = 𝟙 M')
    {w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X} {cw : M' ⟶ M} {cw' : M ⟶ M'}
    (hW : IsWeylConjugation p l p' l' w cw) (hW' : IsWeylConjugation p' l' p l w⁻¹ cw')
    (x : ComplexCharacterParameter F P) :
    weylParameter l' cw' π (weylParameter l cw π' x) = x := by
  have hinv : (G.innerIso w⁻¹).inv = (G.innerIso w).hom := by
    rw [← cancel_mono (G.innerIso w⁻¹).hom, Iso.inv_hom_id, innerIso_inv_hom, Iso.hom_inv_id]
  have hcomp : cw' ≫ cw ≫ l = l := by
    apply (cancel_mono p).mp
    simp only [Category.assoc, hW.comp_eq, reassoc_of% hW'.comp_eq, hinv, Iso.hom_inv_id,
      Category.comp_id]
  have h1 := LinearMap.congr_fun (weylParameter_comp l cw π' l' cw' π hπ') x
  rw [LinearMap.comp_apply] at h1
  rw [h1]
  have h2 : weylParameter (F := F) l (cw' ≫ cw) π = weylParameter l (𝟙 M) π := by
    apply AlgebraTensorModule.ext
    intro s χ
    simp only [weylParameter_tmul, Category.assoc, hcomp, Category.id_comp]
  rw [h2, weylParameter_one_self r π hπ, LinearMap.id_apply]

end Langlands.Global.AdelicGroupPoints

/-! ## Pairings with finite combinations -/

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

section Pairing

variable {F : Type} [Field F] [NumberField F]
  {G P M : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  (K : Subgroup (AdelicGroupPoints F G)) (hKc : IsCompact (K : Set (AdelicGroupPoints F G)))
  (p : P ⟶ G) (l : M ⟶ P) (μM : Measure (AdelicGroupPoints F M)) [μM.IsHaarMeasure] {n : ℕ}
  (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P) (β : (Fin n → ℝ) → ℝ)

omit [IsAffine G.X.left] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] in
/-- The integrand of `(φ, ψ)_P` is additive in `ψ`. -/
theorem inducedInnerProductIntegrand_add_right (φ ψ₁ ψ₂ : AdelicGroupPoints F G → ℂ) :
    AdelicGroupPoints.inducedInnerProductIntegrand K p l e β φ (fun g => ψ₁ g + ψ₂ g) =
      fun z => AdelicGroupPoints.inducedInnerProductIntegrand K p l e β φ ψ₁ z +
        AdelicGroupPoints.inducedInnerProductIntegrand K p l e β φ ψ₂ z := by
  funext z
  simp only [AdelicGroupPoints.inducedInnerProductIntegrand, map_add]
  ring

omit [IsAffine G.X.left] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] in
/-- The integrand of `(φ, ψ)_P` is conjugate-homogeneous in `ψ`. -/
theorem inducedInnerProductIntegrand_mul_right (φ ψ : AdelicGroupPoints F G → ℂ) (t : ℂ) :
    AdelicGroupPoints.inducedInnerProductIntegrand K p l e β φ (fun g => t * ψ g) =
      fun z => (starRingEnd ℂ) t *
        AdelicGroupPoints.inducedInnerProductIntegrand K p l e β φ ψ z := by
  funext z
  simp only [AdelicGroupPoints.inducedInnerProductIntegrand, map_mul]
  ring

/-- When its integrand is integrable on `K × M(F) \ M(𝔸)`, the iterated integral
`inducedInnerProduct` is the integral over the product. -/
theorem inducedInnerProduct_eq_integral_prod {φ ψ : AdelicGroupPoints F G → ℂ}
    (h : Integrable (AdelicGroupPoints.inducedInnerProductIntegrand K p l e β φ ψ)
      ((compactHaarProbability F G K hKc).prod
        (LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F M)
          (isDiscrete_rationalSubgroup F M) μM))) :
    inducedInnerProduct K hKc p l μM e β φ ψ =
      ∫ z, AdelicGroupPoints.inducedInnerProductIntegrand K p l e β φ ψ z
        ∂((compactHaarProbability F G K hKc).prod
          (LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F M)
            (isDiscrete_rationalSubgroup F M) μM)) := by
  have : SFinite (LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F M)
      (isDiscrete_rationalSubgroup F M) μM) := by
    rw [LeftCosetSpace.discreteQuotientMeasure, LeftCosetSpace.quotientMeasure]
    infer_instance
  rw [integral_prod _ h]
  rfl

omit [IsAffine G.X.left] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] in
/-- The integrand of `(φ, ∑ j, y j • h j)_P` is `∑ j, conj (y j)` times that of `(φ, h j)_P`. -/
theorem inducedInnerProductIntegrand_sum_right (φ : AdelicGroupPoints F G → ℂ) {b : ℕ}
    (h : Fin b → AdelicGroupPoints F G → ℂ) (y : Fin b → ℂ) :
    AdelicGroupPoints.inducedInnerProductIntegrand K p l e β φ (fun g => ∑ j, y j * h j g) =
      fun z => ∑ j, (starRingEnd ℂ) (y j) *
        AdelicGroupPoints.inducedInnerProductIntegrand K p l e β φ (h j) z := by
  funext z
  simp only [AdelicGroupPoints.inducedInnerProductIntegrand, map_sum, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

omit [IsAffine G.X.left] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] in
/-- The integrand of `(∑ i, x i • f i, ψ)_P` is `∑ i, x i` times that of `(f i, ψ)_P`. -/
theorem inducedInnerProductIntegrand_sum_left {b : ℕ} (f : Fin b → AdelicGroupPoints F G → ℂ)
    (x : Fin b → ℂ) (ψ : AdelicGroupPoints F G → ℂ) :
    AdelicGroupPoints.inducedInnerProductIntegrand K p l e β (fun g => ∑ i, x i * f i g) ψ =
      fun z => ∑ i, x i * AdelicGroupPoints.inducedInnerProductIntegrand K p l e β (f i) ψ z := by
  funext z
  simp only [AdelicGroupPoints.inducedInnerProductIntegrand, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `(φ, ∑ j, y j • h j)_P = ∑ j, conj (y j) (φ, h j)_P` when every integrand of `(φ, h j)_P` is
integrable. -/
theorem inducedInnerProduct_sum_right (φ : AdelicGroupPoints F G → ℂ) {b : ℕ}
    (h : Fin b → AdelicGroupPoints F G → ℂ) (y : Fin b → ℂ)
    (hint : ∀ j, Integrable (AdelicGroupPoints.inducedInnerProductIntegrand K p l e β φ (h j))
      ((compactHaarProbability F G K hKc).prod
        (LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F M)
          (isDiscrete_rationalSubgroup F M) μM))) :
    Integrable (AdelicGroupPoints.inducedInnerProductIntegrand K p l e β φ
        (fun g => ∑ j, y j * h j g))
      ((compactHaarProbability F G K hKc).prod
        (LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F M)
          (isDiscrete_rationalSubgroup F M) μM)) ∧
    inducedInnerProduct K hKc p l μM e β φ (fun g => ∑ j, y j * h j g) =
      ∑ j, (starRingEnd ℂ) (y j) * inducedInnerProduct K hKc p l μM e β φ (h j) := by
  have hterm := fun j => (hint j).const_mul ((starRingEnd ℂ) (y j))
  have hcomb : Integrable (AdelicGroupPoints.inducedInnerProductIntegrand K p l e β φ
      (fun g => ∑ j, y j * h j g))
      ((compactHaarProbability F G K hKc).prod
        (LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F M)
          (isDiscrete_rationalSubgroup F M) μM)) := by
    rw [inducedInnerProductIntegrand_sum_right]
    exact integrable_finsetSum _ fun j _ => hterm j
  refine ⟨hcomb, ?_⟩
  rw [inducedInnerProduct_eq_integral_prod K hKc p l μM e β hcomb,
    inducedInnerProductIntegrand_sum_right, integral_finsetSum _ fun j _ => hterm j]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, inducedInnerProduct_eq_integral_prod K hKc p l μM e β (hint j)]

/-- `(∑ i, x i • f i, ψ)_P = ∑ i, x i (f i, ψ)_P` when every integrand of `(f i, ψ)_P` is
integrable. -/
theorem inducedInnerProduct_sum_left {b : ℕ} (f : Fin b → AdelicGroupPoints F G → ℂ)
    (x : Fin b → ℂ) (ψ : AdelicGroupPoints F G → ℂ)
    (hint : ∀ i, Integrable (AdelicGroupPoints.inducedInnerProductIntegrand K p l e β (f i) ψ)
      ((compactHaarProbability F G K hKc).prod
        (LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F M)
          (isDiscrete_rationalSubgroup F M) μM))) :
    inducedInnerProduct K hKc p l μM e β (fun g => ∑ i, x i * f i g) ψ =
      ∑ i, x i * inducedInnerProduct K hKc p l μM e β (f i) ψ := by
  have hterm := fun i => (hint i).const_mul (x i)
  have hcomb : Integrable (AdelicGroupPoints.inducedInnerProductIntegrand K p l e β
      (fun g => ∑ i, x i * f i g) ψ)
      ((compactHaarProbability F G K hKc).prod
        (LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F M)
          (isDiscrete_rationalSubgroup F M) μM)) := by
    rw [inducedInnerProductIntegrand_sum_left]
    exact integrable_finsetSum _ fun i _ => hterm i
  rw [inducedInnerProduct_eq_integral_prod K hKc p l μM e β hcomb,
    inducedInnerProductIntegrand_sum_left, integral_finsetSum _ fun i _ => hterm i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, inducedInnerProduct_eq_integral_prod K hKc p l μM e β (hint i)]

/-- The pairing `(φ, ∑ x, a x • χ x)_P`, restricted to the coefficient vectors `a` for which its
integrand is integrable, is the restriction of a conjugate-linear form on `ℂ^{k'}`. -/
theorem exists_inducedInnerProduct_sum_right_eq (φ : AdelicGroupPoints F G → ℂ) {k' : ℕ}
    (χ : Fin k' → AdelicGroupPoints F G → ℂ) :
    ∃ ℓ : Fin k' → ℂ, ∀ a : Fin k' → ℂ,
      Integrable (AdelicGroupPoints.inducedInnerProductIntegrand K p l e β φ
          (fun g => ∑ x, a x * χ x g))
        ((compactHaarProbability F G K hKc).prod
          (LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F M)
            (isDiscrete_rationalSubgroup F M) μM)) →
      inducedInnerProduct K hKc p l μM e β φ (fun g => ∑ x, a x * χ x g) =
        ∑ x, (starRingEnd ℂ) (a x) * ℓ x := by
  classical
  set meas := (compactHaarProbability F G K hKc).prod
    (LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F M)
      (isDiscrete_rationalSubgroup F M) μM) with hmeas
  set I : (Fin k' → ℂ) → K × RationalQuotient F M → ℂ := fun a =>
    AdelicGroupPoints.inducedInnerProductIntegrand K p l e β φ (fun g => ∑ x, a x * χ x g)
    with hI
  have hadd : ∀ a b, I (a + b) = fun z => I a z + I b z := by
    intro a b
    rw [hI]
    dsimp only
    rw [← inducedInnerProductIntegrand_add_right]
    congr 1
    funext g
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  have hsmul : ∀ (t : ℂ) a, I (t • a) = fun z => (starRingEnd ℂ) t * I a z := by
    intro t a
    rw [hI]
    dsimp only
    rw [← inducedInnerProductIntegrand_mul_right]
    congr 1
    funext g
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  have hzero : I 0 = fun _ => 0 := by
    have h := hsmul 0 0
    rw [zero_smul] at h
    rw [h]
    funext z
    simp
  let A : Submodule ℂ (Fin k' → ℂ) :=
    { carrier := {a | Integrable (I a) meas}
      add_mem' := fun {a b} ha hb => by
        show Integrable (I (a + b)) meas
        rw [hadd]
        exact ha.add hb
      zero_mem' := by
        show Integrable (I 0) meas
        rw [hzero]
        exact integrable_zero _ _ _
      smul_mem' := fun t a ha => by
        show Integrable (I (t • a)) meas
        rw [hsmul]
        exact ha.const_mul _ }
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl A
  set pr := Submodule.projectionOnto A C hC with hpr
  set Lt : (Fin k' → ℂ) → ℂ := fun a => ∫ z, I (pr a : Fin k' → ℂ) z ∂meas with hLt
  have hmem : ∀ a, Integrable (I (pr a : Fin k' → ℂ)) meas := fun a => (pr a).2
  have Lt_add : ∀ a b, Lt (a + b) = Lt a + Lt b := by
    intro a b
    simp only [hLt, map_add, Submodule.coe_add]
    rw [hadd, integral_add (hmem a) (hmem b)]
  have Lt_smul : ∀ (t : ℂ) a, Lt (t • a) = (starRingEnd ℂ) t * Lt a := by
    intro t a
    simp only [hLt, map_smul, Submodule.coe_smul]
    rw [hsmul, integral_const_mul]
  refine ⟨fun x => Lt (Pi.single x 1), fun a ha => ?_⟩
  have hpa : (pr a : Fin k' → ℂ) = a := by
    have := Submodule.projectionOnto_apply_left hC ⟨a, ha⟩
    exact congrArg Subtype.val this
  have hval : inducedInnerProduct K hKc p l μM e β φ (fun g => ∑ x, a x * χ x g) = Lt a := by
    rw [inducedInnerProduct_eq_integral_prod K hKc p l μM e β ha]
    simp only [hLt, hpa]
    rfl
  rw [hval]
  let LtH : (Fin k' → ℂ) →+ ℂ := AddMonoidHom.mk' Lt Lt_add
  have hdecomp : a = ∑ x, a x • (Pi.single x 1 : Fin k' → ℂ) := by
    conv_lhs => rw [← Finset.univ_sum_single a]
    refine Finset.sum_congr rfl fun x _ => ?_
    ext y
    simp [Pi.single_apply]
  have h1 : Lt a = LtH (∑ x, a x • (Pi.single x 1 : Fin k' → ℂ)) := by
    rw [← hdecomp]
    rfl
  rw [h1, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  exact Lt_smul (a x) (Pi.single x 1)

end Pairing

end Langlands.Global

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

/-! ## The two statements -/

/-- Adjunction of intertwining integrals in a region of convergence (Mœglin–Waldspurger II.1.8).
In the setting of `IntertwiningContinuedAdjunctionStatement`, for `φ ∈ A^2_P` and
`φ' ∈ A^2_{P'}` there is `R` such that for every `s ∈ ℂⁿ` with `λ = realChart e s`
`R`-regular, writing `ν = w(-λ̄) = weylParameter l cw π' (realChart e (-conj s))`, the integrands
of `(M(w, λ)φ, φ')_{P'}` and of `(φ, M(w⁻¹, ν)φ')_P` are integrable on `K × M'(F) \ M'(𝔸)` and
`K × M(F) \ M(𝔸)`, and `(M(w, λ)φ, φ')_{P'} = (φ, M(w⁻¹, ν)φ')_P`. Both operators are the
intertwining integrals `intertwiningOperator`. -/
def IntertwiningConvergentAdjunctionStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (G P M U P' M' U' : GroupScheme (Spec (CommRingCat.of F)))
    (A A' : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
    [IsAffine P'.X.left] [IsAffine M'.X.left] [LocallyOfFiniteType M'.X.hom]
    [IsAffine U'.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    [IsClosedImmersion (iU ≫ p).hom.hom.left]
    (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp) (π : P ⟶ M)
    (p' : P' ⟶ G) [IsClosedImmersion p'.hom.hom.left] (iU' : U' ⟶ P') (l' : M' ⟶ P')
    [IsClosedImmersion (iU' ≫ p').hom.hom.left]
    (a' : A'.toGrp ⟶ M') (r' : ParabolicRootPresentation p' l' a')
    [Mono r'.data.i.hom.hom.left] [Fintype (relativeWeylGroup r'.data.i)]
    [Mono (CommGroupScheme.groupHom r'.data.f).hom.hom.left]
    (hA' : IsSplitTorus A'.toGrp) (hT' : IsSplitTorus r'.data.T.toGrp) (π' : P' ⟶ M')
    (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (cw : M' ⟶ M) (cw' : M ⟶ M'),
    haveI : LocallyOfFiniteType P.X.hom :=
      IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
    haveI : LocallyOfFiniteType P'.X.hom :=
      IsClosedSubgroup.locallyOfFiniteType (j := p') ‹IsClosedImmersion p'.hom.hom.left›
    IsConnectedReductive G → LeviSubgroup.IsGeometricUnipotentRadical iU →
    LeviSubgroup.IsGeometricUnipotentRadical iU' → l ≫ π = 𝟙 M → l' ≫ π' = 𝟙 M' →
    IsWeylConjugation p l p' l' w cw → IsWeylConjugation p' l' p l w⁻¹ cw' →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K)
      (hK' : IsIwasawaCompact p' K) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
    ∀ (μM : Measure (AdelicGroupPoints F M)) [μM.IsHaarMeasure]
      (μM' : Measure (AdelicGroupPoints F M')) [μM'.IsHaarMeasure],
      IsIwasawaCompatibleMeasure K hK.isCompact p iU l μM →
      IsIwasawaCompatibleMeasure K hK'.isCompact p' iU' l' μM' →
    ∀ {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P)
      (e' : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P'),
      (∀ x, e' x = realWeylParameter l cw π' (e x)) →
    ∀ (β β' : (Fin n → ℝ) → ℝ),
      Continuous β → HasCompactSupport β → ∫ y, β y = 1 →
      Continuous β' → HasCompactSupport β' → ∫ y, β' y = 1 →
    ∀ (φ φ' : AdelicGroupPoints F G → ℂ),
      IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l φ →
      IsSquareIntegrableInducedForm K hK'.isCompact rho hsmooth hcalc p' iU' l' φ' →
    ∃ R : ℝ, ∀ s : Fin n → ℂ, r.IsRegularParameter hA hT R (realChart e s) →
      Integrable (AdelicGroupPoints.inducedInnerProductIntegrand K p' l' e' β'
          (fun g => hK.intertwiningOperator hK' iU l iU' cw π' w φ (realChart e s) g) φ')
        ((compactHaarProbability F G K hK'.isCompact).prod
          (LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F M')
            (isDiscrete_rationalSubgroup F M') μM')) ∧
      Integrable (AdelicGroupPoints.inducedInnerProductIntegrand K p l e β φ
          (fun g => hK'.intertwiningOperator hK iU' l' iU cw' π w⁻¹ φ'
            (weylParameter l cw π' (realChart e (fun t => -(starRingEnd ℂ) (s t)))) g))
        ((compactHaarProbability F G K hK.isCompact).prod
          (LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F M)
            (isDiscrete_rationalSubgroup F M) μM)) ∧
      inducedInnerProduct K hK'.isCompact p' l' μM' e' β'
          (fun g => hK.intertwiningOperator hK' iU l iU' cw π' w φ (realChart e s) g) φ' =
        inducedInnerProduct K hK.isCompact p l μM e β φ
          (fun g => hK'.intertwiningOperator hK iU' l' iU cw' π w⁻¹ φ'
            (weylParameter l cw π' (realChart e (fun t => -(starRingEnd ℂ) (s t)))) g)

/-- Agreement of the continuation of an intertwining operator with the intertwining integral
on the reflected regular region (Mœglin–Waldspurger II.1.6 (iv), Bernstein–Lapid §2.2). Let
`P = MU` and `Q = M'V` be parabolics of a connected reductive `G` over a number field with
presentations `r` and `r'`, let `(w, c)` present an element of `W(P, Q)`, let `π'` be a retraction
of `l'`, and let `φ` be an automorphic form on `U(𝔸)M(F) \ G(𝔸)`. If
`M(w, λ)φ = ∑ i, coeff i λ • ψ i` for `Re λ` sufficiently regular, with `coeff i` meromorphic
with one domain `D`, then for some `R` the same identity holds, with `M(w, λ)φ` the intertwining
integral, for every `λ ∈ D` such that `-wλ` is `R`-regular for `r'`. -/
def IntertwiningReflectedRegionAgreementStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G P M U Q M' V : GroupScheme (Spec (CommRingCat.of F)))
    (A A' : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [IsAffine Q.X.left] [IsAffine V.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)
    (q : Q ⟶ G) [IsClosedImmersion q.hom.hom.left] (iV : V ⟶ Q) (l' : M' ⟶ Q)
    [IsClosedImmersion (iV ≫ q).hom.hom.left]
    (a' : A'.toGrp ⟶ M') (r' : ParabolicRootPresentation q l' a')
    [Mono r'.data.i.hom.hom.left] [Fintype (relativeWeylGroup r'.data.i)]
    [Mono (CommGroupScheme.groupHom r'.data.f).hom.hom.left]
    (hA' : IsSplitTorus A'.toGrp) (hT' : IsSplitTorus r'.data.T.toGrp) (π' : Q ⟶ M')
    (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (c : M' ⟶ M),
    IsConnectedReductive G → LeviSubgroup.IsGeometricUnipotentRadical iU →
    LeviSubgroup.IsGeometricUnipotentRadical iV → l' ≫ π' = 𝟙 M' →
    IsWeylConjugation p l q l' w c →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K)
      (hK' : IsIwasawaCompact q K) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth) (φ : AdelicGroupPoints F G → ℂ),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
      IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
        (K.comap (ofInfinite F G).toMonoidHom) rho φ →
    ∀ (k : ℕ) (ψ : Fin k → AdelicGroupPoints F G → ℂ)
      (coeff : Fin k → ComplexCharacterParameter F P → ℂ)
      (D : Set (ComplexCharacterParameter F P)),
      (∀ i, IsMeromorphicInCoordinatesOn (coeff i) D) →
      (∃ R₀ : ℝ, ∀ lam, r.IsRegularParameter hA hT R₀ lam → ∀ g,
        hK.intertwiningOperator hK' iU l iV c π' w φ lam g = ∑ i, coeff i lam * ψ i g) →
    ∃ R : ℝ, ∀ lam : ComplexCharacterParameter F P,
      r'.IsRegularParameter hA' hT' R (-weylParameter l c π' lam) → lam ∈ D →
      ∀ g : AdelicGroupPoints F G,
        hK.intertwiningOperator hK' iU l iV c π' w φ lam g = ∑ i, coeff i lam * ψ i g

/-- The two statements above imply `IntertwiningContinuedAdjunctionStatement`. -/
def IntertwiningContinuedAdjunctionReductionStatement : Prop :=
  IntertwiningConvergentAdjunctionStatement →
    IntertwiningReflectedRegionAgreementStatement.{0} → IntertwiningContinuedAdjunctionStatement

/-! ## The reduction -/

/-- **Adjunction of continued intertwining operators** (Mœglin–Waldspurger II.1.8 and
IV.1.9 (e)) from the adjunction of the intertwining integrals in a region of convergence and the
agreement of the continuation with the integral on the reflected regular region. -/
theorem intertwiningContinuedAdjunction_of_inputs
    (h1 : IntertwiningConvergentAdjunctionStatement)
    (h2 : IntertwiningReflectedRegionAgreementStatement.{0}) :
    IntertwiningContinuedAdjunctionStatement := by
  intro F _ _ G P M U P' M' U' A A' _ _ _ _ _ _ _ _ _ _ _ p _ iU l _ a r _ _ _ hA hT π
    p' _ iU' l' _ a' r' _ _ _ hA' hT' π' w cw cw' hGred hiU hiU' hπ hπ' hW hW' K hK hK' N d
    rho hsmooth hcalc hKmax hrho μM _ μM' _ hμM hμM' n e e' hee' β β' hβc hβs hβ1 hβ'c hβ's
    hβ'1 φ k ψ coeff D hφ hψ hcoeff hexp m φ' k' χ coeff' D' hφ' hχ hcoeff' hrev
  classical
  have : LocallyOfFiniteType P.X.hom :=
    IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
  have : LocallyOfFiniteType P'.X.hom :=
    IsClosedSubgroup.locallyOfFiniteType (j := p') ‹IsClosedImmersion p'.hom.hom.left›
  have hl : IsRationalLeviSubgroup l := r.isCompatible.levi
  have hl' : IsRationalLeviSubgroup l' := r'.isCompatible.levi
  have : IsIso cw := hW.isIso
  have hpOver : Mono p.hom.hom := by
    let := r.isCompatible.parabolic.isClosedSubgroup.mono
    exact Over.mono_of_mono_left _
  have : Mono p := (Grp.forget _).mono_of_mono_map (f := p) hpOver
  obtain ⟨We, hWe⟩ := AdelicGroupPoints.exists_weylParameter_linearEquiv l l' hl hl' cw π' hπ'
  have hWapp : ∀ x, We x = weylParameter l cw π' x := fun x => LinearMap.congr_fun hWe x
  have : FiniteDimensional ℂ (ComplexCharacterParameter F P) :=
    LinearEquiv.finiteDimensional (realChart e)
  have : FiniteDimensional ℂ (ComplexCharacterParameter F P') :=
    LinearEquiv.finiteDimensional We
  set E₂ : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P' := (realChart e).trans We with hE₂
  set ρ := negConjHomeomorph n with hρ
  -- `ν(s) = w(-λ̄)` in the chart.
  have hνE : ∀ s : Fin n → ℂ,
      weylParameter l cw π' (realChart e (fun t => -(starRingEnd ℂ) (s t))) = E₂ (ρ s) := by
    intro s
    rw [hE₂, LinearEquiv.trans_apply, hWapp]
    rfl
  -- Domains, with empty families allowed.
  set Dt : Set (ComplexCharacterParameter F P) := ⋂ _ : Fin k, D with hDt
  obtain ⟨hDt_od, hcoeff_t⟩ := isMeromorphicInCoordinatesOn_iInter_finite hcoeff
  set D't : Set (ComplexCharacterParameter F P') := ⋂ _ : Fin m × Fin k', D' with hD't
  obtain ⟨hD't_od, hcoeff'_t⟩ := isMeromorphicInCoordinatesOn_iInter_finite
    (f := fun ix : Fin m × Fin k' => coeff' ix.1 ix.2) fun ix => hcoeff' ix.1 ix.2
  have hDsub : D ⊆ Dt := fun y hy => mem_iInter.2 fun _ => hy
  have hD'sub : D' ⊆ D't := fun y hy => mem_iInter.2 fun _ => hy
  have hD'i : ∀ i' : Fin m, D't ⊆ ⋂ _ : Fin k', D' := fun i' y hy =>
    mem_iInter.2 fun x => mem_iInter.1 hy (i', x)
  have hcoeff'_i : ∀ i' x, IsMeromorphicInCoordinatesOn (coeff' i' x) (⋂ _ : Fin k', D') :=
    fun i' => (isMeromorphicInCoordinatesOn_iInter_finite (hcoeff' i')).2
  -- The thresholds.
  obtain ⟨R₁, hR₁⟩ := hexp
  choose R₂ hR₂ using fun i' => h1 F G P M U P' M' U' A A' p iU l a r hA hT π p' iU' l' a' r'
    hA' hT' π' w cw cw' hGred hiU hiU' hπ hπ' hW hW' K hK hK' rho hsmooth hcalc hKmax hrho μM
    μM' hμM hμM' e e' hee' β β' hβc hβs hβ1 hβ'c hβ's hβ'1 φ (φ' i') hφ (hφ' i')
  choose R₃ hR₃ using fun i' => h2 F G P' M' U' P M U A' A p' iU' l' a' r' hA' hT' p iU l a r
    hA hT π w⁻¹ cw' hGred hiU' hiU hπ hW' K hK' hK rho hsmooth hcalc (φ' i') hKmax hrho
    (hφ' i').1 k' χ (coeff' i') (⋂ _ : Fin k', D') (hcoeff'_i i') (hrev i')
  set R : ℝ := max R₁ 0 + ∑ i', |R₂ i'| + ∑ i', |R₃ i'| with hRdef
  have hsum₂ : 0 ≤ ∑ i', |R₂ i'| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hsum₃ : 0 ≤ ∑ i', |R₃ i'| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hRR₁ : R₁ ≤ R := by
    have := le_max_left R₁ 0
    linarith
  have hRR₂ : ∀ i', R₂ i' ≤ R := by
    intro i'
    have h1' := le_abs_self (R₂ i')
    have h2' : |R₂ i'| ≤ ∑ j, |R₂ j| :=
      Finset.single_le_sum (f := fun j => |R₂ j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i')
    have := le_max_right R₁ 0
    linarith
  have hRR₃ : ∀ i', R₃ i' ≤ R := by
    intro i'
    have h1' := le_abs_self (R₃ i')
    have h2' : |R₃ i'| ≤ ∑ j, |R₃ j| :=
      Finset.single_le_sum (f := fun j => |R₃ j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i')
    have := le_max_right R₁ 0
    linarith
  -- A nonempty open set of regular parameters.
  obtain ⟨lam₀, h₀⟩ := r.exists_regularParameter hA hT 0
  obtain ⟨O, hOo, hOne, hOreg⟩ := exists_isOpen_isRegularParameter r hA hT h₀ R (realChart e)
  -- The Gram matrix on `P'` and the conjugate-linear form on `P`.
  set Gm : Fin k → Fin m → ℂ := fun i i' =>
    inducedInnerProduct K hK'.isCompact p' l' μM' e' β' (ψ i) (φ' i') with hGm
  have hintP' : ∀ i i', Integrable (AdelicGroupPoints.inducedInnerProductIntegrand K p' l' e' β'
      (ψ i) (φ' i'))
      ((compactHaarProbability F G K hK'.isCompact).prod
        (LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F M')
          (isDiscrete_rationalSubgroup F M') μM')) :=
    fun i i' => InducedInnerProductIntegrable.integrable_inducedInnerProduct_integrand e'
      hl'.isConnectedReductive r'.isCompatible.splitComponent hA' hπ' μM' hβ'c hβ's (hψ i)
      (hφ' i')
  obtain ⟨ℓ, hℓ⟩ := exists_inducedInnerProduct_sum_right_eq K hK.isCompact p l μM e β φ χ
  -- The two meromorphic functions.
  set f₁ : (Fin m → ℂ) → (Fin n → ℂ) → ℂ := fun c s =>
    ∑ i, coeff i (realChart e s) * ∑ i', (starRingEnd ℂ) (c i') * Gm i i' with hf₁
  set f₂ : (Fin m → ℂ) → (Fin n → ℂ) → ℂ := fun c s =>
    ∑ x, ∑ i', (starRingEnd ℂ) (coeff' i' x (E₂ (ρ s))) * ((starRingEnd ℂ) (c i') * ℓ x)
    with hf₂
  set U₁ : Set (Fin n → ℂ) := realChart e ⁻¹' Dt with hU₁
  set U₂ : Set (Fin n → ℂ) := ρ ⁻¹' (E₂ ⁻¹' D't) with hU₂
  have hU₁od : IsOpen U₁ ∧ Dense U₁ := hDt_od n (realChart e)
  have hU₂od : IsOpen U₂ ∧ Dense U₂ :=
    ⟨(hD't_od n E₂).1.preimage ρ.continuous, (hD't_od n E₂).2.preimage ρ.isOpenMap⟩
  have hmero₁ : ∀ c, IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) (f₁ c) U₁ := fun c =>
    isMeromorphicOn_sum Finset.univ hU₁od.1 hU₁od.2 fun i _ =>
      ((hcoeff_t i).2 n (realChart e)).mul_const _
  have hmero₂ : ∀ c, IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) (f₂ c) U₂ := fun c =>
    isMeromorphicOn_sum Finset.univ hU₂od.1 hU₂od.2 fun x _ =>
      isMeromorphicOn_sum Finset.univ hU₂od.1 hU₂od.2 fun i' _ =>
        (((hcoeff'_t (i', x)).2 n E₂).conj_comp_negConj).mul_const _
  -- The left side is `f₁`.
  have hLHS : ∀ (c : Fin m → ℂ) (s : Fin n → ℂ),
      inducedInnerProduct K hK'.isCompact p' l' μM' e' β'
          (fun g => ∑ i, coeff i (realChart e s) * ψ i g) (fun g => ∑ i', c i' * φ' i' g) =
        f₁ c s := by
    intro c s
    rw [inducedInnerProduct_sum_sum K hK'.isCompact p' l' μM' e' β' ψ φ'
      (fun i => coeff i (realChart e s)) c hintP', hf₁]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i' _ => by ring
  -- The right side is `f₂` wherever its integrand is integrable.
  have hRHS : ∀ (c : Fin m → ℂ) (s : Fin n → ℂ),
      Integrable (AdelicGroupPoints.inducedInnerProductIntegrand K p l e β φ
          (fun g => ∑ x, (∑ i', c i' *
            coeff' i' x (weylParameter l cw π' (realChart e (fun t => -(starRingEnd ℂ) (s t))))) *
              χ x g))
        ((compactHaarProbability F G K hK.isCompact).prod
          (LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F M)
            (isDiscrete_rationalSubgroup F M) μM)) →
      inducedInnerProduct K hK.isCompact p l μM e β φ
          (fun g => ∑ x, (∑ i', c i' *
            coeff' i' x (weylParameter l cw π' (realChart e (fun t => -(starRingEnd ℂ) (s t))))) *
              χ x g) = f₂ c s := by
    intro c s hint
    rw [hℓ _ hint, hf₂]
    dsimp only
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_sum, Finset.sum_mul, hνE s]
    exact Finset.sum_congr rfl fun i' _ => by rw [map_mul]; ring
  -- On the regular open set, both sides agree.
  have hkey : ∀ s ∈ O, s ∈ U₂ → ∀ c : Fin m → ℂ,
      Integrable (AdelicGroupPoints.inducedInnerProductIntegrand K p l e β φ
          (fun g => ∑ x, (∑ i', c i' *
            coeff' i' x (weylParameter l cw π' (realChart e (fun t => -(starRingEnd ℂ) (s t))))) *
              χ x g))
        ((compactHaarProbability F G K hK.isCompact).prod
          (LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F M)
            (isDiscrete_rationalSubgroup F M) μM)) ∧
      inducedInnerProduct K hK'.isCompact p' l' μM' e' β'
          (fun g => ∑ i, coeff i (realChart e s) * ψ i g) (fun g => ∑ i', c i' * φ' i' g) =
        inducedInnerProduct K hK.isCompact p l μM e β φ
          (fun g => ∑ x, (∑ i', c i' *
            coeff' i' x (weylParameter l cw π' (realChart e (fun t => -(starRingEnd ℂ) (s t))))) *
              χ x g) := by
    intro s hsO hsU₂ c
    have hreg := hOreg s hsO
    set nu := weylParameter l cw π' (realChart e (fun t => -(starRingEnd ℂ) (s t))) with hnu
    -- Regularity for the agreement statement.
    have hinv : weylParameter l' cw' π nu = realChart e (fun t => -(starRingEnd ℂ) (s t)) :=
      AdelicGroupPoints.weylParameter_weylParameter_of_inv r hπ hπ' hW hW' _
    have hneg : -weylParameter l' cw' π nu = realChart e (fun t => (starRingEnd ℂ) (s t)) := by
      rw [hinv, ← map_neg]
      congr 1
      funext t
      simp
    have hre : parameterRealPart F P (realChart e s) =
        parameterRealPart F P (-weylParameter l' cw' π nu) := by
      rw [hneg, parameterRealPart_realChart, parameterRealPart_realChart]
      congr 1
    have hreg₃ : ∀ i', r.IsRegularParameter hA hT (R₃ i') (-weylParameter l' cw' π nu) :=
      fun i' => (r.isRegularParameter_of_parameterRealPart_eq hA hT hre hreg).mono r hA hT
        (hRR₃ i')
    have hnuD : ∀ i' : Fin m, nu ∈ ⋂ _ : Fin k', D' := by
      intro i'
      apply hD'i i'
      have : E₂ (ρ s) ∈ D't := hsU₂
      rw [← hνE s] at this
      exact this
    -- The integral `M(w⁻¹, ν)(φ' i')` is its continuation.
    set Mint : Fin m → AdelicGroupPoints F G → ℂ := fun i' g =>
      hK'.intertwiningOperator hK iU' l' iU cw' π w⁻¹ (φ' i') nu g with hMint
    have hMint_eq : ∀ i' g, Mint i' g = ∑ x, coeff' i' x nu * χ x g :=
      fun i' g => hR₃ i' nu (hreg₃ i') (hnuD i') g
    have hfun : (fun g => ∑ x, (∑ i', c i' * coeff' i' x nu) * χ x g) =
        fun g => ∑ i', c i' * Mint i' g := by
      funext g
      simp only [hMint_eq, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun x _ => by ring
    -- The convergent adjunction.
    have hS1 := fun i' => hR₂ i' s (hreg.mono r hA hT (hRR₂ i'))
    have hintR : ∀ i', Integrable (AdelicGroupPoints.inducedInnerProductIntegrand K p l e β φ
        (Mint i'))
        ((compactHaarProbability F G K hK.isCompact).prod
          (LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F M)
            (isDiscrete_rationalSubgroup F M) μM)) := fun i' => (hS1 i').2.1
    obtain ⟨hcomb, hval⟩ := inducedInnerProduct_sum_right K hK.isCompact p l μM e β φ Mint c hintR
    rw [hfun]
    refine ⟨hcomb, ?_⟩
    rw [hval, hLHS c s, hf₁]
    dsimp only
    have hforward : ∀ i', inducedInnerProduct K hK.isCompact p l μM e β φ (Mint i') =
        ∑ i, coeff i (realChart e s) * Gm i i' := by
      intro i'
      rw [← (hS1 i').2.2]
      have hM : (fun g => hK.intertwiningOperator hK' iU l iU' cw π' w φ (realChart e s) g) =
          fun g => ∑ i, coeff i (realChart e s) * ψ i g :=
        funext fun g => hR₁ _ (hreg.mono r hA hT hRR₁) g
      rw [hM, inducedInnerProduct_sum_left K hK'.isCompact p' l' μM' e' β' ψ _ (φ' i')
        fun i => hintP' i i']
    simp only [hforward, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => by ring
  -- The identity theorem.
  have hid : ∀ c : Fin m → ℂ, ∀ s ∈ U₁, s ∈ U₂ → f₁ c s = f₂ c s := by
    intro c
    refine (hmero₁ c).eq_of_eqOn_isOpen (hmero₂ c) hOo hOne fun s hsO _ hs₂ => ?_
    obtain ⟨hint, heq⟩ := hkey s hsO hs₂ c
    rw [← hLHS, heq, hRHS c s hint]
  refine ⟨univ, isOpen_univ, dense_univ, fun s _ hsD hsD' c hint => ?_⟩
  have hs₁ : s ∈ U₁ := hDsub hsD
  have hs₂ : s ∈ U₂ := by
    show E₂ (ρ s) ∈ D't
    rw [← hνE s]
    exact hD'sub hsD'
  rw [hLHS, hid c s hs₁ hs₂, hRHS c s hint]

/-- The reduction, in the form of the proposition
`IntertwiningContinuedAdjunctionReductionStatement`. -/
theorem intertwiningContinuedAdjunctionReduction :
    IntertwiningContinuedAdjunctionReductionStatement :=
  fun h1 h2 => intertwiningContinuedAdjunction_of_inputs h1 h2

end Langlands.Global
