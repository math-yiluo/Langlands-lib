import Langlands.Theta.Metaplectic.Block

/-!
# The standard Weil operator under an isomorphism of polarized spaces

GKT §2.3.1 (Definition 2.9, p. 54, Proposition 2.13, p. 55): the standard Weil operator `r(g)` of a
polarization depends on the polarized space only up to isomorphism. For pairings
`β : X × Y → F`, `β' : X' × Y' → F` and linear isomorphisms `eX : X ≃ X'`, `eY : Y ≃ Y'` with
`β'(eX x, eY y) = β(x, y)`:

* `isometryGroupCongr eX eY he : Sp(X × Y) ≃* Sp(X' × Y')`, `g ↦ (eX × eY) g (eX × eY)⁻¹`, with
  `standardKernel_isometryGroupCongr` (`ker c` is carried by `eY`) and
  `standardIntegrand_isometryGroupCongr`;
* `schwartzBruhatComp eX : S(X') ≃ S(X)`, `φ ↦ φ ∘ eX`, and
  `schwartzBruhatInner_schwartzBruhatComp` (the `L²` forms of `ν` and of `eX⁻¹_* ν`);
* `standardOperator_isometryGroupCongr`: **`r(e g e⁻¹) φ ∘ eX = r(g) (φ ∘ eX)`**. The quotients
  `Y ⧸ ker c` correspond (`standardQuotientCongr`), the image of `d_g` is a positive multiple of
  `d_{e g e⁻¹}` (`exists_map_eq_smul`), and the multiple is `1` because both operators are unitary
  (`eq_of_eq_smul_of_inner`);
* `standardOperator_comp_isometryGroupCongr`: the scalars of the composition rule
  (`exists_standardOperator_comp`) are carried along.
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Langlands.Theta

open HeisenbergGroup Langlands.HarmonicAnalysis
open Langlands.LinearMap.BilinForm (isometryGroup)

universe u v w v' w'

section Group

variable {R : Type u} [CommRing R] {X : Type v} {Y : Type w} {X' : Type v'} {Y' : Type w'}
  [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
  [AddCommGroup X'] [Module R X'] [AddCommGroup Y'] [Module R Y']
  {β : X →ₗ[R] Y →ₗ[R] R} {β' : X' →ₗ[R] Y' →ₗ[R] R}
  (eX : X ≃ₗ[R] X') (eY : Y ≃ₗ[R] Y') (he : ∀ x y, β' (eX x) (eY y) = β x y)

include he in
/-- `eX × eY` is an isometry from `polarizedForm β` to `polarizedForm β'`. -/
theorem polarizedForm_prodCongr (w w' : X × Y) :
    polarizedForm β' (eX.prodCongr eY w) (eX.prodCongr eY w') = polarizedForm β w w' := by
  simp [polarizedForm_apply, he]

/-- **Transport of isometries** along `eX × eY`: `g ↦ (eX × eY) g (eX × eY)⁻¹`. -/
def isometryGroupCongr : isometryGroup (polarizedForm β) ≃* isometryGroup (polarizedForm β') where
  toFun g := ⟨(eX.prodCongr eY).symm.trans ((g : (X × Y) ≃ₗ[R] X × Y).trans (eX.prodCongr eY)),
    fun w w' => by
      change polarizedForm β' (eX.prodCongr eY ((g : (X × Y) ≃ₗ[R] X × Y)
          ((eX.prodCongr eY).symm w))) (eX.prodCongr eY ((g : (X × Y) ≃ₗ[R] X × Y)
          ((eX.prodCongr eY).symm w'))) = _
      rw [polarizedForm_prodCongr eX eY he, g.2, ← polarizedForm_prodCongr eX eY he,
        LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]⟩
  invFun g := ⟨(eX.prodCongr eY).trans ((g : (X' × Y') ≃ₗ[R] X' × Y').trans
      (eX.prodCongr eY).symm), fun w w' => by
      change polarizedForm β ((eX.prodCongr eY).symm ((g : (X' × Y') ≃ₗ[R] X' × Y')
          (eX.prodCongr eY w))) ((eX.prodCongr eY).symm ((g : (X' × Y') ≃ₗ[R] X' × Y')
          (eX.prodCongr eY w'))) = _
      rw [← polarizedForm_prodCongr eX eY he, LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply, g.2, polarizedForm_prodCongr eX eY he]⟩
  left_inv g := Subtype.ext <| LinearEquiv.ext fun w => by
    change (eX.prodCongr eY).symm (eX.prodCongr eY ((g : (X × Y) ≃ₗ[R] X × Y)
      ((eX.prodCongr eY).symm (eX.prodCongr eY w)))) = _
    simp
  right_inv g := Subtype.ext <| LinearEquiv.ext fun w => by
    change eX.prodCongr eY ((eX.prodCongr eY).symm ((g : (X' × Y') ≃ₗ[R] X' × Y')
      (eX.prodCongr eY ((eX.prodCongr eY).symm w)))) = _
    simp
  map_mul' g h := Subtype.ext <| LinearEquiv.ext fun w => by
    change eX.prodCongr eY ((g : (X × Y) ≃ₗ[R] X × Y) ((h : (X × Y) ≃ₗ[R] X × Y)
      ((eX.prodCongr eY).symm w))) = eX.prodCongr eY ((g : (X × Y) ≃ₗ[R] X × Y)
      ((eX.prodCongr eY).symm (eX.prodCongr eY ((h : (X × Y) ≃ₗ[R] X × Y)
        ((eX.prodCongr eY).symm w)))))
    simp

theorem isometryGroupCongr_apply (g : isometryGroup (polarizedForm β)) (w : X × Y) :
    ((isometryGroupCongr eX eY he g : isometryGroup (polarizedForm β')) :
      (X' × Y') ≃ₗ[R] X' × Y') (eX.prodCongr eY w) =
        eX.prodCongr eY ((g : (X × Y) ≃ₗ[R] X × Y) w) := by
  change eX.prodCongr eY ((g : (X × Y) ≃ₗ[R] X × Y) ((eX.prodCongr eY).symm
    (eX.prodCongr eY w))) = _
  rw [LinearEquiv.symm_apply_apply]

theorem isometryInv_isometryGroupCongr (g : isometryGroup (polarizedForm β)) (w : X × Y) :
    isometryInv (isometryGroupCongr eX eY he g) (eX.prodCongr eY w) =
      eX.prodCongr eY (isometryInv g w) := by
  rw [isometryInv, ← map_inv, isometryGroupCongr_apply]

/-- `ker c` is carried by `eY`. -/
theorem standardKernel_isometryGroupCongr (g : isometryGroup (polarizedForm β)) :
    (standardKernel g).map (eY : Y →ₗ[R] Y') = standardKernel (isometryGroupCongr eX eY he g) := by
  ext y'
  obtain ⟨y, rfl⟩ := eY.surjective y'
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply, mem_standardKernel,
    mem_standardKernel]
  have h := isometryInv_isometryGroupCongr eX eY he g (0, y)
  rw [LinearEquiv.prodCongr_apply, map_zero] at h
  rw [h, LinearEquiv.prodCongr_apply]
  exact eX.map_eq_zero_iff.symm

/-- The integrand is carried by `eX × eY`. -/
theorem standardIntegrand_isometryGroupCongr [Invertible (2 : R)] (ψ : AddChar R ℂ)
    (g : isometryGroup (polarizedForm β)) (φ : X' → ℂ) (x : X) (y : Y) :
    standardIntegrand ψ (isometryGroupCongr eX eY he g) φ (eX x) (eY y) =
      standardIntegrand ψ g (φ ∘ eX) x y := by
  have h := isometryInv_isometryGroupCongr eX eY he g (x, y)
  rw [LinearEquiv.prodCongr_apply] at h
  rw [standardIntegrand, standardIntegrand, h, LinearEquiv.prodCongr_apply, he, he]
  rfl

/-- The isomorphism `Y ⧸ ker c(g) ≃ Y' ⧸ ker c(e g e⁻¹)` induced by `eY`. -/
def standardQuotientCongr (g : isometryGroup (polarizedForm β)) :
    (Y ⧸ standardKernel g) ≃ₗ[R] (Y' ⧸ standardKernel (isometryGroupCongr eX eY he g)) :=
  Submodule.Quotient.equiv _ _ eY (standardKernel_isometryGroupCongr eX eY he g)

end Group

section Field

variable {F : Type u} [Field F] [Invertible (2 : F)] {X : Type v} {Y : Type w} {X' : Type v'}
  {Y' : Type w'} [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y]
  [AddCommGroup X'] [Module F X'] [AddCommGroup Y'] [Module F Y']
  {β : X →ₗ[F] Y →ₗ[F] F} {β' : X' →ₗ[F] Y' →ₗ[F] F} {ψ : AddChar F ℂ}
  (eX : X ≃ₗ[F] X') (eY : Y ≃ₗ[F] Y') (he : ∀ x y, β' (eX x) (eY y) = β x y)

theorem standardIntegrandQ_standardQuotientCongr (g : isometryGroup (polarizedForm β))
    (φ : X' → ℂ) (x : X) (q : Y ⧸ standardKernel g) :
    standardIntegrandQ ψ (isometryGroupCongr eX eY he g) φ (eX x)
        (standardQuotientCongr eX eY he g q) = standardIntegrandQ ψ g (φ ∘ eX) x q := by
  induction q using Submodule.Quotient.induction_on with | H y => ?_
  rw [standardQuotientCongr, Submodule.Quotient.equiv_apply, Submodule.mapQ_apply,
    standardIntegrandQ_mk, standardIntegrandQ_mk]
  exact standardIntegrand_isometryGroupCongr eX eY he ψ g φ x y

end Field

section Local

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {X : Type v} [AddCommGroup X] [Module F X] [FiniteDimensional F X] [TopologicalSpace X]
  [IsModuleTopology F X] [IsTopologicalAddGroup X]
  {X' : Type v'} [AddCommGroup X'] [Module F X'] [FiniteDimensional F X'] [TopologicalSpace X']
  [IsModuleTopology F X'] [IsTopologicalAddGroup X']
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace X'] [BorelSpace X']
  (eX : X ≃ₗ[F] X')

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [FiniteDimensional F X]
  [IsTopologicalAddGroup X] [FiniteDimensional F X'] [IsTopologicalAddGroup X'] [MeasurableSpace X]
  [BorelSpace X] [MeasurableSpace X'] [BorelSpace X'] in
private theorem mem_schwartzBruhatSubmodule_comp (φ : SchwartzBruhat X') :
    (fun x => (φ : X' → ℂ) (eX x)) ∈ schwartzBruhatSubmodule X :=
  ⟨φ.2.1.comp_continuous (continuous_of_linearMap' eX.toLinearMap),
    φ.2.2.comp_homeomorph ⟨eX.toEquiv, continuous_of_linearMap' eX.toLinearMap,
      continuous_of_linearMap' eX.symm.toLinearMap⟩⟩

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [FiniteDimensional F X]
  [IsTopologicalAddGroup X] [FiniteDimensional F X'] [IsTopologicalAddGroup X'] [MeasurableSpace X]
  [BorelSpace X] [MeasurableSpace X'] [BorelSpace X'] in
/-- `φ ↦ φ ∘ eX`, from `S(X')` to `S(X)`. -/
def schwartzBruhatComp : SchwartzBruhat X' ≃ₗ[ℂ] SchwartzBruhat X where
  toFun φ := ⟨_, mem_schwartzBruhatSubmodule_comp eX φ⟩
  invFun φ := ⟨_, mem_schwartzBruhatSubmodule_comp eX.symm φ⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv φ := Subtype.ext <| funext fun x => by simp
  right_inv φ := Subtype.ext <| funext fun x => by simp

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [FiniteDimensional F X]
  [IsTopologicalAddGroup X] [FiniteDimensional F X'] [IsTopologicalAddGroup X'] [MeasurableSpace X]
  [BorelSpace X] [MeasurableSpace X'] [BorelSpace X'] in
@[simp] theorem schwartzBruhatComp_apply (φ : SchwartzBruhat X') (x : X) :
    (schwartzBruhatComp eX φ : X → ℂ) x = (φ : X' → ℂ) (eX x) := rfl

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [FiniteDimensional F X]
  [FiniteDimensional F X'] [IsTopologicalAddGroup X'] in
/-- `⟨φ ∘ eX, φ' ∘ eX⟩` for the image measure `eX⁻¹_* ν` is `⟨φ, φ'⟩` for `ν`. -/
theorem schwartzBruhatInner_schwartzBruhatComp (ν : Measure X') [ν.IsAddHaarMeasure]
    (φ φ' : SchwartzBruhat X') :
    schwartzBruhatInner (ν.map eX.symm) (schwartzBruhatComp eX φ) (schwartzBruhatComp eX φ') =
      schwartzBruhatInner ν φ φ' := by
  let E := (linearEquivToContinuousAddEquiv eX.symm).toHomeomorph.toMeasurableEquiv
  have hE : ν.map eX.symm = ν.map E := rfl
  rw [schwartzBruhatInner_apply, schwartzBruhatInner_apply, hE, integral_map_equiv]
  change ∫ x, (starRingEnd ℂ) ((φ : X' → ℂ) (eX (eX.symm x))) *
    (φ' : X' → ℂ) (eX (eX.symm x)) ∂ν = _
  simp only [LinearEquiv.apply_symm_apply]

end Local

section Operator

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Invertible (2 : F)]
  {X : Type v} [AddCommGroup X] [Module F X] [FiniteDimensional F X] [TopologicalSpace X]
  [IsModuleTopology F X] [IsTopologicalAddGroup X]
  {Y : Type w} [AddCommGroup Y] [Module F Y] [FiniteDimensional F Y] [TopologicalSpace Y]
  [IsModuleTopology F Y]
  {X' : Type v'} [AddCommGroup X'] [Module F X'] [FiniteDimensional F X'] [TopologicalSpace X']
  [IsModuleTopology F X'] [IsTopologicalAddGroup X']
  {Y' : Type w'} [AddCommGroup Y'] [Module F Y'] [FiniteDimensional F Y'] [TopologicalSpace Y']
  [IsModuleTopology F Y']
  {β : X →ₗ[F] Y →ₗ[F] F} {β' : X' →ₗ[F] Y' →ₗ[F] F} {ψ : AddChar F ℂ}
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace X'] [BorelSpace X'] [MeasurableSpace Y'] [BorelSpace Y']
  (eX : X ≃ₗ[F] X') (eY : Y ≃ₗ[F] Y') (he : ∀ x y, β' (eX x) (eY y) = β x y)
  [β.IsPerfPair] [β'.IsPerfPair] (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)

/-- **The standard Weil operator is carried by an isomorphism of polarized spaces**:
`r(e g e⁻¹) = T⁻¹ r(g) T` with `T φ = φ ∘ eX`. -/
theorem standardOperator_isometryGroupCongr (g : isometryGroup (polarizedForm β))
    (φ : SchwartzBruhat X') :
    schwartzBruhatComp eX (standardOperator hψ hψ1 (isometryGroupCongr eX eY he g) φ) =
      standardOperator hψ hψ1 g (schwartzBruhatComp eX φ) := by
  set g' := isometryGroupCongr eX eY he g
  obtain ⟨s, hs, hmap⟩ := exists_map_eq_smul (standardMeasure hψ hψ1 g)
    (standardMeasure hψ hψ1 g') (standardQuotientCongr eX eY he g)
  have key : ∀ (φ : SchwartzBruhat X') (x : X),
      (standardOperator hψ hψ1 g (schwartzBruhatComp eX φ) : X → ℂ) x =
        (s : ℂ) * (standardOperator hψ hψ1 g' φ : X' → ℂ) (eX x) := by
    intro φ x
    let Eq := (linearEquivToContinuousAddEquiv
      (standardQuotientCongr eX eY he g)).toHomeomorph.toMeasurableEquiv
    have hEq : (standardMeasure hψ hψ1 g).map (standardQuotientCongr eX eY he g) =
        (standardMeasure hψ hψ1 g).map Eq := rfl
    rw [standardOperator_apply, standardOperator_apply]
    have h1 : ∫ q, standardIntegrandQ ψ g ((schwartzBruhatComp eX φ : X → ℂ)) x q
        ∂(standardMeasure hψ hψ1 g) = ∫ q, standardIntegrandQ ψ g' φ (eX x) (Eq q)
          ∂(standardMeasure hψ hψ1 g) :=
      integral_congr_ae (Filter.Eventually.of_forall fun q =>
        (standardIntegrandQ_standardQuotientCongr eX eY he g φ x q).symm)
    rw [h1, ← integral_map_equiv Eq, ← hEq, hmap, integral_smul_nnreal_measure, NNReal.smul_def,
      Complex.real_smul]
  have := compactOpenExhaustion_of_finiteDimensional F X'
  have := locallyCompactSpace_of_finiteDimensional F X'
  set T := ((schwartzBruhatComp eX).symm : SchwartzBruhat X →ₗ[ℂ] SchwartzBruhat X') ∘ₗ
    standardOperator hψ hψ1 g ∘ₗ (schwartzBruhatComp eX : SchwartzBruhat X' →ₗ[ℂ] SchwartzBruhat X)
  have hT : T = ((s : ℝ) : ℂ) • standardOperator hψ hψ1 g' := by
    refine LinearMap.ext fun φ => Subtype.ext (funext fun x' => ?_)
    change (standardOperator hψ hψ1 g (schwartzBruhatComp eX φ) : X → ℂ) (eX.symm x') = _
    rw [key, LinearEquiv.apply_symm_apply]
    rfl
  have hu : ∀ φ φ', schwartzBruhatInner (Measure.addHaar : Measure X') (T φ) (T φ') =
      schwartzBruhatInner Measure.addHaar φ φ' := by
    intro φ φ'
    rw [← schwartzBruhatInner_schwartzBruhatComp eX]
    change schwartzBruhatInner _ (schwartzBruhatComp eX ((schwartzBruhatComp eX).symm _))
      (schwartzBruhatComp eX ((schwartzBruhatComp eX).symm _)) = _
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, LinearMap.comp_apply,
      LinearMap.comp_apply, standardOperator_inner]
    exact schwartzBruhatInner_schwartzBruhatComp eX _ φ φ'
  have hTT := eq_of_eq_smul_of_inner (NNReal.coe_pos.2 hs) hT Measure.addHaar hu
    (standardOperator_inner hψ hψ1 g' Measure.addHaar)
  have h2 := congrArg (fun A : SchwartzBruhat X' →ₗ[ℂ] SchwartzBruhat X' =>
    schwartzBruhatComp eX (A φ)) hTT
  simp only [T, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h2
  exact h2.symm

/-- **The scalars of the composition rule are carried by an isomorphism of polarized spaces**. -/
theorem standardOperator_comp_isometryGroupCongr {g₁ g₂ : isometryGroup (polarizedForm β)}
    {z : ℂ} (h : standardOperator hψ hψ1 g₁ ∘ₗ standardOperator hψ hψ1 g₂ =
      z • standardOperator hψ hψ1 (g₁ * g₂)) :
    standardOperator hψ hψ1 (isometryGroupCongr eX eY he g₁) ∘ₗ
        standardOperator hψ hψ1 (isometryGroupCongr eX eY he g₂) =
      z • standardOperator hψ hψ1 (isometryGroupCongr eX eY he (g₁ * g₂)) := by
  refine LinearMap.ext fun φ => (schwartzBruhatComp eX).injective ?_
  rw [LinearMap.comp_apply, standardOperator_isometryGroupCongr,
    standardOperator_isometryGroupCongr, LinearMap.smul_apply, map_smul,
    standardOperator_isometryGroupCongr, ← LinearMap.comp_apply, h, LinearMap.smul_apply]

end Operator

end Langlands.Theta
