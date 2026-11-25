import Langlands.Global.AdelicIntertwiningImaginaryUnitarityStatement
import Langlands.Global.AdelicIntertwiningImaginaryIsometryStatement
import Langlands.Global.AdelicInducedInnerProductGramStatement
import Langlands.Global.AdelicRootHyperplaneStatement
import Langlands.Analysis.Meromorphic.ImaginaryHolomorphicExtension
import Langlands.GroupScheme.Rational.ParabolicRootPresentationProof
import Langlands.GroupScheme.Rational.LeviRetraction
import Langlands.GroupScheme.Rational.ReductiveWeylFaithfulness
import Langlands.GroupScheme.Torus.UnipotentHom
import Langlands.GroupScheme.InnerAutomorphismHom
import Langlands.GroupScheme.Rational.ParabolicRootConeEvaluation
import Langlands.GroupScheme.Rational.ParabolicRootPresentationSimpleRoots
import Langlands.GroupScheme.Rational.RelativeCharacterRootComplementBaseChange
import Langlands.GroupScheme.Rational.RelativeRootsCharacterSpan
import Langlands.GroupScheme.Rational.RootSupportFiniteness
import Langlands.GroupScheme.Rational.StandardCocharacterFiniteness
import Langlands.Representation.Plancherel.AmbientCharacterIntertwiningCone
import Langlands.Representation.Exponents.GeometricLemmaExponentTransfer

/-! # Reduction of the unitarity of intertwining operators on the imaginary axis

Mœglin–Waldspurger IV.3.12 and Lapid 2011, p.312 and pp.328–329: holomorphy and unitarity of
`M(w, λ)` for `λ ∈ i𝔞_P^*` follow from the isometry identity at the imaginary points of
holomorphy, the positivity of the inner product on `A^2_{P'}` and the singularities of
`M(w, ·)` along root hyperplanes.

The private sections on rational characters of Levi subgroups and on regular parameters
contain helper lemmas. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct Manifold

set_option autoImplicit false

/-! ## Rational characters of rational Levi subgroups -/

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme

variable {F : Type u} [Field F]
  {P Q M M' : GroupScheme (Spec (CommRingCat.of F))}

private theorem characterRestrict_injective_of_levi {l : M ⟶ P}
    (hl : IsRationalLeviSubgroup l) : Function.Injective (characterRestrict l) := by
  obtain ⟨U, i, hi, hmul⟩ := hl.exists_unipotentRadical
  let : IsIso (subgroupMultiplication l i) := hmul
  intro χ ψ h
  apply Additive.toMul.injective
  apply hom_ext_points
  intro T x
  have hfactor (θ : rationalCharacters P) :
      x ≫ θ.toMul.hom.hom = leviComponent l i x ≫ (characterRestrict l θ).toMul.hom.hom := by
    have htriv := hi.1.isUnipotent.comp_eq_one_of_isSplitTorus isSplitTorus_gm
      (i ≫ θ.toMul) T (radicalComponent l i x)
    simp only [Grp.comp_hom_hom] at htriv
    calc
      _ = ((leviComponent l i x ≫ l.hom.hom) *
          (radicalComponent l i x ≫ i.hom.hom)) ≫ θ.toMul.hom.hom :=
        congrArg (fun y : T ⟶ P.X => y ≫ θ.toMul.hom.hom)
          (leviComponent_mul_radicalComponent l i x).symm
      _ = _ := by
        simp only [MonObj.mul_comp, Category.assoc, htriv, mul_one,
          characterRestrict_apply, Grp.comp_hom_hom]
  rw [hfactor χ, hfactor ψ, h]

private theorem characterRestrict_rightInverse {L H : GroupScheme (Spec (CommRingCat.of F))}
    (j : L ⟶ H) (q : H ⟶ L) (hq : j ≫ q = 𝟙 L) :
    Function.RightInverse (characterRestrict q) (characterRestrict j) := by
  intro χ
  change ((characterRestrict j).comp (characterRestrict q)) χ = χ
  rw [← characterRestrict_comp, hq, characterRestrict_id]
  rfl

/-- Restriction to a rational Levi is bijective on rational characters. -/
private theorem characterRestrict_bijective_of_levi
    {l : M ⟶ P} (hl : IsRationalLeviSubgroup l) : Function.Bijective (characterRestrict l) := by
  obtain ⟨_, _, π, _, _, hπ, _⟩ := hl.exists_unipotentRadical_retraction
  exact ⟨characterRestrict_injective_of_levi hl, (characterRestrict_rightInverse l π hπ).surjective⟩


end Langlands.Global.AdelicGroupPoints

/-! ## Regular parameters exist -/

namespace Langlands.GroupScheme.ParabolicRootPresentation

open Set
open Langlands.Global.AdelicGroupPoints Langlands.Plancherel Langlands.LinearAlgebra

variable {F : Type u} [Field F]
  {G P M : GroupScheme (Spec (CommRingCat.of F))}
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M} (r : ParabolicRootPresentation p l a)


variable
  [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
  [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
  (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)

private theorem parameterRealPart_surjective :
    Function.Surjective (parameterRealPart F P) := by
  let f : RealCharacterParameter F P →ₗ[ℝ] ComplexCharacterParameter F P :=
    AlgebraTensorModule.map Complex.ofRealCLM.toLinearMap LinearMap.id
  have hf : (parameterRealPart F P).comp f = LinearMap.id := by
    apply AlgebraTensorModule.ext
    intro s χ
    change (s : ℂ).re ⊗ₜ[ℤ] χ = s ⊗ₜ[ℤ] χ
    rw [Complex.ofReal_re]
  exact fun y => ⟨f y, LinearMap.congr_fun hf y⟩

private theorem realParameterRestriction_surjective
    (hl : IsRationalLeviSubgroup l) (ha : IsSplitComponent a) :
    Function.Surjective (realParameterRestriction (F := F) (a ≫ l)) := by
  let f := (characterRestrict (a ≫ l)).toIntLinearMap
  have hf : Function.Surjective (f.baseChange ℚ) := by
    have hs₁ := LinearMap.baseChange_surjective ℚ
      (g := (characterRestrict l).toIntLinearMap)
      (characterRestrict_bijective_of_levi hl).surjective
    have hs₂ := ha.rationalCharacterRestrictRat_surjective hl.isConnectedReductive
    change Function.Surjective (((characterRestrict (a ≫ l)).toIntLinearMap).baseChange ℚ)
    rw [characterRestrict_comp]
    change Function.Surjective (((characterRestrict a).toIntLinearMap.comp
      (characterRestrict l).toIntLinearMap).baseChange ℚ)
    rw [LinearMap.baseChange_comp]
    exact hs₂.comp hs₁
  intro y
  obtain ⟨x, hx⟩ := (LinearMap.baseChange_surjective ℝ hf)
    ((rationalRealTensorEquiv (characterLattice A)).symm y)
  refine ⟨rationalRealTensorEquiv (rationalCharacters P) x, ?_⟩
  have hnat := LinearMap.congr_fun (rationalRealTensorEquiv_naturality f) x
  change (rationalRealTensorEquiv (characterLattice A)) ((f.baseChange ℚ).baseChange ℝ x) =
    (f.baseChange ℝ) (rationalRealTensorEquiv (rationalCharacters P) x) at hnat
  change (f.baseChange ℝ) (rationalRealTensorEquiv (rationalCharacters P) x) = y
  rw [← hnat, hx, LinearEquiv.apply_symm_apply]

/-- Each regularity threshold is achieved by a complex character parameter. -/
private theorem exists_regularParameter (R : ℝ) :
    ∃ lam : ComplexCharacterParameter F P, r.IsRegularParameter hA hT R lam := by
  let : Module.Finite ℤ (characterLattice A) := hA.finite_characterLattice
  let : FiniteDimensional ℝ (RealTorusSpace.Vstar A) :=
    inferInstanceAs (Module.Finite ℝ (ℝ ⊗[ℤ] characterLattice A))
  let B := weylInducedCharacterForm hA hT r.data.f r.data.i
  have hB : B.Nondegenerate :=
    weylInducedCharacterForm_nondegenerate hA hT r.data.f r.data.i
  let s := max R 0 + 1
  obtain ⟨v, hv⟩ := (B.toDual hB).surjective (s • r.splitComponentEvaluation)
  obtain ⟨u, hu⟩ := realParameterRestriction_surjective
    r.isCompatible.levi r.isCompatible.splitComponent v
  obtain ⟨lam, hlam⟩ := parameterRealPart_surjective u
  refine ⟨lam, ?_⟩
  rintro α ⟨hne, β, hβ, rfl⟩
  have hroot := (r.restrict_positive_eq_zero_or_mem hβ).resolve_left hne
  have hone : (1 : ℤ) ≤ latticePairing A (r.data.f ≫ β) r.splitComponentCocharacter := by
    have hpos := hroot.2
    omega
  have hone' : (1 : ℝ) ≤ latticePairing A (r.data.f ≫ β) r.splitComponentCocharacter := by
    exact_mod_cast hone
  have hs : 0 ≤ s := (le_max_right R 0).trans (le_add_of_nonneg_right zero_le_one)
  change R < B (realParameterRestriction (a ≫ l) (parameterRealPart F P lam))
    ((1 : ℝ) ⊗ₜ[ℤ] (r.data.f ≫ β))
  rw [hlam, hu, ← LinearMap.BilinForm.toDual_def hB, hv, LinearMap.smul_apply,
    r.splitComponentEvaluation_tmul, one_mul, smul_eq_mul]
  calc
    R < s := (le_max_left R 0).trans_lt (lt_add_of_pos_right _ zero_lt_one)
    _ ≤ _ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hone' hs


end Langlands.GroupScheme.ParabolicRootPresentation

/-! ## A complexified real chart of `X^*(P) ⊗ ℂ` -/

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme

section Chart

variable {F : Type u} [Field F] (P : GroupScheme (Spec (CommRingCat.of F)))

/-- The inclusion `X^*(P) ⊗ ℝ → X^*(P) ⊗ ℂ`, `t ⊗ χ ↦ t ⊗ χ`. -/
def realToComplexParameter : RealCharacterParameter F P →ₗ[ℝ] ComplexCharacterParameter F P :=
  AlgebraTensorModule.map Complex.ofRealCLM.toLinearMap LinearMap.id

theorem realToComplexParameter_tmul (t : ℝ) (χ : rationalCharacters P) :
    realToComplexParameter P (t ⊗ₜ[ℤ] χ) = (t : ℂ) ⊗ₜ[ℤ] χ := rfl

/-- `imu` is `i` times the complexification of `mu`. -/
theorem imaginaryParameter_eq_I_smul (mu : RealCharacterParameter F P) :
    imaginaryParameter F P mu = Complex.I • realToComplexParameter P mu := by
  induction mu using TensorProduct.inductionOn with
  | tmul t χ =>
    rw [realToComplexParameter_tmul, TensorProduct.smul_tmul']
    show (LinearMap.toSpanSingleton ℝ ℂ Complex.I t) ⊗ₜ[ℤ] χ = _
    rw [LinearMap.toSpanSingleton_apply, Complex.real_smul, smul_eq_mul, mul_comm]
  | add x y hx hy => rw [map_add, map_add, hx, hy, smul_add]

theorem cancelBaseChange_one_tmul (y : RealCharacterParameter F P) :
    AlgebraTensorModule.cancelBaseChange ℤ ℝ ℂ ℂ (rationalCharacters P) ((1 : ℂ) ⊗ₜ[ℝ] y) =
      realToComplexParameter P y := by
  induction y using TensorProduct.inductionOn with
  | tmul t χ =>
    rw [AlgebraTensorModule.cancelBaseChange_tmul, realToComplexParameter_tmul,
      Complex.real_smul, mul_one]
  | add x y hx hy => rw [tmul_add, map_add, map_add, hx, hy]

variable {P}

/-- The complex chart `ℂⁿ ≃ X^*(P) ⊗ ℂ` obtained from real coordinates `e : ℝⁿ ≃ X^*(P) ⊗ ℝ`:
`z ↦ ∑ t, z t • e (Pi.single t 1)`. -/
def realChart {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P) :
    (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P :=
  (((Module.Basis.ofEquivFun e.symm).baseChange ℂ).map
    (AlgebraTensorModule.cancelBaseChange ℤ ℝ ℂ ℂ (rationalCharacters P))).equivFun.symm

theorem realChart_apply {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P)
    (z : Fin n → ℂ) :
    realChart e z = ∑ t, z t • realToComplexParameter P (e (Pi.single t 1)) := by
  simp [realChart, Module.Basis.equivFun_symm_apply, cancelBaseChange_one_tmul]

theorem realChart_ofReal {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P)
    (x : Fin n → ℝ) : realChart e (fun t => (x t : ℂ)) = realToComplexParameter P (e x) := by
  rw [realChart_apply]
  have hx : x = ∑ t, x t • (Pi.single t 1 : Fin n → ℝ) := by
    ext t'
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hx]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_smul, map_smul]
  exact Complex.coe_smul (x t) _

theorem realChart_I_mul {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P)
    (x : Fin n → ℝ) :
    realChart e (fun t => (x t : ℂ) * Complex.I) = imaginaryParameter F P (e x) := by
  have h1 : (fun t => (x t : ℂ) * Complex.I) = Complex.I • fun t => (x t : ℂ) := by
    funext t
    simp [mul_comm]
  rw [h1, map_smul, realChart_ofReal, imaginaryParameter_eq_I_smul]

/-- Imaginary points of the chart are imaginary parameters. -/
theorem realChart_mem_range_imaginary {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P)
    (s : Fin n → ℂ) (hs : ∀ t, (s t).re = 0) :
    ∃ mu, realChart e s = imaginaryParameter F P mu := by
  refine ⟨e (fun t => (s t).im), ?_⟩
  rw [← realChart_I_mul]
  congr 1
  funext t
  apply Complex.ext <;> simp [hs t]

/-- Imaginary parameters are imaginary points of the chart. -/
theorem realChart_symm_imaginary_re {n : ℕ}
    (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P) (mu : RealCharacterParameter F P)
    (t : Fin n) :
    ((realChart e).symm (imaginaryParameter F P mu) t).re = 0 := by
  have h1 : imaginaryParameter F P mu = realChart e (fun t => (e.symm mu t : ℂ) * Complex.I) := by
    rw [realChart_I_mul, LinearEquiv.apply_symm_apply]
  rw [h1, LinearEquiv.symm_apply_apply]
  simp

end Chart

section Roots

variable {F : Type u} [Field F]
  {G P M : GroupScheme (Spec (CommRingCat.of F))} {A : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] {p : P ⟶ G} {l : M ⟶ P}
  {a : A.toGrp ⟶ M} (r : ParabolicRootPresentation p l a)
  [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
  [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
  (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)

/-- The complex root functional restricts to the real one on `X^*(P) ⊗ ℝ`. -/
theorem rootFunctional_realToComplexParameter (β : characterLattice A)
    (y : RealCharacterParameter F P) :
    r.rootFunctional hA hT β (realToComplexParameter P y) =
      (r.realRootFunctional hA hT β y : ℂ) := by
  induction y using TensorProduct.inductionOn with
  | tmul t χ =>
    rw [realToComplexParameter_tmul, ParabolicRootPresentation.rootFunctional_tmul]
    have h1 : (t ⊗ₜ[ℤ] χ : RealCharacterParameter F P) = t • ((1 : ℝ) ⊗ₜ[ℤ] χ) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h1, map_smul, smul_eq_mul, Complex.ofReal_mul]
  | add x y hx hy => simp only [map_add, hx, hy, Complex.ofReal_add]

/-- The real root functional of a root in the unipotent radical is not zero. -/
theorem exists_realRootFunctional_ne_zero [LocallyOfFiniteType G.X.hom] {α : characterLattice A}
    (hα : α ∈ r.unipotentRoots)
    {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P) :
    ∃ x : Fin n → ℝ, r.realRootFunctional hA hT α (e x) ≠ 0 := by
  obtain ⟨lam, hlam⟩ := r.exists_regularParameter hA hT 0
  refine ⟨e.symm (parameterRealPart F P lam), ?_⟩
  rw [LinearEquiv.apply_symm_apply]
  exact (hlam α hα).ne'

end Roots

end Langlands.Global.AdelicGroupPoints

/-! ## The reduction -/

namespace Langlands.Global

open Set
open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic Langlands.Analysis.Meromorphic.ImaginaryHyperplane

/-- The reduction of the unitarity statement as a proposition: the isometry at imaginary points
of holomorphy (Mœglin–Waldspurger IV.3.12, first step), the positivity of the inner product on
`A^2_P` and the root-hyperplane singularities of intertwining operators (Bernstein–Lapid,
Theorem 2.3 (6)) imply holomorphy and unitarity of `M(w, λ)` on the imaginary axis. -/
def IntertwiningImaginaryUnitarityReductionStatement : Prop :=
  IntertwiningImaginaryIsometryStatement → InducedInnerProductGramStatement →
    IntertwiningRootHyperplaneStatement.{0} → IntertwiningImaginaryUnitarityStatement

/-- **Holomorphy and unitarity of `M(w, λ)` on the imaginary axis from the isometry identity,
the positivity of the inner product and the root-hyperplane singularities** (Mœglin–Waldspurger
IV.3.12; Lapid 2011, p.312 and pp.328–329). -/
theorem intertwiningImaginaryUnitarity_of_inputs
    (hU : IntertwiningImaginaryIsometryStatement) (hG : InducedInnerProductGramStatement)
    (hRH : IntertwiningRootHyperplaneStatement.{0}) :
    IntertwiningImaginaryUnitarityStatement := by
  intro F _ _ G P M U P' M' U' A _ _ _ _ _ _ _ _ _ _ _ p _ iU l _ a r _ _ _ hA hT p' _ iU' l' _
    π' w cw hGred hiU hp' hiU' hl' hmul hπ' hW K hK hK' N d rho hsmooth hcalc hKmax hrho
    μM _ μM' _ hμM hμM' n e e' hee' β β' hβc hβs hβ1 hβ'c hβ's hβ'1 k m v ψ coeff DM hv hψ
    hcoeff hexp
  classical
  have : LocallyOfFiniteType P.X.hom :=
    IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
  have : LocallyOfFiniteType P'.X.hom :=
    IsClosedSubgroup.locallyOfFiniteType (j := p') ‹IsClosedImmersion p'.hom.hom.left›
  set e₀ : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P := realChart e with he₀
  -- For each `j`, a representation of `M(w, λ)(v j)` holomorphic near the imaginary axis.
  have hj : ∀ j : Fin k, ∃ (c : Fin m → (Fin n → ℂ) → ℂ) (D' : Set (Fin n → ℂ)),
      {s | ∀ t, (s t).re = 0} ⊆ D' ∧ (∀ i, IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) (c i) D') ∧
      ∀ s ∈ e₀ ⁻¹' DM ∩ D', ∀ g, ∑ i, c i s * ψ j i g = ∑ i, coeff j i (e₀ s) * ψ j i g := by
    intro j
    refine exists_holomorphic_on_imaginary_of_isometry (ψ j)
      (fun i i' => inducedInnerProduct K hK'.isCompact p' l' μM' e' β' (ψ j i) (ψ j i'))
      (fun x => hG F G P' M' U' p' iU' l' hGred hp' hiU' hl' hmul K hK' rho hsmooth hcalc μM' e'
        β' hβ'c hβ's hβ'1 m (ψ j) (hψ j) x)
      (fun i s => coeff j i (e₀ s)) (fun i => (hcoeff j i).2 n e₀)
      (inducedInnerProduct K hK.isCompact p l μM e β (v j) (v j)) ?_ ?_
    · intro c D' hc hagree s hsD' hsre
      obtain ⟨mu, hmu⟩ := realChart_mem_range_imaginary e s hsre
      have hmu' : e₀ s = imaginaryParameter F P mu := hmu
      have hiso := hU F G P M U P' M' U' A p iU l a r hA hT p' iU' l' π' w cw hGred hiU hp' hiU'
        hl' hmul hπ' hW K hK hK' rho hsmooth hcalc hKmax hrho μM μM' hμM hμM' e e' hee' β β'
        hβc hβs hβ1 hβ'c hβ's hβ'1 1 m (fun _ => v j) (fun _ => ψ j) (fun _ => coeff j) DM
        (fun _ => hv j) (fun _ => hψ j) (fun _ => hcoeff j) (fun _ => hexp j)
        (fun _ i => c i ∘ e₀.symm) (e₀.symm ⁻¹' D')
        (fun _ i => isMeromorphicInCoordinatesOn_of_chart e₀ (hc i))
        (fun _ lam hlam g => by
          have h1 := hagree (e₀.symm lam) ⟨by simpa using hlam.1, hlam.2⟩ g
          simpa using h1)
        mu 0 0 (by
          show e₀.symm (imaginaryParameter F P mu) ∈ D'
          rw [← hmu', LinearEquiv.symm_apply_apply]
          exact hsD')
      rw [← hmu'] at hiso
      simpa [gramForm] using hiso
    · intro s₀ hs₀
      obtain ⟨S, mm, W, hS, hWo, hs₀W, hH⟩ := hRH F G P M U P' M' U' A p iU l a r hA hT p' iU'
        l' π' w cw hGred hiU hp' hiU' hl' hmul hπ' hW K hK hK' rho hsmooth hcalc (v j) hKmax
        hrho (hv j).1 m (ψ j) (coeff j) DM (hcoeff j) (hexp j) n e₀ s₀
      refine ⟨S × Fin mm, inferInstance,
        fun x => (r.rootFunctional hA hT x.1.1).comp e₀.toLinearMap, ?_, ?_, W, hWo, hs₀W,
        fun g => ?_⟩
      · intro x y
        simp [he₀, realChart_ofReal, rootFunctional_realToComplexParameter]
      · intro x
        obtain ⟨y, hy⟩ := exists_realRootFunctional_ne_zero r hA hT (hS x.1.2) e
        refine ⟨y, ?_⟩
        simpa [he₀, realChart_ofReal, rootFunctional_realToComplexParameter] using hy
      · obtain ⟨h, hhd, hheq⟩ := hH g
        refine ⟨h, hhd, fun s hsW hsD => ?_⟩
        rw [hheq s hsW hsD]
        congr 1
        rw [Fintype.prod_prod_type]
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, map_sub, Fin.prod_const,
          Finset.prod_pow]
        rw [Finset.prod_coe_sort S
          (fun x => r.rootFunctional hA hT x (e₀ s) - r.rootFunctional hA hT x (e₀ s₀))]
  choose c D' hslice hmero hagree using hj
  set DM' : Set (ComplexCharacterParameter F P) := e₀.symm ⁻¹' ⋂ j, D' j with hDM'
  have hrange : Set.range (imaginaryParameter F P) ⊆ DM' := by
    rintro _ ⟨mu, rfl⟩
    exact mem_iInter.mpr fun j => hslice j fun t => realChart_symm_imaginary_re e mu t
  have hmero' : ∀ j i, IsMeromorphicInCoordinatesOn (c j i ∘ e₀.symm) DM' := by
    intro j i
    have hopen : IsOpen (⋂ j, D' j) := isOpen_iInter_of_finite fun j' => (hmero j' i).1
    have hdense : Dense (⋂ j, D' j) :=
      dense_iInter_of_isOpen (fun j' => (hmero j' i).1) fun j' => (hmero j' i).2.1
    exact isMeromorphicInCoordinatesOn_of_chart e₀
      (isMeromorphicOn_restrict (hmero j i) hopen hdense (iInter_subset _ j))
  have hagree' : ∀ j, ∀ lam ∈ DM ∩ DM', ∀ g,
      ∑ i, (c j i ∘ e₀.symm) lam * ψ j i g = ∑ i, coeff j i lam * ψ j i g := by
    intro j lam hlam g
    have h1 := hagree j (e₀.symm lam) ⟨by simpa using hlam.1, mem_iInter.mp hlam.2 j⟩ g
    simpa using h1
  refine ⟨fun j i => c j i ∘ e₀.symm, DM', hrange, hmero', hagree', fun mu j j' => ?_⟩
  exact hU F G P M U P' M' U' A p iU l a r hA hT p' iU' l' π' w cw hGred hiU hp' hiU' hl' hmul
    hπ' hW K hK hK' rho hsmooth hcalc hKmax hrho μM μM' hμM hμM' e e' hee' β β' hβc hβs hβ1
    hβ'c hβ's hβ'1 k m v ψ coeff DM hv hψ hcoeff hexp (fun j i => c j i ∘ e₀.symm) DM' hmero'
    hagree' mu j j' (hrange ⟨mu, rfl⟩)

/-- The reduction, in the form of the proposition
`IntertwiningImaginaryUnitarityReductionStatement`. -/
theorem intertwiningImaginaryUnitarityReduction :
    IntertwiningImaginaryUnitarityReductionStatement :=
  fun hU hG hRH => intertwiningImaginaryUnitarity_of_inputs hU hG hRH

end Langlands.Global
