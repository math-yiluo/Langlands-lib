import Langlands.Shimura.PEL.TraceSimilitudesNaturality
import Mathlib.Topology.Algebra.Group.Units

/-! # Topology of regular-module trace similitudes -/

noncomputable section

universe u v w z t

namespace Langlands.Shimura.PEL

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
    [TopologicalSpace R] [TopologicalSpace A]
    (ψ : LinearMap.BilinForm R A)

/-- Observe both operator directions pointwise, together with the unit multiplier. -/
def regularBilinearCoordinates (g : bilinearSimilitudes A ψ) :
    ((A → A) × (A → A)) × Rˣ :=
  ((g.val.1, g.val.1.symm), g.val.2)

/-- The initial topology for the actual forward and inverse operators and multiplier. -/
@[instance_reducible] def regularBilinearTopology : TopologicalSpace (bilinearSimilitudes A ψ) :=
  TopologicalSpace.induced (regularBilinearCoordinates ψ) inferInstance

local instance : TopologicalSpace (bilinearSimilitudes A ψ) := regularBilinearTopology ψ

theorem continuous_regularBilinear_apply (x : A) :
    Continuous (fun g : bilinearSimilitudes A ψ => g.val.1 x) :=
  (continuous_apply x).comp
    ((continuous_fst.comp continuous_fst).comp
      (show Continuous (regularBilinearCoordinates ψ) from continuous_induced_dom))

theorem continuous_regularBilinear_symm_apply (x : A) :
    Continuous (fun g : bilinearSimilitudes A ψ => g.val.1.symm x) :=
  (continuous_apply x).comp
    ((continuous_snd.comp continuous_fst).comp
      (show Continuous (regularBilinearCoordinates ψ) from continuous_induced_dom))

theorem continuous_regularBilinear_multiplier :
    Continuous (bilinearSimilitudes.multiplier (B := A) ψ) := by
  have hc : Continuous (regularBilinearCoordinates ψ) := continuous_induced_dom
  exact hc.snd

variable (σ : AlgebraInvolution R A) (hψ : ψ.Nondegenerate)
    (hadj : ∀ b x y : A, ψ (x * b) y = ψ x (y * σ b))

/-- The regular-module algebraic comparison is a homeomorphism for the independently
specified operator topology, and preserves the group law. -/
def algebraicBilinearContinuousEquiv [ContinuousMul A] :
    σ.similitudesᵐᵒᵖ ≃ₜ* bilinearSimilitudes A ψ where
  toMulEquiv := algebraicBilinearEquiv σ ψ hψ hadj
  continuous_toFun := by
    have hu : Continuous (fun g : σ.similitudesᵐᵒᵖ => (g.unop.val.1 : A)) :=
      Units.continuous_val.comp (continuous_fst.comp
        (continuous_subtype_val.comp MulOpposite.continuous_unop))
    have hi : Continuous (fun g : σ.similitudesᵐᵒᵖ => (↑((g.unop.val.1)⁻¹) : A)) :=
      Units.continuous_coe_inv.comp (continuous_fst.comp
        (continuous_subtype_val.comp MulOpposite.continuous_unop))
    have hc : Continuous (fun g : σ.similitudesᵐᵒᵖ => g.unop.val.2) :=
      continuous_snd.comp (continuous_subtype_val.comp MulOpposite.continuous_unop)
    apply continuous_induced_rng.mpr
    exact ((continuous_pi fun x => continuous_const.mul hu).prodMk
      (continuous_pi fun x => continuous_const.mul hi)).prodMk hc
  continuous_invFun := by
    have hu : Continuous (fun g : bilinearSimilitudes A ψ => selfEquivUnit g.val.1) :=
      Units.continuous_iff.mpr
        ⟨continuous_regularBilinear_apply ψ 1,
          continuous_regularBilinear_symm_apply ψ 1⟩
    exact MulOpposite.continuous_op.comp
      ((hu.prodMk (continuous_regularBilinear_multiplier ψ)).subtype_mk _)

include σ hψ hadj in
/-- The operator topology makes the regular similitude subgroup a topological group. -/
theorem regularBilinear_isTopologicalGroup [ContinuousMul A] [ContinuousMul R] :
    IsTopologicalGroup (bilinearSimilitudes A ψ) :=
  (algebraicBilinearContinuousEquiv ψ σ hψ hadj).symm.toHomeomorph.isInducing.isTopologicalGroup
    (algebraicBilinearContinuousEquiv ψ σ hψ hadj).symm.toMulEquiv

/-- In the regular module the action is jointly continuous, despite the pointwise
specification of the operator topology. -/
theorem continuous_regularBilinear_action [ContinuousMul A] :
    Continuous (fun p : bilinearSimilitudes A ψ × A => p.1.val.1 p.2) := by
  have h : Continuous (fun p : bilinearSimilitudes A ψ × A =>
      p.2 * p.1.val.1 1) :=
    continuous_snd.mul ((continuous_regularBilinear_apply ψ 1).comp continuous_fst)
  simpa only [← selfEquiv_apply] using h

end Langlands.Shimura.PEL

namespace Langlands.Shimura.CentralSimpleUnitaryData

open NumberField Module _root_.Algebra
open scoped TensorProduct

variable {E : Type u} {K : Type v} {A : Type w}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field K] [NumberField K] [IsTotallyComplex K]
    [Algebra E K] [IsQuadraticExtension E K]
    [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
    [Algebra ℚ A] [IsScalarTower ℚ E A]
    {n : ℕ} (D : CentralSimpleUnitaryData E K A n) (β : Aˣ)
    (hβ : D.involution (β : A) = -(β : A))

/-- A named carrier for the actual inverse-unit trace-form bilinear subgroup,
with its canonical tensor-module operator topology. -/
def HarrisBilinearPoints (S : Type z) [CommRing S] [Algebra ℚ S] : Type (max w z) :=
  D.harrisBilinearSimilitudes β hβ S

namespace HarrisBilinearPoints

variable (S : Type z) [CommRing S] [Algebra ℚ S]

instance : Group (D.HarrisBilinearPoints β hβ S) :=
  inferInstanceAs (Group (D.harrisBilinearSimilitudes β hβ S))

instance [TopologicalSpace S] : TopologicalSpace (D.HarrisBilinearPoints β hβ S) :=
  letI : TopologicalSpace (S ⊗[ℚ] A) := moduleTopology S (S ⊗[ℚ] A)
  PEL.regularBilinearTopology ((D.skewTwist β hβ).tracePairingBaseChange S β⁻¹)

instance [TopologicalSpace S] [IsTopologicalRing S] :
    IsTopologicalGroup (D.HarrisBilinearPoints β hβ S) := by
  let : Module.Finite E A := Module.Finite.of_basis D.totallyRealBasis
  let : Module.Finite ℚ A := FiniteDimensional.trans ℚ E A
  let : TopologicalSpace (S ⊗[ℚ] A) := moduleTopology S (S ⊗[ℚ] A)
  let : IsTopologicalRing (S ⊗[ℚ] A) := IsModuleTopology.isTopologicalRing S _
  exact PEL.regularBilinear_isTopologicalGroup
    ((D.skewTwist β hβ).tracePairingBaseChange S β⁻¹)
    (D.toSecondKindInvolution.rationalInvolution.baseChange S)
    ((D.skewTwist β hβ).tracePairingBaseChange_nondegenerate S β⁻¹)
    (D.skewTwist_tracePairingBaseChange_right β hβ S)

/-- The same actual multiplier, now as a continuous group character. -/
def multiplier [TopologicalSpace S] : D.HarrisBilinearPoints β hβ S →ₜ* Sˣ where
  toMonoidHom := PEL.bilinearSimilitudes.multiplier
    ((D.skewTwist β hβ).tracePairingBaseChange S β⁻¹)
  continuous_toFun := by
    let : TopologicalSpace (S ⊗[ℚ] A) := moduleTopology S (S ⊗[ℚ] A)
    exact PEL.continuous_regularBilinear_multiplier _

omit [IsScalarTower E K A] in
/-- Evaluation of the actual forward operator is continuous. -/
theorem continuous_apply [TopologicalSpace S] (x : S ⊗[ℚ] A) :
    let : TopologicalSpace (S ⊗[ℚ] A) := moduleTopology S (S ⊗[ℚ] A)
    Continuous (fun g : D.HarrisBilinearPoints β hβ S => g.val.1 x) := by
  let : TopologicalSpace (S ⊗[ℚ] A) := moduleTopology S (S ⊗[ℚ] A)
  exact PEL.continuous_regularBilinear_apply _ x

omit [IsScalarTower E K A] in
/-- Evaluation of the actual inverse operator is continuous. -/
theorem continuous_symm_apply [TopologicalSpace S] (x : S ⊗[ℚ] A) :
    let : TopologicalSpace (S ⊗[ℚ] A) := moduleTopology S (S ⊗[ℚ] A)
    Continuous (fun g : D.HarrisBilinearPoints β hβ S => g.val.1.symm x) := by
  let : TopologicalSpace (S ⊗[ℚ] A) := moduleTopology S (S ⊗[ℚ] A)
  exact PEL.continuous_regularBilinear_symm_apply _ x

/-- The regular trace-form action on the tensor algebra is jointly continuous. -/
theorem continuous_action [TopologicalSpace S] [IsTopologicalRing S] :
    let : TopologicalSpace (S ⊗[ℚ] A) := moduleTopology S (S ⊗[ℚ] A)
    Continuous (fun p : D.HarrisBilinearPoints β hβ S × (S ⊗[ℚ] A) =>
      p.1.val.1 p.2) := by
  let : Module.Finite E A := Module.Finite.of_basis D.totallyRealBasis
  let : Module.Finite ℚ A := FiniteDimensional.trans ℚ E A
  let : TopologicalSpace (S ⊗[ℚ] A) := moduleTopology S (S ⊗[ℚ] A)
  let : IsTopologicalRing (S ⊗[ℚ] A) := IsModuleTopology.isTopologicalRing S _
  exact PEL.continuous_regularBilinear_action _

end HarrisBilinearPoints

/-- The existing Harris comparison with the original involution is a topological
group equivalence for the actual module/units and operator topologies. -/
def harrisTraceSimilitudesContinuousEquiv (S : Type z) [CommRing S] [Algebra ℚ S]
    [TopologicalSpace S] [IsTopologicalRing S] :
    (D.toSecondKindInvolution.rationalInvolution.Points S)ᵐᵒᵖ ≃ₜ*
      D.HarrisBilinearPoints β hβ S := by
  letI : Module.Finite E A := Module.Finite.of_basis D.totallyRealBasis
  letI : Module.Finite ℚ A := FiniteDimensional.trans ℚ E A
  letI : TopologicalSpace (S ⊗[ℚ] A) := moduleTopology S (S ⊗[ℚ] A)
  letI : IsTopologicalRing (S ⊗[ℚ] A) := IsModuleTopology.isTopologicalRing S _
  exact PEL.algebraicBilinearContinuousEquiv
    ((D.skewTwist β hβ).tracePairingBaseChange S β⁻¹)
    (D.toSecondKindInvolution.rationalInvolution.baseChange S)
    ((D.skewTwist β hβ).tracePairingBaseChange_nondegenerate S β⁻¹)
    (D.skewTwist_tracePairingBaseChange_right β hβ S)

@[simp] theorem harrisTraceSimilitudesContinuousEquiv_toMulEquiv
    (S : Type z) [CommRing S] [Algebra ℚ S] [TopologicalSpace S] [IsTopologicalRing S] :
    (D.harrisTraceSimilitudesContinuousEquiv β hβ S).toMulEquiv =
      D.harrisTraceSimilitudesEquiv S β hβ := rfl

@[simp] theorem harrisTraceSimilitudesContinuousEquiv_apply
    (S : Type z) [CommRing S] [Algebra ℚ S] [TopologicalSpace S] [IsTopologicalRing S]
    (g : (D.toSecondKindInvolution.rationalInvolution.Points S)ᵐᵒᵖ)
    (x : S ⊗[ℚ] A) :
    (D.harrisTraceSimilitudesContinuousEquiv β hβ S g).val.1 x =
      x * (g.unop.val.1 : S ⊗[ℚ] A) := rfl

@[simp] theorem harrisTraceSimilitudesContinuousEquiv_multiplier
    (S : Type z) [CommRing S] [Algebra ℚ S] [TopologicalSpace S] [IsTopologicalRing S]
    (g : (D.toSecondKindInvolution.rationalInvolution.Points S)ᵐᵒᵖ) :
    HarrisBilinearPoints.multiplier D β hβ S
        (D.harrisTraceSimilitudesContinuousEquiv β hβ S g) =
      AlgebraInvolution.Points.multiplier
        D.toSecondKindInvolution.rationalInvolution S g.unop := rfl

section Coefficients

variable {S : Type z} {T : Type t}
    [CommRing S] [Algebra ℚ S] [TopologicalSpace S] [IsTopologicalRing S]
    [CommRing T] [Algebra ℚ T] [TopologicalSpace T] [IsTopologicalRing T]

/-- The actual tensor coefficient map on Harris bilinear points is continuous. -/
def harrisTraceSimilitudesContinuousMap (f : S →ₐ[ℚ] T) (hf : Continuous f) :
    D.HarrisBilinearPoints β hβ S →ₜ* D.HarrisBilinearPoints β hβ T where
  toMonoidHom := D.harrisTraceSimilitudesMap β hβ f
  continuous_toFun := by
    let : Module.Finite E A := Module.Finite.of_basis D.totallyRealBasis
    let : Module.Finite ℚ A := FiniteDimensional.trans ℚ E A
    have hp : Continuous ((D.toSecondKindInvolution.rationalInvolution.pointsMap f).op) :=
      MulOpposite.continuous_op.comp
        ((D.toSecondKindInvolution.rationalInvolution.continuous_pointsMap f hf).comp
          MulOpposite.continuous_unop)
    exact (D.harrisTraceSimilitudesContinuousEquiv β hβ T).continuous.comp
      (hp.comp (D.harrisTraceSimilitudesContinuousEquiv β hβ S).symm.continuous)

@[simp] theorem harrisTraceSimilitudesContinuousMap_toMonoidHom
    (f : S →ₐ[ℚ] T) (hf : Continuous f) :
    (D.harrisTraceSimilitudesContinuousMap β hβ f hf).toMonoidHom =
      D.harrisTraceSimilitudesMap β hβ f := rfl

@[simp] theorem harrisTraceSimilitudesContinuousMap_apply
    (f : S →ₐ[ℚ] T) (hf : Continuous f) (g : D.HarrisBilinearPoints β hβ S)
    (x : T ⊗[ℚ] A) :
    (D.harrisTraceSimilitudesContinuousMap β hβ f hf g).val.1 x =
      x * AlgebraInvolution.changeCoefficients f (g.val.1 1) := rfl

/-- Continuity enriches the same natural algebraic comparison square. -/
theorem harrisTraceSimilitudesContinuousEquiv_natural
    (f : S →ₐ[ℚ] T) (hf : Continuous f)
    (g : (D.toSecondKindInvolution.rationalInvolution.Points S)ᵐᵒᵖ) :
    D.harrisTraceSimilitudesContinuousMap β hβ f hf
        (D.harrisTraceSimilitudesContinuousEquiv β hβ S g) =
      D.harrisTraceSimilitudesContinuousEquiv β hβ T
        ((D.toSecondKindInvolution.rationalInvolution.pointsMap f).op g) :=
  D.harrisTraceSimilitudesEquiv_natural β hβ f g

@[simp] theorem harrisTraceSimilitudesContinuousMap_id :
    D.harrisTraceSimilitudesContinuousMap β hβ (AlgHom.id ℚ S) continuous_id =
      ContinuousMonoidHom.id (D.HarrisBilinearPoints β hβ S) := by
  ext g
  exact DFunLike.congr_fun (D.harrisTraceSimilitudesMap_id β hβ) g

theorem harrisTraceSimilitudesContinuousMap_comp {U : Type*}
    [CommRing U] [Algebra ℚ U] [TopologicalSpace U] [IsTopologicalRing U]
    (f : S →ₐ[ℚ] T) (hf : Continuous f) (k : T →ₐ[ℚ] U) (hk : Continuous k) :
    D.harrisTraceSimilitudesContinuousMap β hβ (k.comp f) (hk.comp hf) =
      (D.harrisTraceSimilitudesContinuousMap β hβ k hk).comp
        (D.harrisTraceSimilitudesContinuousMap β hβ f hf) := by
  ext g
  exact DFunLike.congr_fun (D.harrisTraceSimilitudesMap_comp β hβ f k) g

/-- The continuous coefficient maps still preserve the actual rational diagonal. -/
theorem harrisTraceSimilitudesContinuousMap_diagonal
    (f : S →ₐ[ℚ] T) (hf : Continuous f)
    (g : PEL.bilinearSimilitudes A ((D.skewTwist β hβ).tracePairing β⁻¹)) :
    D.harrisTraceSimilitudesContinuousMap β hβ f hf
        (D.harrisBilinearDiagonal β hβ S g) =
      D.harrisBilinearDiagonal β hβ T g :=
  D.harrisTraceSimilitudesMap_diagonal β hβ f g

end Coefficients

/-- Actual finite adelic points have the same topological comparison. -/
def harrisFiniteAdelicTraceSimilitudesContinuousEquiv :
    D.toSecondKindInvolution.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ ≃ₜ*
      D.HarrisBilinearPoints β hβ (Langlands.Global.FiniteAdeles ℚ) :=
  D.harrisTraceSimilitudesContinuousEquiv β hβ (Langlands.Global.FiniteAdeles ℚ)

/-- Actual finite-adele evaluation gives a continuous homomorphism into the
bilinear points of the actual finite completion. -/
def harrisFiniteLocalTraceSimilitudesContinuousMap (v : Langlands.Global.FinitePlace ℚ) :
    D.HarrisBilinearPoints β hβ (Langlands.Global.FiniteAdeles ℚ) →ₜ*
      D.HarrisBilinearPoints β hβ (Langlands.Global.FiniteCompletion ℚ v) :=
  D.harrisTraceSimilitudesContinuousMap β hβ (AlgebraInvolution.finiteEvaluation v)
    (AlgebraInvolution.continuous_finiteEvaluation v)

theorem harrisFiniteLocalTraceSimilitudesContinuousEquiv_natural
    (v : Langlands.Global.FinitePlace ℚ)
    (g : D.toSecondKindInvolution.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ) :
    D.harrisFiniteLocalTraceSimilitudesContinuousMap β hβ v
        (D.harrisFiniteAdelicTraceSimilitudesContinuousEquiv β hβ g) =
      D.harrisTraceSimilitudesContinuousEquiv β hβ
        (Langlands.Global.FiniteCompletion ℚ v)
        ((D.toSecondKindInvolution.rationalInvolution.pointsMap
          (AlgebraInvolution.finiteEvaluation v)).op g) :=
  D.harrisTraceSimilitudesContinuousEquiv_natural β hβ _ _ g

theorem harrisFiniteLocalTraceSimilitudesContinuousMap_diagonal
    (v : Langlands.Global.FinitePlace ℚ)
    (g : PEL.bilinearSimilitudes A ((D.skewTwist β hβ).tracePairing β⁻¹)) :
    D.harrisFiniteLocalTraceSimilitudesContinuousMap β hβ v
        (D.harrisBilinearDiagonal β hβ (Langlands.Global.FiniteAdeles ℚ) g) =
      D.harrisBilinearDiagonal β hβ (Langlands.Global.FiniteCompletion ℚ v) g :=
  D.harrisTraceSimilitudesContinuousMap_diagonal β hβ _ _ g

end Langlands.Shimura.CentralSimpleUnitaryData
