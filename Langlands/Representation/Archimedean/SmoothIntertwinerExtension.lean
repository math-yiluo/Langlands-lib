import Langlands.Representation.Archimedean.HilbertIntertwinerEvaluation
import Langlands.Representation.Archimedean.SmoothDerivativeTopology

/-! # Smooth extension of bounded intertwiners along a split restriction -/

noncomputable section

open scoped Manifold ContDiff

set_option autoImplicit false
set_option maxHeartbeats 60000
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.SmoothIntertwinerExtension

universe ug ua uG uA uE uH

variable {𝔤 : Type ug} [NormedAddCommGroup 𝔤] [NormedSpace ℝ 𝔤]
  {𝔞 : Type ua} [NormedAddCommGroup 𝔞] [NormedSpace ℝ 𝔞]
  {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace 𝔤 G]
  {A : Type uA} [Group A] [TopologicalSpace A] [ChartedSpace 𝔞 A]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {H : Type uH} [NormedAddCommGroup H] [NormedSpace ℂ H]
  (π : G →* (E →L[ℂ] E)) (σ : A →* (H →L[ℂ] H))
  (i : G →* A) (p : A →* G) (c : A → A)

local notation "I" => 𝓘(ℝ, 𝔤)
local notation "J" => 𝓘(ℝ, 𝔞)
local notation "W" => boundedIntertwiners π (σ.comp i)

variable (hcomm : ∀ g h, Commute (c g) (i h))

private def orbitOperator (T : W) (g : A) : W :=
  ⟨(σ (c g)).comp T.val, fun h x => by
    change σ (c g) (T.val (π h x)) = σ (i h) (σ (c g) (T.val x))
    rw [T.property h x]
    change (σ (c g) * σ (i h)) (T.val x) = (σ (i h) * σ (c g)) (T.val x)
    rw [← map_mul, ← map_mul, (hcomm g h).eq]⟩

omit [TopologicalSpace G] [TopologicalSpace A] in
private theorem orbitOperator_one (hc₁ : c 1 = 1) (T : W) :
    orbitOperator π σ i c hcomm T 1 = T := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  change σ (c 1) (T.val x) = T.val x
  rw [hc₁, map_one]
  rfl

variable {x₀ : E} (L : H →L[ℂ] ↥(boundedIntertwiners π (σ.comp i)))
  (hL : ∀ T : ↥(boundedIntertwiners π (σ.comp i)), L (T.val x₀) = T)
  (hc : ContMDiff 𝓘(ℝ, 𝔞) 𝓘(ℝ, 𝔞) ∞ c)
  (hp : ContMDiff 𝓘(ℝ, 𝔞) 𝓘(ℝ, 𝔤) ∞ (p : A → G))
  (hsplit : ∀ g, c g * i (p g) = g)

omit [TopologicalSpace G] in
include hL hc in
private theorem contMDiff_orbitOperator (T : W) (hT : IsSmoothVector J σ (T.val x₀)) :
    ContMDiff J 𝓘(ℝ, W) ∞ (orbitOperator π σ i c hcomm T) := by
  have he : orbitOperator π σ i c hcomm T =
      (L.restrictScalars ℝ) ∘ orbitMap σ (T.val x₀) ∘ c := by
    funext g
    exact (hL (orbitOperator π σ i c hcomm T g)).symm
  rw [he]
  exact (L.restrictScalars ℝ).contDiff.contMDiff.comp (hT.comp hc)

omit [TopologicalSpace G] [TopologicalSpace A] in
include hsplit in
private theorem orbitMap_eq (T : W) (x : E) :
    orbitMap σ (T.val x) =
      fun g => (orbitOperator π σ i c hcomm T g).val (orbitMap π x (p g)) := by
  funext g
  calc
    σ g (T.val x) = σ (c g * i (p g)) (T.val x) :=
      congrArg (fun a => σ a (T.val x)) (hsplit g).symm
    _ = σ (c g) (T.val (π (p g) x)) := by
      rw [T.property (p g) x, map_mul]
      rfl

private def realOperatorInclusion : W →L[ℝ] E →L[ℝ] H :=
  (ContinuousLinearMap.restrictScalarsL ℂ E H ℝ ℝ).comp
    ((boundedIntertwiners π (σ.comp i)).subtypeL.restrictScalars ℝ)

include hcomm hL hc hp hsplit in
/-- Global smoothness at one sample vector implies global smoothness on all
locally smooth vectors, given a bounded left inverse to evaluation. -/
theorem isSmoothVector_map (T : W) (hT : IsSmoothVector J σ (T.val x₀))
    {x : E} (hx : IsSmoothVector I π x) : IsSmoothVector J σ (T.val x) := by
  change ContMDiff J 𝓘(ℝ, H) ∞ (orbitMap σ (T.val x))
  rw [orbitMap_eq π σ i p c hcomm hsplit T x]
  have hB := contMDiff_orbitOperator π σ i c hcomm L hL hc T hT
  have hU : ContMDiff J 𝓘(ℝ, E) ∞ (orbitMap π x ∘ p) := hx.comp hp
  exact ((realOperatorInclusion π σ i).contDiff.contMDiff.comp hB).clm_apply hU

omit [Group A] in
private theorem mfderiv_apply_operator
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (C : V →L[ℝ] E →L[ℝ] H) {B : A → V} {u : A → E} {a : A}
    (hB : MDifferentiableAt J 𝓘(ℝ, V) B a)
    (hu : MDifferentiableAt J 𝓘(ℝ, E) u a) (X : 𝔞) :
    mfderiv J 𝓘(ℝ, H) (fun g => C (B g) (u g)) a X =
      C (mfderiv J 𝓘(ℝ, V) B a X) (u a) +
        C (B a) (mfderiv J 𝓘(ℝ, E) u a X) := by
  let ev : V × E → H := fun q => C q.1 q.2
  let P : A → V × E := fun g => (B g, u g)
  have hs : ContMDiff (𝓘(ℝ, V).prod 𝓘(ℝ, E)) 𝓘(ℝ, H) ∞ ev :=
    (C.contDiff.contMDiff.comp contMDiff_fst).clm_apply contMDiff_snd
  have he : MDifferentiableAt (𝓘(ℝ, V).prod 𝓘(ℝ, E)) 𝓘(ℝ, H) ev (P a) :=
    hs.mdifferentiableAt (by simp)
  have hP : MDifferentiableAt J (𝓘(ℝ, V).prod 𝓘(ℝ, E)) P a := hB.prodMk hu
  change mfderiv J 𝓘(ℝ, H) (ev ∘ P) a X = _
  rw [mfderiv_comp_apply a he hP, mfderiv_prod_eq_add_apply he]
  have hpair : mfderiv J (𝓘(ℝ, V).prod 𝓘(ℝ, E)) P a =
      (mfderiv J 𝓘(ℝ, V) B a).prod (mfderiv J 𝓘(ℝ, E) u a) :=
    mfderiv_prodMk hB hu
  rw [hpair]
  let l₁ := (ContinuousLinearMap.apply ℝ H (u a)).comp C
  let l₂ := C (B a)
  change Add.add (α := H)
    (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, H) l₁ (B a) (mfderiv J 𝓘(ℝ, V) B a X))
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, H) l₂ (u a) (mfderiv J 𝓘(ℝ, E) u a X)) = _
  rw [ContinuousLinearMap.mfderiv_eq, ContinuousLinearMap.mfderiv_eq]
  rfl

private def orbitOperatorDerivative (T : W) (X : 𝔞) : W :=
  mfderiv J 𝓘(ℝ, W) (orbitOperator π σ i c hcomm T) 1 X

include hL hc hp hsplit in
private theorem lieDerivative_map
    (T : W) (hT : IsSmoothVector J σ (T.val x₀)) (X : 𝔞)
    {x : E} (hx : IsSmoothVector I π x) :
    lieDerivative J σ X (T.val x) =
      (orbitOperatorDerivative π σ i c hcomm T X).val x +
        T.val (lieDerivative I π (mfderiv J I p 1 X) x) := by
  have hB : MDifferentiableAt J 𝓘(ℝ, W) (orbitOperator π σ i c hcomm T) 1 :=
    (contMDiff_orbitOperator π σ i c hcomm L hL hc T hT).mdifferentiableAt (by simp)
  have hu : MDifferentiableAt J 𝓘(ℝ, E) (orbitMap π x ∘ p) 1 :=
    (hx.comp hp).mdifferentiableAt (by simp)
  unfold lieDerivative
  rw [orbitMap_eq π σ i p c hcomm hsplit T x]
  change mfderiv J 𝓘(ℝ, H)
      (fun g => realOperatorInclusion π σ i (orbitOperator π σ i c hcomm T g)
        ((orbitMap π x ∘ p) g)) 1 X = _
  rw [mfderiv_apply_operator (realOperatorInclusion π σ i) hB hu X]
  change (orbitOperatorDerivative π σ i c hcomm T X).val (orbitMap π x (p 1)) +
    (orbitOperator π σ i c hcomm T 1).val (mfderiv J 𝓘(ℝ, E) (orbitMap π x ∘ p) 1 X) = _
  have hc₁ : c 1 = 1 := by simpa only [map_one, mul_one] using hsplit 1
  have h₁ : orbitMap π x (p 1) = x := by
    rw [map_one]
    change π 1 x = x
    rw [map_one]
    rfl
  rw [orbitOperator_one π σ i c hcomm hc₁ T, h₁]
  have hp₁ : MDifferentiableAt J I p 1 := hp.mdifferentiableAt (by simp)
  have hx₁ : MDifferentiableAt I 𝓘(ℝ, E) (orbitMap π x) 1 :=
    hx.mdifferentiableAt (by simp)
  rw [mfderiv_comp_apply_of_eq 1 hx₁ hp₁ p.map_one X]

include hcomm hL hc hp hsplit

/-- The original intertwiner as a map from local to global smooth vectors. -/
def map (T : W) (hT : IsSmoothVector J σ (T.val x₀)) :
    smoothVectors I π →ₗ[ℂ] smoothVectors J σ :=
  (T.val.toLinearMap.comp (smoothVectors I π).subtype).codRestrict (smoothVectors J σ)
    (fun v => isSmoothVector_map π σ i p c hcomm L hL hc hp hsplit T hT v.property)

@[simp]
theorem map_apply (T : W) (hT : IsSmoothVector J σ (T.val x₀)) (v : smoothVectors I π) :
    (map π σ i p c hcomm L hL hc hp hsplit T hT v : H) = T.val v :=
  rfl

variable [LieGroup 𝓘(ℝ, 𝔤) ∞ G] [LieGroup 𝓘(ℝ, 𝔞) ∞ A]

/-- The induced smooth map intertwines the local action and the restricted global action. -/
theorem map_smoothRepresentation (T : W) (hT : IsSmoothVector J σ (T.val x₀))
    (g : G) (v : smoothVectors I π) :
    map π σ i p c hcomm L hL hc hp hsplit T hT (smoothRepresentation I π g v) =
      smoothRepresentation J σ (i g) (map π σ i p c hcomm L hL hc hp hsplit T hT v) :=
  Subtype.ext (T.property g v)

private theorem sample_derivative_isSmooth (hx₀ : IsSmoothVector I π x₀)
    (T : W) (hT : IsSmoothVector J σ (T.val x₀)) (X : 𝔞) :
    IsSmoothVector J σ ((orbitOperatorDerivative π σ i c hcomm T X).val x₀) := by
  have he := lieDerivative_map π σ i p c hcomm L hL hc hp hsplit T hT X hx₀
  rw [eq_sub_of_add_eq he.symm]
  exact (smoothVectors J σ).sub_mem (isSmoothVector_lieDerivative J σ X hT)
    (isSmoothVector_map π σ i p c hcomm L hL hc hp hsplit T hT
      (isSmoothVector_lieDerivative I π _ hx₀))

open DerivativeSmoothVectors

private theorem continuous_word (hx₀ : IsSmoothVector I π x₀) (Xs : List 𝔞)
    (T : W) (hT : IsSmoothVector J σ (T.val x₀)) :
    Continuous (fun v : DerivativeSmoothVectors I π =>
      (smoothIteratedLieDerivative J σ Xs
        (map π σ i p c hcomm L hL hc hp hsplit T hT (toSmooth I π v)) : H)) := by
  induction Xs using List.reverseRecOn generalizing T with
  | nil =>
    exact T.val.continuous.comp (derivativeCLM I π []).continuous
  | append_singleton Xs X ih =>
    let T' := orbitOperatorDerivative π σ i c hcomm T X
    have hT' : IsSmoothVector J σ (T'.val x₀) :=
      sample_derivative_isSmooth π σ i p c hcomm L hL hc hp hsplit hx₀ T hT X
    let Y : 𝔤 := mfderiv J I p 1 X
    let M := map π σ i p c hcomm L hL hc hp hsplit T hT
    let M' := map π σ i p c hcomm L hL hc hp hsplit T' hT'
    have hd (v : smoothVectors I π) :
        smoothLieDerivative J σ X (M v) =
          M' v + M (smoothLieDerivative I π Y v) :=
      Subtype.ext (lieDerivative_map π σ i p c hcomm L hL hc hp hsplit T hT X v.property)
    have h₁ : Continuous (fun v : DerivativeSmoothVectors I π =>
        (smoothIteratedLieDerivative J σ Xs (M' (toSmooth I π v)) : H)) := ih T' hT'
    have h₂ : Continuous (fun v : DerivativeSmoothVectors I π =>
        (smoothIteratedLieDerivative J σ Xs (M (smoothLieDerivative I π Y (toSmooth I π v))) :
          H)) := (ih T hT).comp (operatorCLM I π Y).continuous
    refine (h₁.add h₂).congr fun v => ?_
    change _ = (smoothIteratedLieDerivative J σ (Xs ++ [X]) (M (toSmooth I π v)) : H)
    rw [smoothIteratedLieDerivative_append]
    change _ = (smoothIteratedLieDerivative J σ Xs
      (smoothLieDerivative J σ X (M (toSmooth I π v))) : H)
    rw [hd, map_add, Submodule.coe_add]
    rfl

/-- The smooth map is continuous for the genuine local and global word-derivative topologies. -/
def derivativeMap (hx₀ : IsSmoothVector I π x₀) (T : W)
    (hT : IsSmoothVector J σ (T.val x₀)) :
    DerivativeSmoothVectors I π →L[ℂ] DerivativeSmoothVectors J σ where
  toLinearMap := (toSmooth J σ).symm.toLinearMap.comp
    ((map π σ i p c hcomm L hL hc hp hsplit T hT).comp (toSmooth I π).toLinearMap)
  cont := by
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro Xs
    change Continuous (fun v : DerivativeSmoothVectors I π =>
      (smoothIteratedLieDerivative J σ Xs
        (map π σ i p c hcomm L hL hc hp hsplit T hT (toSmooth I π v)) : H))
    exact continuous_word π σ i p c hcomm L hL hc hp hsplit hx₀ Xs T hT

@[simp]
theorem toSmooth_derivativeMap (hx₀ : IsSmoothVector I π x₀) (T : W)
    (hT : IsSmoothVector J σ (T.val x₀)) (v : DerivativeSmoothVectors I π) :
    toSmooth J σ (derivativeMap π σ i p c hcomm L hL hc hp hsplit hx₀ T hT v) =
      map π σ i p c hcomm L hL hc hp hsplit T hT (toSmooth I π v) :=
  rfl

/-- A functional with a finite global word bound pulls back to a functional with a
finite local word bound. -/
theorem isContinuousOnSmoothVectors_comp (hx₀ : IsSmoothVector I π x₀)
    (T : W) (hT : IsSmoothVector J σ (T.val x₀))
    (ℓ : smoothVectors J σ →ₗ[ℂ] ℂ) (hℓ : IsContinuousOnSmoothVectors J σ ℓ) :
    IsContinuousOnSmoothVectors I π (ℓ.comp (map π σ i p c hcomm L hL hc hp hsplit T hT)) := by
  apply isContinuousOnSmoothVectors_of_continuous
  exact (continuous_of_isContinuousOnSmoothVectors J σ ℓ hℓ).comp
    (derivativeMap π σ i p c hcomm L hL hc hp hsplit hx₀ T hT).continuous

/-- A continuous global Whittaker functional pulls back along the local smooth map. -/
theorem isWhittakerFunctional_comp (hx₀ : IsSmoothVector I π x₀)
    (T : W) (hT : IsSmoothVector J σ (T.val x₀))
    (N : Subgroup G) (U : Subgroup A) (j : N →* U)
    (hj : ∀ u : N, (j u : A) = i (u : G)) (χ : U →* ℂˣ)
    (ℓ : smoothVectors J σ →ₗ[ℂ] ℂ) (hℓ : IsWhittakerFunctional J σ U χ ℓ) :
    IsWhittakerFunctional I π N (χ.comp j)
      (ℓ.comp (map π σ i p c hcomm L hL hc hp hsplit T hT)) := by
  refine ⟨isContinuousOnSmoothVectors_comp π σ i p c hcomm L hL hc hp hsplit hx₀ T hT ℓ hℓ.1,
    fun u v => ?_⟩
  change ℓ (map π σ i p c hcomm L hL hc hp hsplit T hT (smoothRepresentation I π (u : G) v)) =
    (χ (j u) : ℂ) * ℓ (map π σ i p c hcomm L hL hc hp hsplit T hT v)
  rw [map_smoothRepresentation, ← hj u]
  exact hℓ.2 (j u) _

omit hcomm hL hc hp hsplit

/-- A bounded intertwiner with a globally smooth evaluation at a locally smooth sample
acts continuously on genuine smooth vectors under the supplied splitting and recovery. -/
def SmoothIntertwinerExtensionStatement : Prop :=
  ∀ (V : Type ug) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (W₀ : Type ua) [NormedAddCommGroup W₀] [NormedSpace ℝ W₀]
    (G₀ : Type uG) [Group G₀] [TopologicalSpace G₀] [ChartedSpace V G₀] [LieGroup 𝓘(ℝ, V) ∞ G₀]
    (A₀ : Type uA) [Group A₀] [TopologicalSpace A₀] [ChartedSpace W₀ A₀] [LieGroup 𝓘(ℝ, W₀) ∞ A₀]
    (E₀ : Type uE) [NormedAddCommGroup E₀] [NormedSpace ℂ E₀]
    (H₀ : Type uH) [NormedAddCommGroup H₀] [NormedSpace ℂ H₀]
    (ρ : G₀ →* (E₀ →L[ℂ] E₀)) (τ : A₀ →* (H₀ →L[ℂ] H₀))
    (i₀ : G₀ →* A₀) (p₀ : A₀ →* G₀) (c₀ : A₀ → A₀),
    (∀ g h, Commute (c₀ g) (i₀ h)) → (∀ g, c₀ g * i₀ (p₀ g) = g) →
      ContMDiff 𝓘(ℝ, W₀) 𝓘(ℝ, W₀) ∞ c₀ → ContMDiff 𝓘(ℝ, W₀) 𝓘(ℝ, V) ∞ (p₀ : A₀ → G₀) →
      ∀ (x₀ : E₀) (L₀ : H₀ →L[ℂ] ↥(boundedIntertwiners ρ (τ.comp i₀))),
      (∀ S : ↥(boundedIntertwiners ρ (τ.comp i₀)), L₀ (S.val x₀) = S) →
        IsSmoothVector 𝓘(ℝ, V) ρ x₀ →
        ∀ T : ↥(boundedIntertwiners ρ (τ.comp i₀)), IsSmoothVector 𝓘(ℝ, W₀) τ (T.val x₀) →
          ∃ M : DerivativeSmoothVectors 𝓘(ℝ, V) ρ →L[ℂ] DerivativeSmoothVectors 𝓘(ℝ, W₀) τ,
            ∀ v, (toSmooth 𝓘(ℝ, W₀) τ (M v) : H₀) = T.val (toSmooth 𝓘(ℝ, V) ρ v)

theorem smoothIntertwinerExtension : SmoothIntertwinerExtensionStatement.{ug, ua, uG, uA, uE, uH} := by
  intro V _ _ W₀ _ _ G₀ _ _ _ _ A₀ _ _ _ _ E₀ _ _ H₀ _ _
    ρ τ i₀ p₀ c₀ hcomm₀ hsplit₀ hc₀ hp₀ x₀ L₀ hL₀ hx₀ T hT
  exact ⟨derivativeMap ρ τ i₀ p₀ c₀ hcomm₀ L₀ hL₀ hc₀ hp₀ hsplit₀ hx₀ T hT, fun v => rfl⟩

end Langlands.Archimedean.SmoothIntertwinerExtension
