import Langlands.BaseChange.CyclicAlgebraTopology
import Langlands.BaseChange.SigmaLiftInductionStatement
import Langlands.BaseChange.PseudoCoefficient
import Langlands.AllField.HarmonicAnalysis.PadicScalarHaarScalingProof
import Langlands.AllField.Representation.Parabolic.NormalizedAdmissibilityProof
import Langlands.Representation.Tensor.FiniteProperties

/-!
# The induced σ-intertwiner of a normalized product induction

For a σ-stable family `Π₁, …, Π_r` of representations of the blocks `GL_{nᵢ}(E)` with
σ-intertwiners `Aᵢ`, the operator `ι(A)(ξ)(g) = (A₁ ⊗ ⋯ ⊗ A_r)(ξ(g^{σ⁻¹}))` is a σ-intertwiner
of the normalized product induction `i(Π₁, …, Π_r)` (Henniart–Lemaire 2011, II.4.4).
The module also proves the inputs: continuity of `σ` and of `g ↦ g^σ`, σ-invariance of the
normalized absolute value and of the block modulus, and admissibility of normalized product
inductions of admissible families. See the paired Markdown.
-/

noncomputable section

open MeasureTheory
open scoped NNReal

/-! ## Transport of smooth induced functions along an automorphism -/

namespace Langlands.Induction

universe uR uG uV uW

variable {R : Type uR} {G : Type uG} {V : Type uV} {W : Type uW}
variable [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

omit [IsTopologicalGroup G] in
/-- Every smooth induced function is invariant under right translation by one open
subgroup. -/
theorem exists_openSubgroup_eval_mul (P : Subgroup G) (ρ : Representation R P V)
    (f : SmoothFunctions P ρ) :
    ∃ K : OpenSubgroup G, ∀ (k : K) (x : G), eval P ρ f (x * (k : G)) = eval P ρ f x := by
  obtain ⟨K, hK⟩ := f.2
  refine ⟨K, fun k x => ?_⟩
  have h := hK k
  exact congrArg (fun φ : EquivariantFunctions P ρ => (φ : G → V) x) h

/-- The function `x ↦ T (f (θ⁻¹ x))` of a smooth induced function `f`, for an automorphism
`θ` of `G` whose inverse is continuous, an automorphism `θP` of `P` that agrees with `θ` on
`P`, and a linear map `T` with `T ∘ ρ(p) = τ(θP p) ∘ T`. -/
def transportSmoothFunction (P : Subgroup G) {ρ : Representation R P V} {τ : Representation R P W}
    (θ : G ≃* G) (hθ : Continuous θ.symm) (θP : P ≃* P)
    (hθP : ∀ p : P, ((θP p : P) : G) = θ p)
    (T : V →ₗ[R] W) (hT : ∀ (p : P) (v : V), T (ρ p v) = τ (θP p) (T v))
    (f : SmoothFunctions P ρ) : SmoothFunctions P τ :=
  smoothFunctionOf P τ (fun x => T (eval P ρ f (θ.symm x)))
    (fun p x => by
      have hp : θ.symm (p : G) = ((θP.symm p : P) : G) := by
        rw [MulEquiv.symm_apply_eq, ← hθP, MulEquiv.apply_symm_apply]
      have hcov : f.1.1 (((θP.symm p : P) : G) * θ.symm x) =
          ρ (θP.symm p) (f.1.1 (θ.symm x)) := f.1.2 _ _
      change T (eval P ρ f (θ.symm ((p : G) * x))) = τ p (T (eval P ρ f (θ.symm x)))
      rw [map_mul, hp]
      change T (f.1.1 (((θP.symm p : P) : G) * θ.symm x)) = _
      rw [hcov, hT, MulEquiv.apply_symm_apply]
      rfl)
    ((exists_openSubgroup_eval_mul P ρ f).choose.comap θ.symm.toMonoidHom hθ)
    (fun k x => by
      have hk : θ.symm (k : G) ∈ (exists_openSubgroup_eval_mul P ρ f).choose := k.2
      change T (eval P ρ f (θ.symm (x * (k : G)))) = T (eval P ρ f (θ.symm x))
      rw [map_mul, (exists_openSubgroup_eval_mul P ρ f).choose_spec ⟨_, hk⟩])

omit [IsTopologicalGroup G] in
@[simp]
theorem eval_transportSmoothFunction (P : Subgroup G) {ρ : Representation R P V}
    {τ : Representation R P W} (θ : G ≃* G) (hθ : Continuous θ.symm) (θP : P ≃* P)
    (hθP : ∀ p : P, ((θP p : P) : G) = θ p)
    (T : V →ₗ[R] W) (hT : ∀ (p : P) (v : V), T (ρ p v) = τ (θP p) (T v))
    (f : SmoothFunctions P ρ) (x : G) :
    eval P τ (transportSmoothFunction P θ hθ θP hθP T hT f) x = T (eval P ρ f (θ.symm x)) :=
  rfl

omit [IsTopologicalGroup G] in
private theorem smoothTransport_ext (P : Subgroup G) {ρ : Representation R P V}
    {f g : SmoothFunctions P ρ} (h : ∀ x, eval P ρ f x = eval P ρ g x) : f = g :=
  Subtype.ext (Subtype.ext (funext h))

/-- `transportSmoothFunction` as a linear map. -/
def transportSmoothLinearMap (P : Subgroup G) {ρ : Representation R P V} {τ : Representation R P W}
    (θ : G ≃* G) (hθ : Continuous θ.symm) (θP : P ≃* P)
    (hθP : ∀ p : P, ((θP p : P) : G) = θ p)
    (T : V →ₗ[R] W) (hT : ∀ (p : P) (v : V), T (ρ p v) = τ (θP p) (T v)) :
    SmoothFunctions P ρ →ₗ[R] SmoothFunctions P τ where
  toFun := transportSmoothFunction P θ hθ θP hθP T hT
  map_add' f g := smoothTransport_ext P fun x => by
    change T (eval P ρ (f + g) (θ.symm x)) = T (eval P ρ f (θ.symm x)) + T (eval P ρ g (θ.symm x))
    rw [← map_add]
    rfl
  map_smul' c f := smoothTransport_ext P fun x => by
    change T (eval P ρ (c • f) (θ.symm x)) = c • T (eval P ρ f (θ.symm x))
    rw [← map_smul]
    rfl

/-- The transport `f ↦ T ∘ f ∘ θ⁻¹` along a topological automorphism `θ` of `G` that
preserves `P`, for a linear equivalence `T` with `T ∘ ρ(p) = τ(θ p) ∘ T`, is an isomorphism
of the smooth induced representation of `ρ` with the pullback along `θ` of the smooth induced
representation of `τ`. -/
def transportSmoothEquiv (P : Subgroup G) {ρ : Representation R P V} {τ : Representation R P W}
    (θ : G ≃* G) (hθ : Continuous θ) (hθ' : Continuous θ.symm) (θP : P ≃* P)
    (hθP : ∀ p : P, ((θP p : P) : G) = θ p)
    (T : V ≃ₗ[R] W) (hT : ∀ (p : P) (v : V), T (ρ p v) = τ (θP p) (T v)) :
    (smoothInduced P ρ).Equiv ((smoothInduced P τ).comp θ.toMonoidHom) :=
  have hθP' : ∀ p : P, ((θP.symm p : P) : G) = θ.symm p := fun p => by
    rw [MulEquiv.eq_symm_apply, ← hθP, MulEquiv.apply_symm_apply]
  have hT' : ∀ (p : P) (w : W), T.symm (τ p w) = ρ (θP.symm p) (T.symm w) := fun p w => by
    rw [LinearEquiv.symm_apply_eq, hT, MulEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  Representation.Equiv.mk
    { transportSmoothLinearMap P θ hθ' θP hθP T.toLinearMap hT with
      invFun := transportSmoothLinearMap P θ.symm hθ θP.symm hθP' T.symm.toLinearMap hT'
      left_inv := fun f => smoothTransport_ext P fun x => by
        change T.symm (T (eval P ρ f (θ.symm (θ.symm.symm x)))) = eval P ρ f x
        rw [LinearEquiv.symm_apply_apply, MulEquiv.symm_symm, MulEquiv.symm_apply_apply]
      right_inv := fun f => smoothTransport_ext P fun x => by
        change T (T.symm (eval P τ f (θ.symm.symm (θ.symm x)))) = eval P τ f x
        rw [LinearEquiv.apply_symm_apply, MulEquiv.symm_symm, MulEquiv.apply_symm_apply] }
    (fun g => LinearMap.ext fun f => smoothTransport_ext P fun x => by
      change T (eval P ρ f (θ.symm x * g)) = T (eval P ρ f (θ.symm (x * θ g)))
      rw [map_mul, MulEquiv.symm_apply_apply])

@[simp]
theorem eval_transportSmoothEquiv (P : Subgroup G) {ρ : Representation R P V}
    {τ : Representation R P W} (θ : G ≃* G) (hθ : Continuous θ) (hθ' : Continuous θ.symm)
    (θP : P ≃* P) (hθP : ∀ p : P, ((θP p : P) : G) = θ p)
    (T : V ≃ₗ[R] W) (hT : ∀ (p : P) (v : V), T (ρ p v) = τ (θP p) (T v))
    (f : SmoothFunctions P ρ) (x : G) :
    eval P τ (transportSmoothEquiv P θ hθ hθ' θP hθP T hT f) x = T (eval P ρ f (θ.symm x)) :=
  rfl

end Langlands.Induction

/-! ## The entrywise action of `σ` on `GL_n(E)` and the normalized absolute value -/

namespace Langlands.BaseChange

open Langlands.GeneralLinear

universe u v uV uW

section Continuity

variable {F : Type u} [Field F] [TopologicalSpace F]
  {E : Type v} [Field E] [TopologicalSpace E] [IsTopologicalRing E] [Algebra F E]
  [IsModuleTopology F E]

/-- An `F`-algebra automorphism of `E` is continuous for the `F`-module topology of `E`. -/
theorem continuous_algEquiv (σ : E ≃ₐ[F] E) : Continuous σ :=
  IsModuleTopology.continuous_of_linearMap (R := F) σ.toLinearMap

/-- The inverse `g ↦ g^{σ⁻¹}` of the entrywise action of `σ` on `GL_n(E)` is continuous. -/
theorem continuous_entrywiseAut_symm (σ : E ≃ₐ[F] E) (n : ℕ) :
    Continuous (entrywiseAut σ n).symm :=
  continuous_entrywiseAut σ.symm n

end Continuity

section Abs

variable {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

/-- The normalized absolute value of a nonarchimedean local field is invariant under every
ring automorphism that is a homeomorphism: both scale an additive Haar measure by the same
factor. -/
theorem normalizedAbsUnits_map_ringEquiv (τ : E ≃+* E) (hτ : Continuous τ)
    (hτ' : Continuous τ.symm) (a : Eˣ) :
    (LocalFieldData.ofInstances E).normalizedAbsUnits (Units.map ((τ : E →+* E) : E →* E) a) =
      (LocalFieldData.ofInstances E).normalizedAbsUnits a := by
  let _ : MeasurableSpace E := borel E
  have hB : BorelSpace E := ⟨rfl⟩
  have _ : @BorelSpace E (LocalFieldData.ofInstances E).topology _ := hB
  let μ : Measure E := Measure.addHaar
  let ν : Measure E := μ.map τ
  have hμ : μ.IsAddHaarMeasure := inferInstanceAs (Measure.addHaar (G := E)).IsAddHaarMeasure
  have hν : ν.IsAddHaarMeasure := τ.toAddEquiv.isAddHaarMeasure_map μ hτ hτ'
  have _ : @Measure.IsAddHaarMeasure E _ (LocalFieldData.ofInstances E).topology _ μ := hμ
  have _ : @Measure.IsAddHaarMeasure E _ (LocalFieldData.ofInstances E).topology _ ν := hν
  have h1 := AllField.HarmonicAnalysis.padicScalarHaarScaling E (LocalFieldData.ofInstances E)
    ν (Units.map ((τ : E →+* E) : E →* E) a)
  have h2 := AllField.HarmonicAnalysis.padicScalarHaarScaling E (LocalFieldData.ofInstances E)
    μ a
  have hmeas : Measurable τ := hτ.measurable
  have h3 : ν.map (fun x => ((Units.map ((τ : E →+* E) : E →* E) a : Eˣ) : E) * x) =
      (μ.map (fun x => (a : E) * x)).map τ := by
    rw [Measure.map_map (continuous_const_mul _).measurable hmeas,
      Measure.map_map hmeas (continuous_const_mul _).measurable]
    congr 1
    funext x
    simp [map_mul]
  rw [h1, h2, Measure.map_smul] at h3
  on_goal 2 => exact hmeas.aemeasurable
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : E)
  have hpos : ν K ≠ 0 := (Measure.measure_pos_of_mem_nhds (μ := ν) hK0).ne'
  have hfin : ν K ≠ ⊤ := hK.measure_lt_top.ne
  have h4 := congrArg (fun m : Measure E => m K) h3
  simp only [Measure.smul_apply, Measure.nnreal_smul_coe_apply] at h4
  have h5 := (ENNReal.mul_left_inj hpos hfin).1 h4
  exact Units.ext (inv_inj.1 (ENNReal.coe_inj.1 h5))

variable {F : Type u} [Field F] [TopologicalSpace F] [Algebra F E] [IsModuleTopology F E]

/-- The normalized absolute value of `E` is invariant under `σ`. -/
theorem normalizedAbsUnits_algEquiv (σ : E ≃ₐ[F] E) (a : Eˣ) :
    (LocalFieldData.ofInstances E).normalizedAbsUnits (Units.map ((σ : E →+* E) : E →* E) a) =
      (LocalFieldData.ofInstances E).normalizedAbsUnits a :=
  normalizedAbsUnits_map_ringEquiv σ.toRingEquiv (continuous_algEquiv σ)
    (continuous_algEquiv σ.symm) a

/-- `|det g^σ| = |det g|` on `GL_n(E)`. -/
theorem determinantNorm_entrywiseAut (σ : E ≃ₐ[F] E) (n : ℕ) (g : GeneralLinear n E) :
    (LocalFieldData.ofInstances E).determinantNorm n (entrywiseAut σ n g) =
      (LocalFieldData.ofInstances E).determinantNorm n g := by
  change (LocalFieldData.ofInstances E).normalizedAbsUnits
      (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (σ : E →+* E) g)) =
    (LocalFieldData.ofInstances E).normalizedAbsUnits (Matrix.GeneralLinearGroup.det g)
  rw [Matrix.GeneralLinearGroup.map_det]
  exact normalizedAbsUnits_algEquiv σ _

/-- The modulus of a standard block Levi of `GL_n(E)` is invariant under `σ`. -/
theorem leviModulus_leviAut (σ : E ≃ₐ[F] E) {n : ℕ} (B : BlockShape n) (m : B.Levi E) :
    (LocalFieldData.ofInstances E).leviModulus B (leviAut σ B m) =
      (LocalFieldData.ofInstances E).leviModulus B m := by
  simp only [LocalFieldData.leviModulus_apply, leviAut_apply, determinantNorm_entrywiseAut]

end Abs

/-! ## The entrywise action on a standard parabolic subgroup -/

section Parabolic

variable {F : Type u} [CommRing F] {E : Type v} [CommRing E] [Algebra F E]

/-- The restriction of `g ↦ g^σ` to the standard parabolic subgroup of `B`. -/
def parabolicAut (σ : E ≃ₐ[F] E) {n : ℕ} (B : BlockShape n) :
    B.parabolic E ≃* B.parabolic E where
  toFun p := ⟨entrywiseAut σ n p, (entrywiseAut_mem_parabolic_iff σ B p).2 p.2⟩
  invFun p := ⟨entrywiseAut σ.symm n p, (entrywiseAut_mem_parabolic_iff σ.symm B p).2 p.2⟩
  left_inv p := Subtype.ext ((entrywiseAut σ n).symm_apply_apply (p : GeneralLinear n E))
  right_inv p := Subtype.ext ((entrywiseAut σ n).apply_symm_apply (p : GeneralLinear n E))
  map_mul' p q := Subtype.ext (map_mul (entrywiseAut σ n) (p : GeneralLinear n E) q)

@[simp]
theorem coe_parabolicAut (σ : E ≃ₐ[F] E) {n : ℕ} (B : BlockShape n) (p : B.parabolic E) :
    ((parabolicAut σ B p : B.parabolic E) : GeneralLinear n E) = entrywiseAut σ n p :=
  rfl

theorem leviProjection_parabolicAut (σ : E ≃ₐ[F] E) {n : ℕ} (B : BlockShape n)
    (p : B.parabolic E) :
    B.leviProjection E (parabolicAut σ B p) = leviAut σ B (B.leviProjection E p) :=
  leviProjection_entrywiseAut σ B p

end Parabolic

section ParabolicModulus

variable {F : Type u} [Field F] [TopologicalSpace F]
  {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [IsModuleTopology F E]

/-- The half modulus of a standard parabolic subgroup of `GL_n(E)` is invariant under `σ`. -/
theorem parabolicHalfModulus_parabolicAut (σ : E ≃ₐ[F] E) {n : ℕ} (B : BlockShape n)
    (p : B.parabolic E) :
    (LocalFieldData.ofInstances E).parabolicHalfModulus B (parabolicAut σ B p) =
      (LocalFieldData.ofInstances E).parabolicHalfModulus B p := by
  rw [LocalFieldData.parabolicHalfModulus_apply, LocalFieldData.parabolicHalfModulus_apply,
    leviProjection_parabolicAut]
  exact Units.ext (by
    rw [LocalFieldData.leviHalfModulus_apply, LocalFieldData.leviHalfModulus_apply,
      leviModulus_leviAut])

end ParabolicModulus

/-! ## The tensor product of the block σ-intertwiners -/

section Tensor

variable {F : Type u} [CommRing F] {E : Type v} [CommRing E] [Algebra F E]
  (σ : E ≃ₐ[F] E) {n : ℕ} (B : BlockShape n)
  {W : Fin B.length → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
  {P : ∀ i, Representation ℂ (GeneralLinear (B.size i) E) (W i)}

/-- The tensor product `A₁ ⊗ ⋯ ⊗ A_r` of σ-intertwiners of the block factors: an isomorphism
of the Levi representation `P₁ ⊗ ⋯ ⊗ P_r` with its pullback along `leviAut σ B`. -/
def leviTensorIntertwiner (A : ∀ i, SigmaIntertwiner σ (B.size i) (P i)) :
    (B.blockTensor P).Equiv ((B.blockTensor P).comp (leviAut σ B).toMonoidHom) :=
  Representation.Equiv.mk (PiTensorProduct.congr fun i => (A i).toLinearEquiv) fun m =>
    PiTensorProduct.ext <| MultilinearMap.ext fun w => by
      have hA : ∀ i, (A i).toLinearEquiv (P i (m i) (w i)) =
          P i (entrywiseAut σ (B.size i) (m i)) ((A i).toLinearEquiv (w i)) := fun i =>
        LinearMap.congr_fun ((A i).comp_apply_eq (m i)) (w i)
      change PiTensorProduct.congr (fun i => (A i).toLinearEquiv)
          (B.blockTensor P m (PiTensorProduct.tprod ℂ w)) =
        B.blockTensor P (leviAut σ B m)
          (PiTensorProduct.congr (fun i => (A i).toLinearEquiv) (PiTensorProduct.tprod ℂ w))
      rw [BlockShape.blockTensor_tprod, PiTensorProduct.congr_tprod, PiTensorProduct.congr_tprod,
        BlockShape.blockTensor_tprod]
      simp only [leviAut_apply, hA]

@[simp]
theorem leviTensorIntertwiner_tprod (A : ∀ i, SigmaIntertwiner σ (B.size i) (P i))
    (w : ∀ i, W i) :
    (leviTensorIntertwiner σ B A).toLinearEquiv (PiTensorProduct.tprod ℂ w) =
      PiTensorProduct.tprod ℂ (fun i => (A i).toLinearEquiv (w i)) :=
  PiTensorProduct.congr_tprod _ _

/-- The tensor product of the block factors of a family of σ-stable representations is
σ-stable as a representation of the Levi product. -/
theorem isLeviSigmaStable_blockTensor (A : ∀ i, SigmaIntertwiner σ (B.size i) (P i)) :
    IsLeviSigmaStable σ B (B.blockTensor P) :=
  ⟨leviTensorIntertwiner σ B A⟩

end Tensor

/-! ## The induced σ-intertwiner and admissibility -/

section Induced

variable {F : Type u} [Field F] [TopologicalSpace F]
  {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [IsModuleTopology F E]
  (σ : E ≃ₐ[F] E) {n : ℕ} (B : BlockShape n)
  {W : Fin B.length → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
  {P : ∀ i, Representation ℂ (GeneralLinear (B.size i) E) (W i)}

/-- The tensor product of the block σ-intertwiners intertwines the normalized inducing
representation `δ_P^{1/2} ⊗ (P₁ ⊗ ⋯ ⊗ P_r)` of the parabolic with its pullback along `σ`. -/
theorem leviTensorIntertwiner_inducing (A : ∀ i, SigmaIntertwiner σ (B.size i) (P i))
    (p : B.parabolic E) (w : PiTensorProduct ℂ W) :
    (leviTensorIntertwiner σ B A).toLinearEquiv
        (twist ((LocalFieldData.ofInstances E).parabolicHalfModulus B)
          ((B.blockTensor P).comp (B.leviProjection E)) p w) =
      twist ((LocalFieldData.ofInstances E).parabolicHalfModulus B)
          ((B.blockTensor P).comp (B.leviProjection E)) (parabolicAut σ B p)
        ((leviTensorIntertwiner σ B A).toLinearEquiv w) := by
  change (leviTensorIntertwiner σ B A).toLinearEquiv
      (((LocalFieldData.ofInstances E).parabolicHalfModulus B p : ℂ) •
        B.blockTensor P (B.leviProjection E p) w) =
    ((LocalFieldData.ofInstances E).parabolicHalfModulus B (parabolicAut σ B p) : ℂ) •
      B.blockTensor P (B.leviProjection E (parabolicAut σ B p))
        ((leviTensorIntertwiner σ B A).toLinearEquiv w)
  rw [map_smul, parabolicHalfModulus_parabolicAut, leviProjection_parabolicAut]
  congr 1
  exact LinearMap.congr_fun
    ((leviTensorIntertwiner σ B A).isIntertwining' (B.leviProjection E p)) w

/-- Henniart–Lemaire's induced σ-intertwiner `ι(A)` of `i(P₁, …, P_r)`:
`ι(A)(ξ)(g) = (A₁ ⊗ ⋯ ⊗ A_r)(ξ(g^{σ⁻¹}))`. -/
def inducedSigmaIntertwiner (A : ∀ i, SigmaIntertwiner σ (B.size i) (P i)) :
    SigmaIntertwiner σ n ((LocalFieldData.ofInstances E).normalizedProductInduced B P) :=
  Induction.transportSmoothEquiv (B.parabolic E) (entrywiseAut σ n) (continuous_entrywiseAut σ n)
    (continuous_entrywiseAut_symm σ n) (parabolicAut σ B) (fun _ => rfl)
    (leviTensorIntertwiner σ B A).toLinearEquiv (leviTensorIntertwiner_inducing σ B A)

/-- The defining formula `ι(A)(ξ)(g) = (A₁ ⊗ ⋯ ⊗ A_r)(ξ(g^{σ⁻¹}))`. -/
theorem eval_inducedSigmaIntertwiner (A : ∀ i, SigmaIntertwiner σ (B.size i) (P i))
    (ξ : Induction.SmoothFunctions (B.parabolic E)
      (twist ((LocalFieldData.ofInstances E).parabolicHalfModulus B)
        ((B.blockTensor P).comp (B.leviProjection E))))
    (g : GeneralLinear n E) :
    Induction.eval (B.parabolic E)
        (twist ((LocalFieldData.ofInstances E).parabolicHalfModulus B)
          ((B.blockTensor P).comp (B.leviProjection E)))
        ((inducedSigmaIntertwiner σ B A).toLinearEquiv ξ) g =
      (leviTensorIntertwiner σ B A).toLinearEquiv
        (Induction.eval (B.parabolic E)
          (twist ((LocalFieldData.ofInstances E).parabolicHalfModulus B)
            ((B.blockTensor P).comp (B.leviProjection E))) ξ (entrywiseAut σ.symm n g)) :=
  rfl

/-- The normalized product induction of a σ-stable family is σ-stable. -/
theorem isSigmaStable_normalizedProductInduced (A : ∀ i, SigmaIntertwiner σ (B.size i) (P i)) :
    IsSigmaStable σ n ((LocalFieldData.ofInstances E).normalizedProductInduced B P) :=
  ⟨inducedSigmaIntertwiner σ B A⟩

end Induced

section Admissible

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ} (B : BlockShape n)
  {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

/-- Normalized parabolic induction of a tensor product of admissible block representations is
admissible. -/
theorem isAdmissible_normalizedProductInduced
    (π : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i))
    (hπ : ∀ i, IsAdmissible (π i)) :
    IsAdmissible ((LocalFieldData.ofInstances F).normalizedProductInduced B π) :=
  AllField.Parabolic.normalizedInductionAdmissibility F (LocalFieldData.ofInstances F) B _
    (B.blockTensor π) (FiniteTensor.isAdmissible_external π hπ)

end Admissible

end Langlands.BaseChange
