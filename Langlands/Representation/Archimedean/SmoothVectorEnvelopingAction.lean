import Langlands.Representation.Archimedean.EnvelopingInduction
import Langlands.Representation.Archimedean.SmoothFunctionalOrbit
import Langlands.Geometry.Manifold.SmoothGroupLieDifferential
import Langlands.Geometry.Manifold.SmoothGroupConjugationLie
import Langlands.Algebra.ComplexLieExtension

/-!
# The enveloping algebra acting on smooth vectors

Let `π` be a representation of a real Lie group `M` (modelled on a normed space `A`) on a complex
inner product space `E` by bounded operators. The derivatives `dπ(X)`, `X ∈ Lie(M)`, act on the
smooth vectors. Through the Hilbert matrix coefficients `g ↦ ⟪u, π g w⟫` they correspond to the
differentiations `groupDirectionalValue` of functions on `M`, so the Lie law of `dπ` follows from
the Lie law of these differentiations, which is the hypothesis `smoothVectorFieldCommutator`.
This gives the action of the universal enveloping algebra of the complexified Lie algebra on the
smooth vectors, with the covariance `π g ∘ dπ(y) = dπ(Ad(g) y) ∘ π g`.
-/

noncomputable section

open scoped Manifold ContDiff InnerProductSpace TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace Langlands.Archimedean.SmoothVectorEnveloping

open Langlands.Geometry.Manifold

attribute [local instance 100] LieRing.ofAssociativeRing

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  {M : Type*} [Group M] [TopologicalSpace M] [ChartedSpace A M] [LieGroup 𝓘(ℝ, A) ∞ M]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  (π : M →* (E →L[ℂ] E))

local notation "I" => 𝓘(ℝ, A)

/-- The Hilbert matrix coefficient `g ↦ ⟪u, π g w⟫`. -/
def hilbertCoefficient (u w : E) : M → ℂ := fun g => ⟪u, π g w⟫_ℂ

omit [LieGroup I ∞ M] in
theorem contMDiff_hilbertCoefficient (u : E) {w : E} (hw : IsSmoothVector I π w) :
    ContMDiff I 𝓘(ℝ, ℂ) ∞ (hilbertCoefficient π u w) :=
  ((innerSL ℂ u).restrictScalars ℝ).contDiff.contMDiff.comp hw

/-- The derivative of a scalar orbit `h ↦ ℓ(π (g h) w)` for a continuous real-linear `ℓ`. -/
theorem mfderiv_clm_orbit (ℓ : E →L[ℝ] ℂ) (g : M) {w : E} (hw : IsSmoothVector I π w)
    (X : A) :
    mfderiv I 𝓘(ℝ, ℂ) (fun h => ℓ (π (g * h) w)) 1 X = ℓ (π g (lieDerivative I π X w)) := by
  let B : E →L[ℝ] ℂ := ℓ.comp ((π g).restrictScalars ℝ)
  have hf : MDifferentiableAt I 𝓘(ℝ, E) (orbitMap π w) 1 := hw.mdifferentiableAt (by simp)
  have he : (fun h => ℓ (π (g * h) w)) = B ∘ orbitMap π w := by
    funext h
    simp only [Function.comp_apply, B, orbitMap, map_mul]
    rfl
  rw [he, mfderiv_comp 1 B.differentiableAt.mdifferentiableAt hf, ContinuousLinearMap.mfderiv_eq]
  rfl

/-- Differentiating a Hilbert coefficient differentiates the vector. -/
theorem groupDirectionalValue_hilbertCoefficient (u : E) {w : E} (hw : IsSmoothVector I π w)
    (X : GroupLieAlgebra I M) (g : M) :
    groupDirectionalValue I X (hilbertCoefficient π u w) g =
      hilbertCoefficient π u (lieDerivative I π X w) g := by
  have h := mfderiv_clm_orbit π ((innerSL ℂ u).restrictScalars ℝ) g hw X
  exact h

theorem groupDirectionalValue_hilbertCoefficient_fun (u : E) {w : E}
    (hw : IsSmoothVector I π w) (X : GroupLieAlgebra I M) :
    groupDirectionalValue I X (hilbertCoefficient π u w) =
      hilbertCoefficient π u (lieDerivative I π X w) :=
  funext (groupDirectionalValue_hilbertCoefficient π u hw X)

/-- Vectors with the same Hilbert coefficients at the identity are equal. -/
theorem eq_of_hilbertCoefficient_one {w w' : E}
    (h : ∀ u : E, hilbertCoefficient π u w 1 = hilbertCoefficient π u w' 1) : w = w' := by
  apply ext_inner_left ℂ
  intro u
  simpa [hilbertCoefficient] using h u

/-- The derivatives `dπ` satisfy the Lie law on smooth vectors, given the scalar commutator law
for vector fields on `M`. -/
theorem lieDerivative_lie [CompleteSpace A] [LieGroup I (minSmoothness ℝ 3) M]
    (hcalc : smoothVectorFieldCommutator I M) (X Y : GroupLieAlgebra I M) {w : E}
    (hw : IsSmoothVector I π w) :
    lieDerivative I π (⁅X, Y⁆ : GroupLieAlgebra I M) w =
      lieDerivative I π X (lieDerivative I π Y w) - lieDerivative I π Y (lieDerivative I π X w) := by
  have hYw := isSmoothVector_lieDerivative I π Y hw
  have hXw := isSmoothVector_lieDerivative I π X hw
  apply eq_of_hilbertCoefficient_one π
  intro u
  have hc := groupDirectionalValue_commutator_of_vectorFieldCommutator I hcalc X Y
    (contMDiff_hilbertCoefficient π u hw) 1
  rw [groupDirectionalValue_hilbertCoefficient π u hw,
    groupDirectionalValue_hilbertCoefficient_fun π u hw,
    groupDirectionalValue_hilbertCoefficient_fun π u hw,
    groupDirectionalValue_hilbertCoefficient π u hYw,
    groupDirectionalValue_hilbertCoefficient π u hXw] at hc
  rw [hc]
  simp [hilbertCoefficient, inner_sub_right]

/-- Right covariance: `π g ∘ dπ(X) = dπ(Ad(g) X) ∘ π g` on smooth vectors. -/
theorem apply_lieDerivative_eq (g : M) (X : GroupLieAlgebra I M) {w : E}
    (hw : IsSmoothVector I π w) :
    π g (lieDerivative I π X w) =
      lieDerivative I π (groupTangentConjugation I g X) (π g w) := by
  have hgw : IsSmoothVector I π (π g w) := isSmoothVector_apply I π hw g
  apply eq_of_hilbertCoefficient_one π
  intro u
  have h := groupDirectionalValue_rightTranslation I g X (contMDiff_hilbertCoefficient π u hw) 1
  have hR : (fun y => hilbertCoefficient π u w (y * g)) = hilbertCoefficient π u (π g w) := by
    funext y
    simp [hilbertCoefficient, map_mul]
  rw [hR, groupDirectionalValue_hilbertCoefficient π u hw,
    groupDirectionalValue_hilbertCoefficient π u hgw] at h
  simpa [hilbertCoefficient] using h

/-- Induction over the generators `ι Z` of a complexified Lie algebra: pure tensors, sums. -/
theorem generatorInduction {L : Type*} [LieRing L] [LieAlgebra ℝ L]
    {C : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L) → Prop}
    (htmul : ∀ (c : ℂ) (X : L), C (UniversalEnvelopingAlgebra.ι ℂ (c ⊗ₜ[ℝ] X)))
    (hadd : ∀ a b, C a → C b → C (a + b)) (Z : ℂ ⊗[ℝ] L) :
    C (UniversalEnvelopingAlgebra.ι ℂ Z) := by
  induction Z using TensorProduct.inductionOn with
  | tmul c X => exact htmul c X
  | add Z₁ Z₂ h₁ h₂ =>
    rw [map_add]
    exact hadd _ _ h₁ h₂

variable [CompleteSpace A] [LieGroup 𝓘(ℝ, A) (minSmoothness ℝ 3) M]

local notation "𝔘" => UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ, A) M)

/-- The derivatives `dπ(X)` as a real Lie algebra homomorphism into the complex endomorphisms
of the smooth vectors. -/
def smoothLieAction (hcalc : smoothVectorFieldCommutator I M) :
    GroupLieAlgebra I M →ₗ⁅ℝ⁆ Module.End ℂ (smoothVectors I π) where
  toFun X := smoothLieDerivative I π X
  map_add' X Y := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact map_add (mfderiv I 𝓘(ℝ, E) (orbitMap π (v : E)) 1) X Y
  map_smul' c X := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact map_smul (mfderiv I 𝓘(ℝ, E) (orbitMap π (v : E)) 1) c X
  map_lie' := by
    intro X Y
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    rw [LieRing.of_associative_ring_bracket]
    exact lieDerivative_lie π hcalc X Y v.property

/-- The action of the universal enveloping algebra of the complexified Lie algebra on the
smooth vectors. -/
def envelopingAction (hcalc : smoothVectorFieldCommutator I M) :
    𝔘 →ₐ[ℂ] Module.End ℂ (smoothVectors I π) :=
  Langlands.Algebra.ComplexLieExtension.enveloping (smoothLieAction π hcalc)

theorem envelopingAction_ι_tmul (hcalc : smoothVectorFieldCommutator I M) (c : ℂ)
    (X : GroupLieAlgebra I M) (v : smoothVectors I π) :
    (envelopingAction π hcalc (UniversalEnvelopingAlgebra.ι ℂ (c ⊗ₜ[ℝ] X)) v : E) =
      c • lieDerivative I π X v := by
  unfold envelopingAction
  rw [Langlands.Algebra.ComplexLieExtension.enveloping_generator,
    Langlands.Algebra.ComplexLieExtension.lie_tmul]
  rfl

theorem envelopingAction_algebraMap (hcalc : smoothVectorFieldCommutator I M) (r : ℂ)
    (v : smoothVectors I π) :
    envelopingAction π hcalc (algebraMap ℂ 𝔘 r) v = r • v := by
  rw [AlgHom.commutes]
  rfl

/-- Covariance: for an algebra endomorphism `φ` of the enveloping algebra extending `Ad(g)`,
`π g ∘ dπ(y) = dπ(φ y) ∘ π g` on smooth vectors. -/
theorem apply_envelopingAction (hcalc : smoothVectorFieldCommutator I M) (g : M)
    (φ : 𝔘 →ₐ[ℂ] 𝔘)
    (hφ : ∀ (c : ℂ) (X : GroupLieAlgebra I M),
      φ (UniversalEnvelopingAlgebra.ι ℂ (c ⊗ₜ[ℝ] X)) =
        UniversalEnvelopingAlgebra.ι ℂ (c ⊗ₜ[ℝ] groupTangentConjugation I g X))
    (y : 𝔘) (v : smoothVectors I π) :
    π g (envelopingAction π hcalc y v) =
      envelopingAction π hcalc (φ y) (smoothRepresentation I π g v) := by
  induction y using Langlands.Archimedean.InfinitesimalCharacter.envInduction generalizing v with
  | algebraMap r =>
    rw [φ.commutes, envelopingAction_algebraMap, envelopingAction_algebraMap]
    simp
  | «ι» Z =>
    revert v
    induction Z using TensorProduct.inductionOn with
    | tmul c X =>
      intro v
      rw [hφ, envelopingAction_ι_tmul, envelopingAction_ι_tmul, map_smul,
        apply_lieDerivative_eq π g X v.property]
      rfl
    | add Z₁ Z₂ h₁ h₂ =>
      intro v
      simp only [map_add, LinearMap.add_apply, Submodule.coe_add]
      rw [h₁, h₂]
  | mul a b ha hb =>
    simp only [map_mul, Module.End.mul_apply]
    rw [ha, show smoothRepresentation I π g (envelopingAction π hcalc b v) =
      envelopingAction π hcalc (φ b) (smoothRepresentation I π g v) from Subtype.ext (hb v)]
  | add a b ha hb =>
    simp only [map_add, LinearMap.add_apply, Submodule.coe_add]
    rw [ha, hb]

/-- Every element of the enveloping algebra has a formal adjoint on the smooth vectors of a
unitary representation. -/
theorem exists_formalAdjoint (hcalc : smoothVectorFieldCommutator I M)
    (hπ : ∀ g u v, ⟪π g u, π g v⟫_ℂ = ⟪u, v⟫_ℂ) (y : 𝔘) :
    ∃ y' : 𝔘, ∀ v w : smoothVectors I π,
      ⟪(envelopingAction π hcalc y v : E), (w : E)⟫_ℂ =
        ⟪(v : E), (envelopingAction π hcalc y' w : E)⟫_ℂ := by
  induction y using Langlands.Archimedean.InfinitesimalCharacter.envInduction with
  | algebraMap r =>
    refine ⟨algebraMap ℂ 𝔘 ((starRingEnd ℂ) r), fun v w => ?_⟩
    rw [envelopingAction_algebraMap, envelopingAction_algebraMap]
    simp [inner_smul_left, inner_smul_right]
  | «ι» Z =>
    induction Z using TensorProduct.inductionOn with
    | tmul c X =>
      refine ⟨UniversalEnvelopingAlgebra.ι ℂ ((-(starRingEnd ℂ) c) ⊗ₜ[ℝ] X), fun v w => ?_⟩
      rw [envelopingAction_ι_tmul, envelopingAction_ι_tmul, inner_smul_left, inner_smul_right,
        SmoothFunctionalOrbit.inner_lieDerivative_eq_neg π hπ v w X]
      simp
    | add Z₁ Z₂ h₁ h₂ =>
      obtain ⟨y₁, hy₁⟩ := h₁
      obtain ⟨y₂, hy₂⟩ := h₂
      refine ⟨y₁ + y₂, fun v w => ?_⟩
      simp only [map_add, LinearMap.add_apply, Submodule.coe_add, inner_add_left,
        inner_add_right, hy₁, hy₂]
  | mul a b ha hb =>
    obtain ⟨a', ha'⟩ := ha
    obtain ⟨b', hb'⟩ := hb
    refine ⟨b' * a', fun v w => ?_⟩
    simp only [map_mul, Module.End.mul_apply]
    rw [ha', hb']
  | add a b ha hb =>
    obtain ⟨a', ha'⟩ := ha
    obtain ⟨b', hb'⟩ := hb
    refine ⟨a' + b', fun v w => ?_⟩
    simp only [map_add, LinearMap.add_apply, Submodule.coe_add, inner_add_left,
      inner_add_right, ha', hb']

section Commuting

omit [CompleteSpace A] [LieGroup 𝓘(ℝ, A) (minSmoothness ℝ 3) M]

variable (σ : E →L[ℂ] E) (hσ : ∀ g v, σ (π g v) = π g (σ v))
include hσ

/-- A bounded operator commuting with `π` preserves smooth vectors. -/
theorem isSmoothVector_comm {v : E} (hv : IsSmoothVector I π v) : IsSmoothVector I π (σ v) := by
  have he : orbitMap π (σ v) = (σ.restrictScalars ℝ) ∘ orbitMap π v := by
    funext g
    simp [orbitMap, hσ]
  change ContMDiff I 𝓘(ℝ, E) ∞ (orbitMap π (σ v))
  rw [he]
  exact (σ.restrictScalars ℝ).contDiff.contMDiff.comp hv

/-- A bounded operator commuting with `π` commutes with the derivatives `dπ(X)`. -/
theorem lieDerivative_comm (X : A) {v : E} (hv : IsSmoothVector I π v) :
    lieDerivative I π X (σ v) = σ (lieDerivative I π X v) := by
  have he : orbitMap π (σ v) = (σ.restrictScalars ℝ) ∘ orbitMap π v := by
    funext g
    simp [orbitMap, hσ]
  have hf : MDifferentiableAt I 𝓘(ℝ, E) (orbitMap π v) 1 := hv.mdifferentiableAt (by simp)
  unfold lieDerivative
  rw [he, mfderiv_comp 1 (σ.restrictScalars ℝ).differentiableAt.mdifferentiableAt hf,
    ContinuousLinearMap.mfderiv_eq]
  rfl

/-- The restriction of a commuting bounded operator to the smooth vectors. -/
def smoothCommuting : smoothVectors I π →ₗ[ℂ] smoothVectors I π where
  toFun v := ⟨σ v, isSmoothVector_comm π σ hσ v.property⟩
  map_add' v w := Subtype.ext (map_add σ (v : E) (w : E))
  map_smul' c v := Subtype.ext (map_smul σ c (v : E))

variable [CompleteSpace A] [LieGroup 𝓘(ℝ, A) (minSmoothness ℝ 3) M] in
/-- A bounded operator commuting with `π` commutes with the enveloping action. -/
theorem envelopingAction_comm (hcalc : smoothVectorFieldCommutator I M) (y : 𝔘)
    (v : smoothVectors I π) :
    σ (envelopingAction π hcalc y v) = envelopingAction π hcalc y (smoothCommuting π σ hσ v) := by
  induction y using Langlands.Archimedean.InfinitesimalCharacter.envInduction generalizing v with
  | algebraMap r =>
    rw [envelopingAction_algebraMap, envelopingAction_algebraMap]
    simp [smoothCommuting]
  | «ι» Z =>
    revert v
    induction Z using TensorProduct.inductionOn with
    | tmul c X =>
      intro v
      rw [envelopingAction_ι_tmul, envelopingAction_ι_tmul, map_smul]
      simp only [smoothCommuting, LinearMap.coe_mk, AddHom.coe_mk]
      rw [lieDerivative_comm π σ hσ (show A from X) v.property]
    | add Z₁ Z₂ h₁ h₂ =>
      intro v
      simp only [map_add, LinearMap.add_apply, Submodule.coe_add]
      rw [h₁, h₂]
  | mul a b ha hb =>
    simp only [map_mul, Module.End.mul_apply]
    rw [ha, show smoothCommuting π σ hσ (envelopingAction π hcalc b v) =
      envelopingAction π hcalc b (smoothCommuting π σ hσ v) from Subtype.ext (hb v)]
  | add a b ha hb =>
    simp only [map_add, LinearMap.add_apply, Submodule.coe_add]
    rw [ha, hb]

end Commuting

/-- **Transfer to coefficients.** Let `Θ` be an action of the enveloping algebra on a space `S`
of functions on `M` in which `ι (1 ⊗ X)` acts by the differentiation `groupDirectionalValue X`.
Let `W` be a space of smooth vectors stable under every `dπ(X)` and `ℓ` a linear form whose
coefficients `g ↦ ℓ (π g w)`, `w ∈ W`, lie in `S` and are differentiated by differentiating `w`.
Then `Θ y` maps the coefficient of `w` to the coefficient of `dπ(y) w`, for every `y`. -/
theorem envelopingAction_coefficient (hcalc : smoothVectorFieldCommutator I M)
    (S : Submodule ℂ (M → ℂ)) (Θ : 𝔘 →ₐ[ℂ] Module.End ℂ S)
    (hΘ : ∀ (X : GroupLieAlgebra I M) (f : S),
      ((Θ (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)) f : S) : M → ℂ) =
        groupDirectionalValue I X f)
    (W : Submodule ℂ (smoothVectors I π)) (hW : ∀ X, ∀ w ∈ W, smoothLieDerivative I π X w ∈ W)
    (ℓ : E →ₗ[ℂ] ℂ) (hS : ∀ w ∈ W, (fun g => ℓ (π g (w : E))) ∈ S)
    (hder : ∀ w ∈ W, ∀ (X : GroupLieAlgebra I M) (g : M),
      groupDirectionalValue I X (fun g => ℓ (π g (w : E))) g =
        ℓ (π g (lieDerivative I π X (w : E))))
    (y : 𝔘) (w : smoothVectors I π) (hw : w ∈ W) :
    envelopingAction π hcalc y w ∈ W ∧
      ((Θ y ⟨fun g => ℓ (π g (w : E)), hS w hw⟩ : S) : M → ℂ) =
        fun g => ℓ (π g (envelopingAction π hcalc y w : E)) := by
  induction y using Langlands.Archimedean.InfinitesimalCharacter.envInduction generalizing w with
  | algebraMap r =>
    rw [envelopingAction_algebraMap, Θ.commutes]
    refine ⟨W.smul_mem r hw, ?_⟩
    funext g
    simp
  | «ι» Z =>
    revert w
    induction Z using TensorProduct.inductionOn with
    | tmul c X =>
      intro w hw
      have hcX : c ⊗ₜ[ℝ] X = c • ((1 : ℂ) ⊗ₜ[ℝ] X) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      have hD : envelopingAction π hcalc (UniversalEnvelopingAlgebra.ι ℂ (c ⊗ₜ[ℝ] X)) w =
          c • smoothLieDerivative I π X w :=
        Subtype.ext (envelopingAction_ι_tmul π hcalc c X w)
      refine ⟨hD ▸ W.smul_mem c (hW X w hw), ?_⟩
      rw [hD, hcX, map_smul, map_smul, LinearMap.smul_apply, Submodule.coe_smul, hΘ]
      funext g
      simp only [Pi.smul_apply, smul_eq_mul, Submodule.coe_smul, map_smul,
        smoothLieDerivative_apply]
      rw [hder w hw X g]
    | add Z₁ Z₂ h₁ h₂ =>
      intro w hw
      obtain ⟨hw₁, he₁⟩ := h₁ w hw
      obtain ⟨hw₂, he₂⟩ := h₂ w hw
      simp only [map_add, LinearMap.add_apply, Submodule.coe_add]
      refine ⟨W.add_mem hw₁ hw₂, ?_⟩
      rw [he₁, he₂]
      funext g
      simp
  | mul a b ha hb =>
    obtain ⟨hwb, heb⟩ := hb w hw
    obtain ⟨hwa, hea⟩ := ha _ hwb
    simp only [map_mul, Module.End.mul_apply]
    refine ⟨hwa, ?_⟩
    rw [show Θ b ⟨fun g => ℓ (π g (w : E)), hS w hw⟩ =
      ⟨fun g => ℓ (π g (envelopingAction π hcalc b w : E)), hS _ hwb⟩ from Subtype.ext heb, hea]
  | add a b ha hb =>
    obtain ⟨hwa, hea⟩ := ha w hw
    obtain ⟨hwb, heb⟩ := hb w hw
    simp only [map_add, LinearMap.add_apply, Submodule.coe_add]
    refine ⟨W.add_mem hwa hwb, ?_⟩
    rw [hea, heb]
    funext g
    simp

end Langlands.Archimedean.SmoothVectorEnveloping
