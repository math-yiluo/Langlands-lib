import Langlands.AlgebraicGeometry.Modules.NoetherianCechProjectiveRepresentativeProof
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_nonempty_sections_top_equiv_H0_ofModules
import Langlands.CommutativeAlgebra.CokernelDualHom

/-! # The module `Q` of a linear system from a Čech projective representative -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.LinearSystemCechModule

open Scheme.TwoAffineOpenCover

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (.of R)) (M : X.Modules)
  (𝒰 : X.OrderedAffineCover)

/-- The Čech presheaf of `M` pulled back to the base change of `X` along `Spec A ⟶ Spec R`. -/
abbrev baseChangePresheaf (A : Type u) [CommRing A] [Algebra R A] :=
  OModulePresheaf.ofModules (pullback.snd π (specMap R A))
    ((Scheme.Modules.pullback (pullback.fst π (specMap R A))).obj M)

/-- The parts in degrees zero, one and two of a Čech projective representative of `M`, with its
comparison maps
after every base change (from `NoetherianCechProjectiveRepresentativeStatement`). -/
structure CechRep where
  /-- Degree-zero term. -/
  K₀ : Type u
  /-- Degree-one term. -/
  K₁ : Type u
  [addCommGroup₀ : AddCommGroup K₀]
  [module₀ : Module R K₀]
  [finite₀ : Module.Finite R K₀]
  [projective₀ : Module.Projective R K₀]
  [addCommGroup₁ : AddCommGroup K₁]
  [module₁ : Module R K₁]
  [finite₁ : Module.Finite R K₁]
  [projective₁ : Module.Projective R K₁]
  /-- The differential. -/
  δ : K₀ →ₗ[R] K₁
  /-- The comparison with Čech cochains over `R`. -/
  φ : K₀ →ₗ[R] (OModulePresheaf.ofModules π M).cochain 𝒰 0
  /-- The comparison with Čech cochains after base change. -/
  Θ : ∀ (A : Type u) [CommRing A] [Algebra R A],
    A ⊗[R] K₀ →ₗ[A] (baseChangePresheaf π M A).cochain (𝒰.baseChange π A) 0
  /-- The comparison sends `δ`-cocycles to Čech cocycles. -/
  Θ_cocycle : ∀ (A : Type u) [CommRing A] [Algebra R A] (x : A ⊗[R] K₀),
    δ.baseChange A x = 0 → (baseChangePresheaf π M A).d (𝒰.baseChange π A) 0 (Θ A x) = 0
  /-- Injectivity on cocycles. -/
  Θ_inj : ∀ (A : Type u) [CommRing A] [Algebra R A] (x : A ⊗[R] K₀),
    δ.baseChange A x = 0 → Θ A x = 0 → x = 0
  /-- Surjectivity onto cocycles. -/
  Θ_surj : ∀ (A : Type u) [CommRing A] [Algebra R A]
    (y : (baseChangePresheaf π M A).cochain (𝒰.baseChange π A) 0),
    (baseChangePresheaf π M A).d (𝒰.baseChange π A) 0 y = 0 →
      ∃ x : A ⊗[R] K₀, δ.baseChange A x = 0 ∧ Θ A x = y
  /-- The explicit formula: `Θ (a ⊗ k)` is `a` times the pulled-back cochain `φ k`. -/
  Θ_tmul : ∀ (A : Type u) [CommRing A] [Algebra R A] (a : A) (k : K₀) (s : 𝒰.Idx 0),
    Θ A (a ⊗ₜ[R] k) s = a • (baseChangePresheaf π M A).res (𝒰.baseChange_inter_le π A s)
      ((((Scheme.Modules.pullbackPushforwardAdjunction
        (pullback.fst π (specMap R A))).unit.app M).app (𝒰.inter s)).hom (φ k s))
  /-- Degree-two term. -/
  K₂ : Type u
  [addCommGroup₂ : AddCommGroup K₂]
  [module₂ : Module R K₂]
  [finite₂ : Module.Finite R K₂]
  [projective₂ : Module.Projective R K₂]
  /-- The second differential. -/
  δ₁ : K₁ →ₗ[R] K₂
  δ₁_comp_δ : δ₁ ∘ₗ δ = 0
  /-- The comparison in degree one after base change. -/
  Θ₁ : ∀ (A : Type u) [CommRing A] [Algebra R A],
    A ⊗[R] K₁ →ₗ[A] (baseChangePresheaf π M A).cochain (𝒰.baseChange π A) 1
  /-- Degree-one cocycles go to Čech cocycles. -/
  Θ₁_cocycle : ∀ (A : Type u) [CommRing A] [Algebra R A] (x : A ⊗[R] K₁),
    δ₁.baseChange A x = 0 → (baseChangePresheaf π M A).d (𝒰.baseChange π A) 1 (Θ₁ A x) = 0
  /-- Injectivity on `H¹`. -/
  Θ₁_exact : ∀ (A : Type u) [CommRing A] [Algebra R A] (x : A ⊗[R] K₁),
    δ₁.baseChange A x = 0 →
      Θ₁ A x ∈ LinearMap.range ((baseChangePresheaf π M A).d (𝒰.baseChange π A) 0) →
        x ∈ LinearMap.range (δ.baseChange A)

attribute [instance] CechRep.addCommGroup₀ CechRep.module₀ CechRep.finite₀ CechRep.projective₀
  CechRep.addCommGroup₁ CechRep.module₁ CechRep.finite₁ CechRep.projective₁
  CechRep.addCommGroup₂ CechRep.module₂ CechRep.finite₂ CechRep.projective₂

/-- A Čech representative exists for proper flat morphisms to noetherian affine schemes and
locally trivial modules. -/
theorem nonempty_cechRep [IsNoetherianRing R] [IsProper π] [Flat π]
    (htriv : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)) :
    Nonempty (CechRep π M 𝒰) := by
  obtain ⟨K, _, _, _, _, δ, hδδ, -, φ, -, Θ, -, -, -, -, hΘ⟩ :=
    Langlands.AlgebraicGeometry.Modules.noetherianCechProjectiveRepresentative π M htriv 𝒰
      (Fintype.card 𝒰.ι) (Nat.le_succ _)
  refine ⟨{
    K₀ := K 0
    K₁ := K 1
    δ := δ 0
    Θ := fun A => Θ A 0
    Θ_cocycle := fun A _ _ x hx => ?_
    Θ_inj := fun A _ _ x hx h0 => (hΘ A).2.2.1 x hx h0
    Θ_surj := fun A _ _ y hy => (hΘ A).2.2.2.1 y hy
    φ := φ 0
    Θ_tmul := fun A _ _ a k s => (hΘ A).2.1 0 a k s
    K₂ := K 2
    δ₁ := δ 1
    δ₁_comp_δ := hδδ 0
    Θ₁ := fun A => Θ A 1
    Θ₁_cocycle := fun A _ _ x hx => ?_
    Θ₁_exact := fun A _ _ x hx h => (hΘ A).2.2.2.2.1 0 x hx h }⟩
  · have h := congrArg (fun f => f x) ((hΘ A).1 0)
    simp only [LinearMap.coe_comp, Function.comp_apply] at h
    rw [← h, hx, map_zero]
  · have h := congrArg (fun f => f x) ((hΘ A).1 1)
    simp only [LinearMap.coe_comp, Function.comp_apply] at h
    rw [← h, hx, map_zero]

namespace CechRep

open P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_sections_top_equiv_H0_ofModules.AC3Aux

variable {π M 𝒰} (C : CechRep π M 𝒰) (A : Type u) [CommRing A] [Algebra R A]

/-- Restriction of global sections of the base-changed module to Čech `0`-cocycles, as a linear
equivalence. -/
def sectionsEquivH0 :
    letI := moduleSectionsOfHom (pullback.snd π (specMap R A))
      ((Scheme.Modules.pullback (pullback.fst π (specMap R A))).obj M) ⊤
    Γ((Scheme.Modules.pullback (pullback.fst π (specMap R A))).obj M, ⊤) ≃ₗ[A]
      (baseChangePresheaf π M A).H0 (𝒰.baseChange π A) :=
  LinearEquiv.ofBijective (toH0 _ _ (𝒰.baseChange π A))
    ⟨toH0_injective _ _ _, toH0_surjective _ _ _⟩

/-- The `δ`-cocycles of `A ⊗ K₀` are the Čech `0`-cocycles of the base change. -/
def kerEquivH0 :
    {x : A ⊗[R] C.K₀ // C.δ.lTensor A x = 0} ≃ (baseChangePresheaf π M A).H0 (𝒰.baseChange π A) where
  toFun x := ⟨C.Θ A x.1, C.Θ_cocycle A x.1 (by rw [LinearMap.baseChange_eq_ltensor]; exact x.2)⟩
  invFun y := ⟨(C.Θ_surj A y.1 y.2).choose, by
    rw [← LinearMap.baseChange_eq_ltensor]; exact (C.Θ_surj A y.1 y.2).choose_spec.1⟩
  left_inv x := by
    apply Subtype.ext
    have h := (C.Θ_surj A (C.Θ A x.1) (C.Θ_cocycle A x.1
      (by rw [LinearMap.baseChange_eq_ltensor]; exact x.2))).choose_spec
    rw [← sub_eq_zero]
    apply C.Θ_inj A
    · rw [map_sub, h.1, LinearMap.baseChange_eq_ltensor, x.2, sub_zero]
    · rw [map_sub, h.2, sub_self]
  right_inv y := by
    apply Subtype.ext
    exact (C.Θ_surj A y.1 y.2).choose_spec.2

/-- **The module `Q` of the linear system.** -/
abbrev Q : Type u := Langlands.CommutativeAlgebra.CokernelDualHom.Q C.δ

/-- `R`-linear maps `Q → A` are the global sections of the base change of `M` to `A`. -/
def homEquivSections : (C.Q →ₗ[R] A) ≃
    Γ((Scheme.Modules.pullback (pullback.fst π (specMap R A))).obj M, ⊤) :=
  (Langlands.CommutativeAlgebra.CokernelDualHom.homEquiv C.δ A).trans
    ((C.kerEquivH0 A).trans (sectionsEquivH0 (π := π) (M := M) (𝒰 := 𝒰) A).symm.toEquiv)

end CechRep

end Langlands.AlgebraicGeometry.Picard.LinearSystemCechModule
