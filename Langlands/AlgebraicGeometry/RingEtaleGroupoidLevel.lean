import Langlands.AlgebraicGeometry.RingEtaleGroupoidScheme

/-! # Level groupoids of multiplicative coactions

Let `t₀ : B₀ →+* C₀` be a ring étale groupoid and let `D` be a `B₀`-algebra with a
multiplicative coaction `θ : D → C₀ ⊗[B₀] D`. Then `θ` is a ring map, and together with
`d ↦ 1 ⊗ d` it is a ring étale groupoid on `D` with relation ring `C₀ ⊗[B₀] D`.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

namespace Langlands.AlgebraicGeometry

variable {B₀ C₀ D : Type u} [CommRing B₀] [CommRing C₀] [CommRing D] [Algebra B₀ C₀]
  [Algebra B₀ D]

namespace RingEtaleGroupoid

section Tensor

theorem tensor_ringHom_ext {T : Type*} [CommRing T] {f g : C₀ ⊗[B₀] D →+* T}
    (hl : ∀ c : C₀, f (c ⊗ₜ 1) = g (c ⊗ₜ 1)) (hr : ∀ d : D, f (1 ⊗ₜ d) = g (1 ⊗ₜ d)) :
    f = g := by
  refine RingHom.ext fun x => ?_
  induction x with
  | tmul c d =>
    have hcd : c ⊗ₜ[B₀] d = (c ⊗ₜ[B₀] (1 : D)) * ((1 : C₀) ⊗ₜ[B₀] d) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hcd, map_mul, map_mul, hl, hr]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- The ring map `C₀ ⊗[B₀] D →+* T`, `c ⊗ d ↦ φ c * ρ d`. -/
noncomputable def tensorLift {T : Type*} [CommRing T] (φ : C₀ →+* T) (ρ : D →+* T)
    (h : φ.comp (algebraMap B₀ C₀) = ρ.comp (algebraMap B₀ D)) : C₀ ⊗[B₀] D →+* T :=
  letI : Algebra B₀ T := (ρ.comp (algebraMap B₀ D)).toAlgebra
  (Algebra.TensorProduct.productMap
    { toRingHom := φ, commutes' := fun b => congrArg (fun f : B₀ →+* T => f b) h }
    { toRingHom := ρ, commutes' := fun _ => rfl }).toRingHom

@[simp]
theorem tensorLift_tmul {T : Type*} [CommRing T] (φ : C₀ →+* T) (ρ : D →+* T)
    (h : φ.comp (algebraMap B₀ C₀) = ρ.comp (algebraMap B₀ D)) (c : C₀) (d : D) :
    tensorLift φ ρ h (c ⊗ₜ d) = φ c * ρ d :=
  letI : Algebra B₀ T := (ρ.comp (algebraMap B₀ D)).toAlgebra
  Algebra.TensorProduct.productMap_apply_tmul _ _ c d

theorem algebraMap_tmul_one (b : B₀) :
    (algebraMap B₀ C₀ b) ⊗ₜ[B₀] (1 : D) = (1 : C₀) ⊗ₜ[B₀] (algebraMap B₀ D b) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

end Tensor

section Eval

variable {T : Type u} [CommRing T] [Algebra B₀ T]

/-- The multiplication map `T ⊗[B₀] D →ₐ[B₀] T`, `x ⊗ d ↦ x * ρ d`. -/
noncomputable def evalMap (ρ : D →ₐ[B₀] T) : T ⊗[B₀] D →ₐ[B₀] T :=
  Algebra.TensorProduct.productMap (AlgHom.id B₀ T) ρ

@[simp]
theorem evalMap_tmul (ρ : D →ₐ[B₀] T) (x : T) (d : D) : evalMap ρ (x ⊗ₜ d) = x * ρ d :=
  Algebra.TensorProduct.productMap_apply_tmul _ _ _ _

theorem evalMap_smul (ρ : D →ₐ[B₀] T) (y : T) (z : T ⊗[B₀] D) :
    evalMap ρ (y • z) = y * evalMap ρ z := by
  induction z with
  | tmul x d => rw [TensorProduct.smul_tmul', evalMap_tmul, evalMap_tmul, smul_eq_mul, mul_assoc]
  | add x z hx hz => rw [smul_add, map_add, map_add, hx, hz, mul_add]

theorem evalMap_rTensor (ρ : D →ₐ[B₀] T) (φ : C₀ →ₐ[B₀] T) (z : C₀ ⊗[B₀] D) :
    evalMap ρ (LinearMap.rTensor D φ.toLinearMap z) =
      Algebra.TensorProduct.productMap φ ρ z := by
  induction z with
  | tmul c d => simp
  | add x z hx hz => simp only [map_add, hx, hz]

variable {t₀ : B₀ →+* C₀}

theorem productMap_coaction_of_counit (θ : GroupoidCoaction t₀ D) (φ : C₀ →ₐ[B₀] T)
    (hφ : (φ : C₀ →+* T).comp t₀ = algebraMap B₀ T) (ρ : D →ₐ[B₀] T) (d : D) :
    Algebra.TensorProduct.productMap φ ρ (θ.coaction d) = ρ d := by
  rw [← evalMap_rTensor, θ.counit T φ hφ d, evalMap_tmul, one_mul]

theorem evalMap_coactionCompose (θ : GroupoidCoaction t₀ D) (φ₁ : C₀ →+* T)
    (φ₂ : C₀ →ₐ[B₀] T) (h : φ₁.comp (algebraMap B₀ C₀) = (φ₂ : C₀ →+* T).comp t₀)
    (ρ : D →ₐ[B₀] T) (ψ : C₀ ⊗[B₀] D →+* T) (hψl : ∀ c : C₀, ψ (c ⊗ₜ 1) = φ₁ c)
    (hψr : ∀ m : D, ψ (1 ⊗ₜ m) = Algebra.TensorProduct.productMap φ₂ ρ (θ.coaction m))
    (z : C₀ ⊗[B₀] D) :
    evalMap ρ (coactionCompose t₀ D θ.coaction θ.map_smul φ₁ φ₂ h z) = ψ z := by
  induction z with
  | tmul c m =>
    change evalMap ρ (φ₁ c • LinearMap.rTensor D φ₂.toLinearMap (θ.coaction m)) = _
    have hcm : c ⊗ₜ[B₀] m = (c ⊗ₜ[B₀] (1 : D)) * ((1 : C₀) ⊗ₜ[B₀] m) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [evalMap_smul, evalMap_rTensor, hcm, map_mul, hψl, hψr]
  | add x z hx hz => simp only [map_add, hx, hz]

end Eval

end RingEtaleGroupoid

namespace GroupoidCoaction

variable {t₀ : B₀ →+* C₀}

/-- A coaction on a `B₀`-algebra is multiplicative if it preserves `1` and products. -/
structure IsMultiplicative (θ : GroupoidCoaction t₀ D) : Prop where
  map_one : θ.coaction 1 = 1
  map_mul : ∀ x y : D, θ.coaction (x * y) = θ.coaction x * θ.coaction y

/-- A multiplicative coaction as a ring map. -/
def toRingHom (θ : GroupoidCoaction t₀ D) (hθ : θ.IsMultiplicative) : D →+* C₀ ⊗[B₀] D where
  toFun := θ.coaction
  map_one' := hθ.map_one
  map_mul' := hθ.map_mul
  map_zero' := θ.coaction.map_zero
  map_add' := θ.coaction.map_add

@[simp]
theorem toRingHom_apply (θ : GroupoidCoaction t₀ D) (hθ : θ.IsMultiplicative) (d : D) :
    θ.toRingHom hθ d = θ.coaction d :=
  rfl

theorem coaction_algebraMap (θ : GroupoidCoaction t₀ D) (hθ : θ.IsMultiplicative) (b : B₀) :
    θ.coaction (algebraMap B₀ D b) = t₀ b ⊗ₜ 1 := by
  rw [Algebra.algebraMap_eq_smul_one, θ.map_smul, hθ.map_one, Algebra.TensorProduct.one_def,
    TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end GroupoidCoaction


namespace RingEtaleGroupoid

/-- The target map of a ring étale groupoid is étale as soon as the source map is, by symmetry:
the inverse point `σ` with `σ ∘ t = s` and `σ ∘ s = t` is an involution. -/
theorem etale_of_symm {B C : Type u} [CommRing B] [CommRing C] [Algebra B C] {t : B →+* C}
    (hom_ext : ∀ {f g : C →+* C}, f.comp t = g.comp t →
      f.comp (algebraMap B C) = g.comp (algebraMap B C) → f = g)
    (symm : ∃ σ : C →+* C, σ.comp t = algebraMap B C ∧ σ.comp (algebraMap B C) = t)
    (hs : (algebraMap B C).Etale) : t.Etale := by
  obtain ⟨σ, hσt, hσs⟩ := symm
  have hσσ : σ.comp σ = RingHom.id C :=
    hom_ext (by rw [RingHom.comp_assoc, hσt, hσs, RingHom.id_comp])
      (by rw [RingHom.comp_assoc, hσs, hσt, RingHom.id_comp])
  have hbij : Function.Bijective σ := Function.bijective_iff_has_inverse.mpr
    ⟨σ, fun x => congrArg (fun h : C →+* C => h x) hσσ,
      fun x => congrArg (fun h : C →+* C => h x) hσσ⟩
  rw [← hσs]
  exact RingHom.Etale.stableUnderComposition _ _ hs (RingHom.Etale.of_bijective hbij)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {t₀ : B₀ →+* C₀}

theorem level_hom_ext (hE₀ : RingEtaleGroupoid t₀) (θ : GroupoidCoaction t₀ D)
    (hθ : θ.IsMultiplicative) {T : Type u} [CommRing T] {f g : C₀ ⊗[B₀] D →+* T}
    (ht : f.comp (θ.toRingHom hθ) = g.comp (θ.toRingHom hθ))
    (hs : f.comp (algebraMap D (C₀ ⊗[B₀] D)) = g.comp (algebraMap D (C₀ ⊗[B₀] D))) :
    f = g := by
  have hl : f.comp Algebra.TensorProduct.includeLeftRingHom =
      g.comp Algebra.TensorProduct.includeLeftRingHom := by
    apply hE₀.hom_ext
    · ext b
      change f (t₀ b ⊗ₜ 1) = g (t₀ b ⊗ₜ 1)
      rw [← θ.coaction_algebraMap hθ]
      exact congrArg (fun h : D →+* T => h (algebraMap B₀ D b)) ht
    · ext b
      change f (algebraMap B₀ C₀ b ⊗ₜ 1) = g (algebraMap B₀ C₀ b ⊗ₜ 1)
      rw [algebraMap_tmul_one]
      exact congrArg (fun h : D →+* T => h (algebraMap B₀ D b)) hs
  exact tensor_ringHom_ext (fun c => congrArg (fun h : C₀ →+* T => h c) hl)
    (fun d => congrArg (fun h : D →+* T => h d) hs)

theorem identity_point (hE₀ : RingEtaleGroupoid t₀) {T : Type u} [CommRing T] [Algebra B₀ T] :
    (((Algebra.ofId B₀ T).comp hE₀.identity : C₀ →ₐ[B₀] T) : C₀ →+* T).comp t₀ =
      algebraMap B₀ T := by
  ext b
  change algebraMap B₀ T (hE₀.identity (t₀ b)) = algebraMap B₀ T b
  rw [show hE₀.identity (t₀ b) = b from
    congrArg (fun h : B₀ →+* B₀ => h b) hE₀.identity_comp_t]

theorem level_refl (hE₀ : RingEtaleGroupoid t₀) (θ : GroupoidCoaction t₀ D)
    (hθ : θ.IsMultiplicative) (T : Type u) [CommRing T] (a : D →+* T) :
    ∃ φ : C₀ ⊗[B₀] D →+* T, φ.comp (θ.toRingHom hθ) = a ∧
      φ.comp (algebraMap D (C₀ ⊗[B₀] D)) = a := by
  let : Algebra B₀ T := (a.comp (algebraMap B₀ D)).toAlgebra
  let aₐ : D →ₐ[B₀] T := { toRingHom := a, commutes' := fun _ => rfl }
  let φ₁ : C₀ →ₐ[B₀] T := (Algebra.ofId B₀ T).comp hE₀.identity
  refine ⟨(Algebra.TensorProduct.productMap φ₁ aₐ).toRingHom, ?_, ?_⟩
  · ext d
    exact productMap_coaction_of_counit θ φ₁ hE₀.identity_point aₐ d
  · ext d
    change Algebra.TensorProduct.productMap φ₁ aₐ (1 ⊗ₜ d) = a d
    rw [Algebra.TensorProduct.productMap_apply_tmul, map_one, one_mul]
    rfl

theorem level_symm (hE₀ : RingEtaleGroupoid t₀) (θ : GroupoidCoaction t₀ D)
    (hθ : θ.IsMultiplicative) (T : Type u) [CommRing T] (φ : C₀ ⊗[B₀] D →+* T) :
    ∃ ψ : C₀ ⊗[B₀] D →+* T,
      ψ.comp (θ.toRingHom hθ) = φ.comp (algebraMap D (C₀ ⊗[B₀] D)) ∧
        ψ.comp (algebraMap D (C₀ ⊗[B₀] D)) = φ.comp (θ.toRingHom hθ) := by
  let a : D →+* T := φ.comp (algebraMap D (C₀ ⊗[B₀] D))
  let b : D →+* T := φ.comp (θ.toRingHom hθ)
  let φ₁ : C₀ →+* T := φ.comp Algebra.TensorProduct.includeLeftRingHom
  obtain ⟨ψ₀, hψ₀t, hψ₀s⟩ := hE₀.symm T φ₁
  have hb : φ₁.comp t₀ = b.comp (algebraMap B₀ D) := by
    ext x
    change φ (t₀ x ⊗ₜ 1) = φ (θ.coaction (algebraMap B₀ D x))
    rw [θ.coaction_algebraMap hθ]
  have hφ₁s : φ₁.comp (algebraMap B₀ C₀) = a.comp (algebraMap B₀ D) := by
    ext x
    change φ (algebraMap B₀ C₀ x ⊗ₜ 1) = φ (1 ⊗ₜ algebraMap B₀ D x)
    rw [algebraMap_tmul_one]
  refine ⟨tensorLift ψ₀ b (hψ₀s.trans hb), ?_, ?_⟩
  · ext d
    let : Algebra B₀ T := (a.comp (algebraMap B₀ D)).toAlgebra
    let aₐ : D →ₐ[B₀] T := { toRingHom := a, commutes' := fun _ => rfl }
    let φ₁ₐ : C₀ →ₐ[B₀] T :=
      { toRingHom := φ₁, commutes' := fun x => congrArg (fun h : B₀ →+* T => h x) hφ₁s }
    let φ₃ : C₀ →ₐ[B₀] T := (Algebra.ofId B₀ T).comp hE₀.identity
    have h₃ : (φ₃ : C₀ →+* T).comp t₀ = ψ₀.comp t₀ := by
      rw [hE₀.identity_point, hψ₀t, hφ₁s]
      rfl
    have hprod : (Algebra.TensorProduct.productMap φ₁ₐ aₐ : C₀ ⊗[B₀] D →+* T) = φ := by
      refine tensor_ringHom_ext (fun c => ?_) (fun m => ?_)
      · change Algebra.TensorProduct.productMap φ₁ₐ aₐ (c ⊗ₜ 1) = φ (c ⊗ₜ 1)
        rw [Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one]
        rfl
      · change Algebra.TensorProduct.productMap φ₁ₐ aₐ (1 ⊗ₜ m) = φ (1 ⊗ₜ m)
        rw [Algebra.TensorProduct.productMap_apply_tmul, map_one, one_mul]
        rfl
    have key := θ.coassoc T ψ₀ φ₁ₐ φ₃ hψ₀s h₃ d
    have hev := congrArg (evalMap aₐ) key
    rw [evalMap_rTensor, productMap_coaction_of_counit θ φ₃ hE₀.identity_point aₐ d,
      evalMap_coactionCompose θ ψ₀ φ₁ₐ hψ₀s aₐ (tensorLift ψ₀ b (hψ₀s.trans hb))
        (fun c => ?_) (fun m => ?_)] at hev
    · exact hev.symm
    · rw [tensorLift_tmul, map_one, mul_one]
    · rw [tensorLift_tmul, map_one, one_mul]
      exact (congrArg (fun h : C₀ ⊗[B₀] D →+* T => h (θ.coaction m)) hprod).symm
  · ext d
    change tensorLift ψ₀ b (hψ₀s.trans hb) (1 ⊗ₜ d) = b d
    rw [tensorLift_tmul, map_one, one_mul]

theorem level_trans (hE₀ : RingEtaleGroupoid t₀) (θ : GroupoidCoaction t₀ D)
    (hθ : θ.IsMultiplicative) (T : Type u) [CommRing T] (φ ψ : C₀ ⊗[B₀] D →+* T)
    (hφψ : φ.comp (algebraMap D (C₀ ⊗[B₀] D)) = ψ.comp (θ.toRingHom hθ)) :
    ∃ χ : C₀ ⊗[B₀] D →+* T, χ.comp (θ.toRingHom hθ) = φ.comp (θ.toRingHom hθ) ∧
      χ.comp (algebraMap D (C₀ ⊗[B₀] D)) = ψ.comp (algebraMap D (C₀ ⊗[B₀] D)) := by
  let φ₁ : C₀ →+* T := φ.comp Algebra.TensorProduct.includeLeftRingHom
  let ψ₁ : C₀ →+* T := ψ.comp Algebra.TensorProduct.includeLeftRingHom
  let ρ : D →+* T := ψ.comp (algebraMap D (C₀ ⊗[B₀] D))
  have h₀ : φ₁.comp (algebraMap B₀ C₀) = ψ₁.comp t₀ := by
    ext x
    change φ (algebraMap B₀ C₀ x ⊗ₜ 1) = ψ (t₀ x ⊗ₜ 1)
    rw [algebraMap_tmul_one, ← θ.coaction_algebraMap hθ]
    exact congrArg (fun h : D →+* T => h (algebraMap B₀ D x)) hφψ
  obtain ⟨κ, hκt, hκs⟩ := hE₀.trans T φ₁ ψ₁ h₀
  have hψ₁s : ψ₁.comp (algebraMap B₀ C₀) = ρ.comp (algebraMap B₀ D) := by
    ext x
    change ψ (algebraMap B₀ C₀ x ⊗ₜ 1) = ψ (1 ⊗ₜ algebraMap B₀ D x)
    rw [algebraMap_tmul_one]
  have hκρ : κ.comp (algebraMap B₀ C₀) = ρ.comp (algebraMap B₀ D) := hκs.trans hψ₁s
  refine ⟨tensorLift κ ρ hκρ, ?_, ?_⟩
  · ext d
    let : Algebra B₀ T := (ρ.comp (algebraMap B₀ D)).toAlgebra
    let ρₐ : D →ₐ[B₀] T := { toRingHom := ρ, commutes' := fun _ => rfl }
    let ψ₁ₐ : C₀ →ₐ[B₀] T :=
      { toRingHom := ψ₁, commutes' := fun x => congrArg (fun h : B₀ →+* T => h x) hψ₁s }
    let κₐ : C₀ →ₐ[B₀] T :=
      { toRingHom := κ, commutes' := fun x => congrArg (fun h : B₀ →+* T => h x) hκρ }
    have hprodψ : (Algebra.TensorProduct.productMap ψ₁ₐ ρₐ : C₀ ⊗[B₀] D →+* T) = ψ := by
      refine tensor_ringHom_ext (fun c => ?_) (fun m => ?_)
      · change Algebra.TensorProduct.productMap ψ₁ₐ ρₐ (c ⊗ₜ 1) = ψ (c ⊗ₜ 1)
        rw [Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one]
        rfl
      · change Algebra.TensorProduct.productMap ψ₁ₐ ρₐ (1 ⊗ₜ m) = ψ (1 ⊗ₜ m)
        rw [Algebra.TensorProduct.productMap_apply_tmul, map_one, one_mul]
        rfl
    have hprodκ : (Algebra.TensorProduct.productMap κₐ ρₐ : C₀ ⊗[B₀] D →+* T) =
        tensorLift κ ρ hκρ := by
      refine tensor_ringHom_ext (fun c => ?_) (fun m => ?_)
      · change Algebra.TensorProduct.productMap κₐ ρₐ (c ⊗ₜ 1) = tensorLift κ ρ hκρ (c ⊗ₜ 1)
        rw [Algebra.TensorProduct.productMap_apply_tmul, tensorLift_tmul]
        rfl
      · change Algebra.TensorProduct.productMap κₐ ρₐ (1 ⊗ₜ m) = tensorLift κ ρ hκρ (1 ⊗ₜ m)
        rw [Algebra.TensorProduct.productMap_apply_tmul, tensorLift_tmul]
        rfl
    have key := θ.coassoc T φ₁ ψ₁ₐ κₐ h₀ hκt d
    have hev := congrArg (evalMap ρₐ) key
    rw [evalMap_rTensor, evalMap_coactionCompose θ φ₁ ψ₁ₐ h₀ ρₐ φ (fun c => rfl)
      (fun m => ?_)] at hev
    · change tensorLift κ ρ hκρ (θ.coaction d) = φ (θ.coaction d)
      rw [← hprodκ]
      exact hev
    · rw [show Algebra.TensorProduct.productMap ψ₁ₐ ρₐ (θ.coaction m) = ψ (θ.coaction m) from
        congrArg (fun h : C₀ ⊗[B₀] D →+* T => h (θ.coaction m)) hprodψ]
      exact congrArg (fun h : D →+* T => h m) hφψ
  · ext d
    change tensorLift κ ρ hκρ (1 ⊗ₜ d) = ρ d
    rw [tensorLift_tmul, map_one, one_mul]

theorem level_etale_algebraMap (hE₀ : RingEtaleGroupoid t₀) :
    (algebraMap D (C₀ ⊗[B₀] D)).Etale :=
  RingHom.Etale.isStableUnderBaseChange B₀ C₀ D (C₀ ⊗[B₀] D) hE₀.etale_algebraMap

/-- A multiplicative coaction of a ring étale groupoid `t₀ : B₀ →+* C₀` on a `B₀`-algebra `D`
gives the ring étale groupoid `D →+* C₀ ⊗[B₀] D` with source map `d ↦ 1 ⊗ d` and target map
the coaction. -/
theorem level (hE₀ : RingEtaleGroupoid t₀) (θ : GroupoidCoaction t₀ D)
    (hθ : θ.IsMultiplicative) : RingEtaleGroupoid (θ.toRingHom hθ) where
  hom_ext ht hs := level_hom_ext hE₀ θ hθ ht hs
  refl := level_refl hE₀ θ hθ
  symm := level_symm hE₀ θ hθ
  trans := level_trans hE₀ θ hθ
  etale_algebraMap := level_etale_algebraMap hE₀
  etale_t := etale_of_symm (fun ht hs => level_hom_ext hE₀ θ hθ ht hs)
    (by
      obtain ⟨σ, h1, h2⟩ := level_symm hE₀ θ hθ _ (RingHom.id _)
      exact ⟨σ, by simpa using h1, by simpa using h2⟩)
    (level_etale_algebraMap hE₀)

end RingEtaleGroupoid


namespace RingEtaleGroupoid

/-- Transport of a ring étale groupoid along a ring isomorphism of relation rings that is
compatible with the source algebra structures. -/
theorem ofRingEquiv {B C C' : Type u} [CommRing B] [CommRing C] [CommRing C'] [Algebra B C]
    [Algebra B C'] {t : B →+* C} (hG : RingEtaleGroupoid t) (e : C ≃+* C')
    (he : e.toRingHom.comp (algebraMap B C) = algebraMap B C') :
    RingEtaleGroupoid (e.toRingHom.comp t) where
  hom_ext {T} _ f g ht hs := by
    have hfg : f.comp e.toRingHom = g.comp e.toRingHom := hG.hom_ext
      (by rw [RingHom.comp_assoc, RingHom.comp_assoc]; exact ht)
      (by rw [RingHom.comp_assoc, RingHom.comp_assoc, he]; exact hs)
    ext x
    have := congrArg (fun h : C →+* T => h (e.symm x)) hfg
    simpa using this
  refl T _ a := by
    obtain ⟨φ, h1, h2⟩ := hG.refl T a
    refine ⟨φ.comp e.symm.toRingHom, ?_, ?_⟩
    · ext b
      simpa using congrArg (fun h : B →+* T => h b) h1
    · ext b
      have := congrArg (fun h : B →+* T => h b) h2
      rw [← he]
      simpa using this
  symm T _ φ := by
    obtain ⟨ψ, h1, h2⟩ := hG.symm T (φ.comp e.toRingHom)
    refine ⟨ψ.comp e.symm.toRingHom, ?_, ?_⟩
    · ext b
      have := congrArg (fun h : B →+* T => h b) h1
      rw [← he]
      simpa using this
    · ext b
      have := congrArg (fun h : B →+* T => h b) h2
      rw [← he]
      simpa using this
  trans T _ φ ψ h := by
    obtain ⟨χ, h1, h2⟩ := hG.trans T (φ.comp e.toRingHom) (ψ.comp e.toRingHom)
      (by rw [RingHom.comp_assoc, RingHom.comp_assoc, he]; exact h)
    refine ⟨χ.comp e.symm.toRingHom, ?_, ?_⟩
    · ext b
      have := congrArg (fun h : B →+* T => h b) h1
      simpa using this
    · ext b
      have := congrArg (fun h : B →+* T => h b) h2
      rw [← he]
      simpa using this
  etale_algebraMap := by
    rw [← he]
    exact RingHom.Etale.respectsIso.1 _ e hG.etale_algebraMap
  etale_t := RingHom.Etale.respectsIso.1 _ e hG.etale_t

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {t₀ : B₀ →+* C₀}

theorem rTensor_eq_map {T : Type u} [CommRing T] [Algebra B₀ T] (φ : C₀ →ₐ[B₀] T)
    (z : C₀ ⊗[B₀] D) :
    LinearMap.rTensor D φ.toLinearMap z = Algebra.TensorProduct.map φ (AlgHom.id B₀ D) z := by
  induction z with
  | tmul c d => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem smul_eq_tmul_one_mul {T : Type u} [CommRing T] [Algebra B₀ T] (y : T)
    (z : T ⊗[B₀] D) : y • z = (y ⊗ₜ[B₀] (1 : D)) * z := by
  induction z with
  | tmul x d =>
    rw [TensorProduct.smul_tmul', Algebra.TensorProduct.tmul_mul_tmul, one_mul, smul_eq_mul]
  | add x z hx hz => rw [smul_add, mul_add, hx, hz]

/-- Conversely, a ring étale groupoid `τ : D →+* C₀ ⊗[B₀] D` with source map `d ↦ 1 ⊗ d`,
whose target map is `t₀`-semilinear, is a coaction of the groupoid `t₀` on `D`. -/
noncomputable def coactionOfLevel (hE₀ : RingEtaleGroupoid t₀) (τ : D →+* C₀ ⊗[B₀] D)
    (hτ : ∀ b : B₀, τ (algebraMap B₀ D b) = t₀ b ⊗ₜ 1) (hG : RingEtaleGroupoid τ) :
    GroupoidCoaction t₀ D where
  coaction := τ.toAddMonoidHom
  map_smul b m := by
    change τ (b • m) = t₀ b • τ m
    rw [Algebra.smul_def, map_mul, hτ, smul_eq_tmul_one_mul]
  counit T _ _ φ hφ m := by
    change LinearMap.rTensor D φ.toLinearMap (τ m) = (1 : T) ⊗ₜ m
    rw [rTensor_eq_map]
    obtain ⟨ρ, hρt, hρs⟩ := hG.refl (T ⊗[B₀] D) Algebra.TensorProduct.includeRight.toRingHom
    have hl : ρ.comp Algebra.TensorProduct.includeLeftRingHom =
        ((Algebra.TensorProduct.map φ (AlgHom.id B₀ D) : C₀ ⊗[B₀] D →ₐ[B₀] T ⊗[B₀] D) :
          C₀ ⊗[B₀] D →+* T ⊗[B₀] D).comp Algebra.TensorProduct.includeLeftRingHom := by
      apply hE₀.hom_ext
      · ext b
        change ρ (t₀ b ⊗ₜ 1) = φ (t₀ b) ⊗ₜ 1
        rw [← hτ, show ρ (τ (algebraMap B₀ D b)) = 1 ⊗ₜ algebraMap B₀ D b from
          congrArg (fun h : D →+* T ⊗[B₀] D => h (algebraMap B₀ D b)) hρt,
          show φ (t₀ b) = algebraMap B₀ T b from congrArg (fun h : B₀ →+* T => h b) hφ,
          algebraMap_tmul_one]
      · ext b
        change ρ (algebraMap B₀ C₀ b ⊗ₜ 1) = φ (algebraMap B₀ C₀ b) ⊗ₜ 1
        rw [algebraMap_tmul_one, AlgHom.commutes, algebraMap_tmul_one]
        exact congrArg (fun h : D →+* T ⊗[B₀] D => h (algebraMap B₀ D b)) hρs
    have hρ : ρ = ((Algebra.TensorProduct.map φ (AlgHom.id B₀ D) :
        C₀ ⊗[B₀] D →ₐ[B₀] T ⊗[B₀] D) : C₀ ⊗[B₀] D →+* T ⊗[B₀] D) := by
      refine tensor_ringHom_ext (fun c => congrArg (fun h : C₀ →+* T ⊗[B₀] D => h c) hl)
        (fun d => ?_)
      change ρ (1 ⊗ₜ d) = φ 1 ⊗ₜ d
      rw [map_one]
      exact congrArg (fun h : D →+* T ⊗[B₀] D => h d) hρs
    rw [show Algebra.TensorProduct.map φ (AlgHom.id B₀ D) (τ m) = ρ (τ m) from
      (congrArg (fun h : C₀ ⊗[B₀] D →+* T ⊗[B₀] D => h (τ m)) hρ).symm]
    exact congrArg (fun h : D →+* T ⊗[B₀] D => h m) hρt
  coassoc T _ _ φ₁ φ₂ φ₃ h h₃ m := by
    change LinearMap.rTensor D φ₃.toLinearMap (τ m) =
      coactionCompose t₀ D τ.toAddMonoidHom _ φ₁ φ₂ h (τ m)
    let Ψ₂ : C₀ ⊗[B₀] D →+* T ⊗[B₀] D :=
      ((Algebra.TensorProduct.map φ₂ (AlgHom.id B₀ D) : C₀ ⊗[B₀] D →ₐ[B₀] T ⊗[B₀] D) :
        C₀ ⊗[B₀] D →+* T ⊗[B₀] D)
    let Ψ₃ : C₀ ⊗[B₀] D →+* T ⊗[B₀] D :=
      ((Algebra.TensorProduct.map φ₃ (AlgHom.id B₀ D) : C₀ ⊗[B₀] D →ₐ[B₀] T ⊗[B₀] D) :
        C₀ ⊗[B₀] D →+* T ⊗[B₀] D)
    have hc : (Algebra.TensorProduct.includeLeftRingHom.comp φ₁).comp (algebraMap B₀ C₀) =
        (Ψ₂.comp τ).comp (algebraMap B₀ D) := by
      ext b
      change φ₁ (algebraMap B₀ C₀ b) ⊗ₜ 1 = Ψ₂ (τ (algebraMap B₀ D b))
      rw [hτ]
      change φ₁ (algebraMap B₀ C₀ b) ⊗ₜ 1 = φ₂ (t₀ b) ⊗ₜ 1
      rw [show φ₁ (algebraMap B₀ C₀ b) = φ₂ (t₀ b) from congrArg (fun f : B₀ →+* T => f b) h]
    let Ψ₁ : C₀ ⊗[B₀] D →+* T ⊗[B₀] D :=
      tensorLift (Algebra.TensorProduct.includeLeftRingHom.comp φ₁) (Ψ₂.comp τ) hc
    have h12 : Ψ₁.comp (algebraMap D (C₀ ⊗[B₀] D)) = Ψ₂.comp τ := by
      ext d
      change tensorLift _ _ hc (1 ⊗ₜ d) = Ψ₂ (τ d)
      rw [tensorLift_tmul, map_one, one_mul]
      rfl
    obtain ⟨χ, hχt, hχs⟩ := hG.trans (T ⊗[B₀] D) Ψ₁ Ψ₂ h12
    have hl : χ.comp Algebra.TensorProduct.includeLeftRingHom =
        Ψ₃.comp Algebra.TensorProduct.includeLeftRingHom := by
      apply hE₀.hom_ext
      · ext b
        change χ (t₀ b ⊗ₜ 1) = φ₃ (t₀ b) ⊗ₜ 1
        rw [← hτ, show χ (τ (algebraMap B₀ D b)) = Ψ₁ (τ (algebraMap B₀ D b)) from
          congrArg (fun f : D →+* T ⊗[B₀] D => f (algebraMap B₀ D b)) hχt, hτ]
        change tensorLift _ _ hc (t₀ b ⊗ₜ 1) = _
        rw [tensorLift_tmul, map_one, mul_one]
        change φ₁ (t₀ b) ⊗ₜ 1 = φ₃ (t₀ b) ⊗ₜ 1
        rw [show φ₃ (t₀ b) = φ₁ (t₀ b) from congrArg (fun f : B₀ →+* T => f b) h₃]
      · ext b
        change χ (algebraMap B₀ C₀ b ⊗ₜ 1) = φ₃ (algebraMap B₀ C₀ b) ⊗ₜ 1
        rw [algebraMap_tmul_one, AlgHom.commutes, algebraMap_tmul_one,
          show χ (1 ⊗ₜ algebraMap B₀ D b) = Ψ₂ (1 ⊗ₜ algebraMap B₀ D b) from
            congrArg (fun f : D →+* T ⊗[B₀] D => f (algebraMap B₀ D b)) hχs]
        change φ₂ 1 ⊗ₜ algebraMap B₀ D b = 1 ⊗ₜ algebraMap B₀ D b
        rw [map_one]
    have hχ : χ = Ψ₃ := by
      refine tensor_ringHom_ext (fun c => congrArg (fun f : C₀ →+* T ⊗[B₀] D => f c) hl)
        (fun d => ?_)
      rw [show χ (1 ⊗ₜ d) = Ψ₂ (1 ⊗ₜ d) from
        congrArg (fun f : D →+* T ⊗[B₀] D => f d) hχs]
      change φ₂ 1 ⊗ₜ d = φ₃ 1 ⊗ₜ d
      rw [map_one, map_one]
    rw [rTensor_eq_map]
    change Ψ₃ (τ m) = _
    rw [← hχ, show χ (τ m) = Ψ₁ (τ m) from congrArg (fun f : D →+* T ⊗[B₀] D => f m) hχt]
    generalize τ m = z
    induction z with
    | tmul c d =>
      change tensorLift _ _ hc (c ⊗ₜ d) = φ₁ c • LinearMap.rTensor D φ₂.toLinearMap (τ d)
      rw [tensorLift_tmul, smul_eq_tmul_one_mul, rTensor_eq_map]
      rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]

@[simp]
theorem coactionOfLevel_coaction (hE₀ : RingEtaleGroupoid t₀) (τ : D →+* C₀ ⊗[B₀] D)
    (hτ : ∀ b : B₀, τ (algebraMap B₀ D b) = t₀ b ⊗ₜ 1) (hG : RingEtaleGroupoid τ) (d : D) :
    (hE₀.coactionOfLevel τ hτ hG).coaction d = τ d :=
  rfl

theorem coactionOfLevel_isMultiplicative (hE₀ : RingEtaleGroupoid t₀) (τ : D →+* C₀ ⊗[B₀] D)
    (hτ : ∀ b : B₀, τ (algebraMap B₀ D b) = t₀ b ⊗ₜ 1) (hG : RingEtaleGroupoid τ) :
    (hE₀.coactionOfLevel τ hτ hG).IsMultiplicative where
  map_one := map_one τ
  map_mul := map_mul τ

/-- An equivariant map of algebras with coactions gives a cartesian morphism of the
corresponding étale equivalence relations. -/
theorem isCartesianHom_of_equivariant {D' : Type u} [CommRing D'] [Algebra B₀ D']
    {τ : D →+* C₀ ⊗[B₀] D} {τ' : D' →+* C₀ ⊗[B₀] D'} (hG : RingEtaleGroupoid τ)
    (hG' : RingEtaleGroupoid τ') (φ : D →ₐ[B₀] D')
    (hφ : ∀ d : D, Algebra.TensorProduct.map (AlgHom.id B₀ C₀) φ (τ d) = τ' (φ d)) :
    EtaleEquivalenceRelation.IsCartesianHom hG'.toScheme hG.toScheme
      (Spec.map (CommRingCat.ofHom (φ : D →+* D')))
      (Spec.map (CommRingCat.ofHom
        ((Algebra.TensorProduct.map (AlgHom.id B₀ C₀) φ : C₀ ⊗[B₀] D →ₐ[B₀] C₀ ⊗[B₀] D') :
          C₀ ⊗[B₀] D →+* C₀ ⊗[B₀] D'))) := by
  constructor
  · change Spec.map (CommRingCat.ofHom
        ((Algebra.TensorProduct.map (AlgHom.id B₀ C₀) φ : C₀ ⊗[B₀] D →ₐ[B₀] C₀ ⊗[B₀] D') :
          C₀ ⊗[B₀] D →+* C₀ ⊗[B₀] D')) ≫ Spec.map (CommRingCat.ofHom τ) =
      Spec.map (CommRingCat.ofHom τ') ≫ Spec.map (CommRingCat.ofHom (φ : D →+* D'))
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext d
    exact hφ d
  · apply isPullback_SpecMap_of_isPushout
    have e1 : CommRingCat.ofHom (algebraMap B₀ D) ≫ CommRingCat.ofHom (φ : D →+* D') =
        CommRingCat.ofHom (algebraMap B₀ D') := by
      ext b
      exact φ.commutes b
    have e2 : CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom : C₀ →+* C₀ ⊗[B₀] D) ≫
        CommRingCat.ofHom
          ((Algebra.TensorProduct.map (AlgHom.id B₀ C₀) φ : C₀ ⊗[B₀] D →ₐ[B₀] C₀ ⊗[B₀] D') :
            C₀ ⊗[B₀] D →+* C₀ ⊗[B₀] D') =
        CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : C₀ →+* C₀ ⊗[B₀] D') := by
      ext c
      change Algebra.TensorProduct.map (AlgHom.id B₀ C₀) φ (c ⊗ₜ 1) = c ⊗ₜ 1
      rw [Algebra.TensorProduct.map_tmul, map_one]
      rfl
    refine IsPushout.of_top (h₁₁ := CommRingCat.ofHom (algebraMap B₀ C₀))
      (v₁₁ := CommRingCat.ofHom (algebraMap B₀ D))
      (v₁₂ := CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ?_ ?_
      (CommRingCat.isPushout_tensorProduct B₀ C₀ D)
    · rw [e1, e2]
      exact CommRingCat.isPushout_tensorProduct B₀ C₀ D'
    · ext d
      change Algebra.TensorProduct.map (AlgHom.id B₀ C₀) φ (1 ⊗ₜ d) = 1 ⊗ₜ φ d
      rw [Algebra.TensorProduct.map_tmul, map_one]

end RingEtaleGroupoid

end Langlands.AlgebraicGeometry
