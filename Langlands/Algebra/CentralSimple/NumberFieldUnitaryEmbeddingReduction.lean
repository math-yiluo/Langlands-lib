import Langlands.Algebra.CentralSimple.NumberFieldUnitaryEmbeddingStatement
import Langlands.Algebra.CentralSimple.NumberFieldLandherrStatement
import Langlands.Algebra.CentralSimple.NumberFieldLocalGlobalEmbeddingStatement
import Langlands.Algebra.CentralSimple.MaximalSubfieldConjugacyStatement
import Langlands.Algebra.CentralSimple.NumberFieldUnitaryEmbeddingClassStatement

/-! # The unitary embedding theorem from Landherr's theorem and a global twist class -/

noncomputable section

universe u

open scoped TensorProduct

namespace Langlands.CentralSimple

open Langlands.GroupScheme.Quaternionic Langlands.GroupScheme.SU3Root

/-- **The unitary embedding theorem from four premises.** Landherr's theorem, the
local–global principle for embeddings of maximal subfields, Skolem–Noether conjugacy and
self-centralization of maximal subfields after scalar extension, and the existence of global
fixed-field twists with everywhere local unitary solutions together imply the local–global
principle for embeddings of fields with involution into central simple algebras with unitary
involution over number fields. -/
def NumberFieldUnitaryEmbeddingReductionStatement : Prop :=
  NumberFieldLandherrStatement.{u} → NumberFieldLocalGlobalEmbeddingStatement.{u} →
    MaximalSubfieldConjugacyStatement.{u} → NumberFieldUnitaryEmbeddingClassStatement.{u} →
      NumberFieldUnitaryEmbeddingStatement.{u}

namespace UnitaryEmbeddingReduction

section Abstract

variable {R A L : Type*} [CommRing R] [Ring A] [Algebra R A] [CommRing L] [Algebra R L]
  (τ : FirstKindInvolution R A) (σ : FirstKindInvolution R L)

/-- The image of a unit under an involution, as a unit. -/
def involutionUnit (u : Aˣ) : Aˣ where
  val := τ u
  inv := τ ↑u⁻¹
  val_inv := by rw [← τ.map_mul, u.inv_mul, τ.map_one]
  inv_val := by rw [← τ.map_mul, u.mul_inv, τ.map_one]

@[simp] theorem involutionUnit_val (u : Aˣ) : (involutionUnit τ u : A) = τ u := rfl

@[simp] theorem involutionUnit_inv (u : Aˣ) : ((involutionUnit τ u)⁻¹ : Aˣ) = τ (↑u⁻¹ : A) :=
  rfl

theorem involution_inv_of_fixed (t : Aˣ) (ht : τ (t : A) = t) : τ (↑t⁻¹ : A) = ↑t⁻¹ := by
  have h := involutionUnit_inv τ t
  have h' : involutionUnit τ t = t := Units.ext ht
  rw [h'] at h
  exact h.symm

variable (f : L →ₐ[R] A)

/-- **Local twist class.** If `τ (f y) = t f(σ y) t⁻¹` with `τ t = t`, the image of `f` is
self-centralizing, and the conjugate `u f(·) u⁻¹` intertwines `σ` and `τ`, then
`t f(a) = h τ(h)` for a `σ`-fixed unit `a` of `L` and a unit `h` of `A`. -/
theorem exists_class_of_conjugate (hf : Function.Injective f) (t : Aˣ) (ht : τ (t : A) = t)
    (htw : ∀ y, τ (f y) = t * f (σ y) * ↑t⁻¹)
    (hcent : ∀ x : A, (∀ y, x * f y = f y * x) → ∃ y, f y = x)
    (u : Aˣ) (hu : ∀ y, (u : A) * f (σ y) * ↑u⁻¹ = τ ((u : A) * f y * ↑u⁻¹)) :
    ∃ a : Lˣ, σ (a : L) = a ∧ ∃ h : Aˣ, (t : A) * f a = h * τ h := by
  set V : Aˣ := involutionUnit τ u with hVdef
  have hV1 : τ (u : A) = V := rfl
  have hV2 : τ (↑u⁻¹ : A) = ↑V⁻¹ := rfl
  have hV3 : τ (V : A) = u := τ.apply_apply _
  set m : Aˣ := t⁻¹ * V * u with hm
  -- `m` commutes with the image of `f`
  have hcomm : ∀ z, (m : A) * f z = f z * m := by
    intro z
    have h1 := hu (σ z)
    rw [σ.apply_apply, τ.map_mul, τ.map_mul, htw (σ z), σ.apply_apply, hV1, hV2] at h1
    have h2 := congrArg (fun X => (↑t⁻¹ : A) * (V : A) * X * (u : A)) h1
    simp only [mul_assoc, Units.mul_inv_cancel_left, Units.inv_mul_cancel_left, Units.inv_mul,
      mul_one] at h2
    simp only [hm, Units.val_mul, mul_assoc]
    exact h2
  have hcomm' : ∀ z, (↑m⁻¹ : A) * f z = f z * ↑m⁻¹ := by
    intro z
    have h2 := congrArg (fun X => (↑m⁻¹ : A) * X * (↑m⁻¹ : A)) (hcomm z)
    simp only [mul_assoc, Units.inv_mul_cancel_left, Units.mul_inv,
      mul_one] at h2
    exact h2.symm
  obtain ⟨β, hβ⟩ := hcent m hcomm
  obtain ⟨β', hβ'⟩ := hcent (↑m⁻¹ : A) hcomm'
  have hββ' : β * β' = 1 := by
    apply hf
    rw [map_mul, hβ, hβ', Units.mul_inv, map_one]
  let b : Lˣ := ⟨β, β', hββ', by rw [mul_comm]; exact hββ'⟩
  refine ⟨b, ?_, V, ?_⟩
  · show σ β = β
    apply hf
    have h3 := htw β
    rw [hβ] at h3
    have hτm : τ (m : A) = (V : A) * u * ↑t⁻¹ := by
      simp only [hm, Units.val_mul, τ.map_mul, involution_inv_of_fixed τ t ht, hV1, hV3,
        mul_assoc]
    rw [hτm] at h3
    have h4 := congrArg (fun X => (↑t⁻¹ : A) * X * (t : A)) h3
    simp only [mul_assoc, Units.inv_mul_cancel_left, Units.inv_mul, mul_one] at h4
    rw [hβ, hm]
    simp only [Units.val_mul, mul_assoc]
    exact h4.symm
  · show (t : A) * f β = V * τ (V : A)
    rw [hβ, hm, hV3]
    simp only [Units.val_mul, mul_assoc, Units.mul_inv_cancel_left]

/-- **Twisted embeddings.** If `τ (f y) = t f(σ y) t⁻¹` and `t f(a) = x τ(x)` for a unit `a`
of `L` and a unit `x` of `A`, then conjugation of `f` by `τ(x)` intertwines `σ` and `τ`. -/
theorem conjugate_intertwines (t : Aˣ) (htw : ∀ y, τ (f y) = t * f (σ y) * ↑t⁻¹)
    (a : Lˣ) (x : Aˣ) (hx : (t : A) * f a = x * τ x) (y : L) :
    τ (τ (x : A) * f y * ↑(involutionUnit τ x)⁻¹) =
      τ (x : A) * f (σ y) * ↑(involutionUnit τ x)⁻¹ := by
  set W : Aˣ := involutionUnit τ x with hWdef
  have hW1 : τ (x : A) = W := rfl
  have hW2 : τ (W : A) = x := τ.apply_apply _
  have hW3 : τ (↑W⁻¹ : A) = ↑x⁻¹ := τ.apply_apply _
  set fa : Aˣ := Units.map f.toMonoidHom a with hfa
  have hfa1 : (fa : A) = f a := rfl
  have hfa2 : (↑fa⁻¹ : A) = f ↑a⁻¹ := rfl
  have hxu : t * fa = x * W := Units.ext (by rw [Units.val_mul, Units.val_mul, hfa1, hx, hW1])
  have hu1 : x⁻¹ * t = W * fa⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq, mul_assoc, hxu, ← mul_assoc, inv_mul_cancel, one_mul]
  have hu2 : t⁻¹ * x = fa * W⁻¹ := by
    have := congrArg Inv.inv hu1
    simpa [mul_inv_rev] using this
  have hcomm : (↑fa⁻¹ : A) * f (σ y) * fa = f (σ y) := by
    rw [hfa1, hfa2, ← map_mul, ← map_mul, mul_comm (↑a⁻¹ : L), mul_assoc, Units.inv_mul,
      mul_one]
  rw [hW1, τ.map_mul, τ.map_mul, hW2, hW3, htw y]
  calc (↑x⁻¹ : A) * (↑t * f (σ y) * ↑t⁻¹ * ↑x)
      = ↑(x⁻¹ * t) * f (σ y) * ↑(t⁻¹ * x) := by
        simp only [Units.val_mul, mul_assoc]
    _ = ↑W * (↑fa⁻¹ * f (σ y) * ↑fa) * ↑W⁻¹ := by
        rw [hu1, hu2]; simp only [Units.val_mul, mul_assoc]
    _ = ↑W * f (σ y) * ↑W⁻¹ := by rw [hcomm]

/-- The conjugate `p ↦ w f(p) w⁻¹` of an algebra homomorphism by a unit. -/
def conjugateHom (w : Aˣ) (f : L →ₐ[R] A) : L →ₐ[R] A where
  toFun p := w * f p * ↑w⁻¹
  map_one' := by simp
  map_mul' p q := by
    simp only [map_mul, mul_assoc, Units.inv_mul_cancel_left]
  map_zero' := by simp
  map_add' p q := by simp [mul_add, add_mul]
  commutes' r := by
    simp only [AlgHom.commutes, Algebra.commutes, mul_assoc, Units.mul_inv_cancel_left]

@[simp] theorem conjugateHom_apply (w : Aˣ) (p : L) :
    conjugateHom w f p = w * f p * ↑w⁻¹ := rfl

end Abstract

section Field

variable {R A L : Type*} [CommRing R] [Ring A] [Algebra R A] [Field L] [Algebra R L]
  (τ : FirstKindInvolution R A) (σ : FirstKindInvolution R L) (f : L →ₐ[R] A)

/-- **Symmetric twisting element** (Hilbert's Theorem 90 for `σ`). If `σ` is nontrivial,
`τ (f (σ y)) = g f(y) g⁻¹` for a unit `g`, and the image of `f` is self-centralizing, then
there is a unit `t` with `τ t = t` and `τ (f y) = t f(σ y) t⁻¹`. -/
theorem exists_symmetric_twist (hf : Function.Injective f) (θ : L) (hθ : σ θ ≠ θ)
    (g : Aˣ) (hg : ∀ y, τ (f (σ y)) = g * f y * ↑g⁻¹)
    (hcent : ∀ x : A, (∀ y, x * f y = f y * x) → ∃ y, f y = x) :
    ∃ t : Aˣ, τ (t : A) = t ∧ ∀ y, τ (f y) = t * f (σ y) * ↑t⁻¹ := by
  set G : Aˣ := involutionUnit τ g with hGdef
  have hG1 : τ (g : A) = G := rfl
  have hG2 : τ (↑g⁻¹ : A) = ↑G⁻¹ := rfl
  have hG3 : τ (G : A) = g := τ.apply_apply _
  have hg' : ∀ y, τ (f y) = g * f (σ y) * ↑g⁻¹ := by
    intro y
    have := hg (σ y)
    rwa [σ.apply_apply] at this
  set c : Aˣ := g⁻¹ * G with hc
  have hcomm : ∀ z, (c : A) * f z = f z * c := by
    intro w
    have h1 := congrArg τ (hg (σ w))
    rw [τ.apply_apply, τ.map_mul, τ.map_mul, hg' (σ w), hG1, hG2, σ.apply_apply] at h1
    have h2 := congrArg (fun X => (↑g⁻¹ : A) * (G : A) * X) h1
    simp only [mul_assoc, Units.mul_inv_cancel_left, Units.inv_mul_cancel_left] at h2
    simp only [hc, Units.val_mul, mul_assoc]
    exact h2
  obtain ⟨γ, hγ⟩ := hcent c hcomm
  have hσγ : f (σ γ) = ↑G⁻¹ * g := by
    have h1 := hg' γ
    rw [hγ, hc, Units.val_mul, τ.map_mul, hG3, hG2] at h1
    have h2 := congrArg (fun X => (↑g⁻¹ : A) * X * (g : A)) h1
    simp only [mul_assoc, Units.inv_mul_cancel_left, Units.inv_mul, mul_one] at h2
    exact h2.symm
  have hγσγ : γ * σ γ = 1 := by
    apply hf
    rw [map_mul, hγ, hσγ, map_one, hc, Units.val_mul, mul_assoc, Units.mul_inv_cancel_left,
      Units.inv_mul]
  -- Hilbert's Theorem 90
  obtain ⟨μ, hμ0, hμ⟩ : ∃ μ : L, μ ≠ 0 ∧ γ * σ μ = μ := by
    by_cases h : 1 + γ = 0
    · refine ⟨θ + γ * σ θ, ?_, ?_⟩
      · have hγ1 : γ = -1 := by linear_combination h
        rw [hγ1, neg_one_mul, ← sub_eq_add_neg, sub_ne_zero]
        exact hθ.symm
      · rw [σ.map_add, σ.map_mul, σ.apply_apply]
        linear_combination θ * hγσγ
    · refine ⟨1 + γ, h, ?_⟩
      rw [σ.map_add, σ.map_one]
      linear_combination hγσγ
  set fm : Aˣ := Units.map f.toMonoidHom (Units.mk0 μ hμ0) with hfm
  have hfm1 : (fm : A) = f μ := rfl
  have hfm2 : (↑fm⁻¹ : A) = f μ⁻¹ := rfl
  refine ⟨g * fm, ?_, ?_⟩
  · rw [Units.val_mul, τ.map_mul, hG1, hfm1, hg' μ]
    have h3 : f (σ μ) * f γ = f μ := by rw [← map_mul, mul_comm, hμ]
    calc (g : A) * f (σ μ) * ↑g⁻¹ * ↑G = g * (f (σ μ) * c) := by
          simp only [hc, Units.val_mul, mul_assoc]
      _ = g * f μ := by rw [← hγ, h3]
  · intro y
    rw [hg' y]
    have hcm : (fm : A) * f (σ y) * ↑fm⁻¹ = f (σ y) := by
      rw [hfm1, hfm2, ← map_mul, ← map_mul, mul_comm μ, mul_assoc, mul_inv_cancel₀ hμ0,
        mul_one]
    calc (g : A) * f (σ y) * ↑g⁻¹ = g * (fm * f (σ y) * ↑fm⁻¹) * ↑g⁻¹ := by rw [hcm]
      _ = ↑(g * fm) * f (σ y) * ↑(g * fm)⁻¹ := by
        simp only [Units.val_mul, mul_inv_rev, mul_assoc]

end Field

section Tensor

variable {F E B P : Type u} [Field F] [Field E] [Algebra F E]
  [Ring B] [Algebra E B] [Algebra F B] [IsScalarTower F E B]
  [Field P] [Algebra E P] [Algebra F P] [IsScalarTower F E P]

variable (F) in
/-- The scalar extension `id_K ⊗ f : K ⊗[F] P → K ⊗[F] B` of an `E`-algebra homomorphism. -/
abbrev extend (K : Type u) [CommRing K] [Algebra F K] (f : P →ₐ[E] B) :
    K ⊗[F] P →ₐ[K] K ⊗[F] B :=
  Algebra.TensorProduct.map (AlgHom.id K K) (f.restrictScalars F)

theorem extend_tmul (K : Type u) [CommRing K] [Algebra F K] (f : P →ₐ[E] B) (r : K) (p : P) :
    extend F K f (r ⊗ₜ[F] p) = r ⊗ₜ[F] f p := rfl

/-- Scalar extension along a field extension preserves injectivity. -/
theorem extend_injective (K : Type u) [Field K] [Algebra F K] (f : P →ₐ[E] B)
    (hf : Function.Injective f) : Function.Injective (extend F K f) := by
  have h : ⇑(extend F K f) = ⇑(LinearMap.lTensor K (f.restrictScalars F).toLinearMap) := by
    funext y
    induction y using TensorProduct.inductionOn with
    | tmul r p => rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [h]
  exact Module.Flat.lTensor_preserves_injective_linearMap _ hf

variable (F) in
/-- The unit `1 ⊗ t` of `K ⊗[F] B`. -/
def tensorUnit (K : Type u) [CommRing K] [Algebra F K] (t : Bˣ) : (K ⊗[F] B)ˣ :=
  Units.map (Algebra.TensorProduct.includeRight : B →ₐ[F] K ⊗[F] B).toMonoidHom t

omit [Field E] [Algebra E B] [IsScalarTower F E B] in
@[simp] theorem tensorUnit_val (K : Type u) [CommRing K] [Algebra F K] (t : Bˣ) :
    (tensorUnit F K t : K ⊗[F] B) = (1 : K) ⊗ₜ[F] (t : B) := rfl

omit [Field E] [Algebra E B] [IsScalarTower F E B] in
@[simp] theorem tensorUnit_inv (K : Type u) [CommRing K] [Algebra F K] (t : Bˣ) :
    (↑(tensorUnit F K t)⁻¹ : K ⊗[F] B) = (1 : K) ⊗ₜ[F] (↑t⁻¹ : B) := rfl

/-- The twisting identity `τ (f p) = t f(σ p) t⁻¹` survives scalar extension. -/
theorem extend_twist (K : Type u) [CommRing K] [Algebra F K] (τ : FirstKindInvolution F B)
    (σ : FirstKindInvolution F P) (f : P →ₐ[E] B) (t : Bˣ)
    (htw : ∀ p, τ (f p) = t * f (σ p) * ↑t⁻¹) (y : K ⊗[F] P) :
    τ.baseChange K (extend F K f y) =
      tensorUnit F K t * extend F K f (σ.baseChange K y) * ↑(tensorUnit F K t)⁻¹ := by
  induction y using TensorProduct.inductionOn with
  | tmul r p =>
    rw [extend_tmul, FirstKindInvolution.baseChange_tmul, FirstKindInvolution.baseChange_tmul,
      extend_tmul, tensorUnit_val, tensorUnit_inv, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, htw p]
  | add x y hx hy =>
    rw [map_add, FirstKindInvolution.map_add, hx, hy, FirstKindInvolution.map_add, map_add,
      mul_add, add_mul]

/-- The global case of the conjugacy statement, transported along `F ⊗[F] X ≃ X`. -/
theorem global_conjugacy (hConj : MaximalSubfieldConjugacyStatement.{u})
    [FiniteDimensional F E] [Algebra.IsSeparable F E] [FiniteDimensional E B]
    [Algebra.IsCentral E B] [IsSimpleRing B] [FiniteDimensional E P] [Algebra.IsSeparable E P]
    (hdim : Module.finrank E B = Module.finrank E P ^ 2) (f g : P →ₐ[E] B)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    (∃ u : Bˣ, ∀ p, g p = u * f p * ↑u⁻¹) ∧
      ∀ x : B, (∀ p, x * f p = f p * x) → ∃ p, f p = x := by
  have key : ∀ (h : P →ₐ[E] B) (y : F ⊗[F] P),
      extend F F h y = (Algebra.TensorProduct.lid F B).symm (h (Algebra.TensorProduct.lid F P y)) := by
    intro h y
    apply (Algebra.TensorProduct.lid F B).injective
    rw [AlgEquiv.apply_symm_apply]
    induction y using TensorProduct.inductionOn with
    | tmul r p =>
      rw [extend_tmul, Algebra.TensorProduct.lid_tmul, Algebra.TensorProduct.lid_tmul]
      exact (map_smul (h.restrictScalars F) r p).symm
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  have hinj : ∀ h : P →ₐ[E] B, Function.Injective h → Function.Injective (extend F F h) := by
    intro h hh a b hab
    rw [key, key] at hab
    exact (Algebra.TensorProduct.lid F P).injective (hh ((Algebra.TensorProduct.lid F B).symm.injective hab))
  have hE : ∀ (h : P →ₐ[E] B) (e : E),
      extend F F h ((1 : F) ⊗ₜ[F] algebraMap E P e) = (1 : F) ⊗ₜ[F] algebraMap E B e := by
    intro h e
    rw [extend_tmul, AlgHom.commutes]
  obtain ⟨⟨u, hu⟩, hc⟩ :=
    hConj F E B P F hdim (extend F F f) (extend F F g) (hinj f hf) (hinj g hg) (hE f) (hE g)
  refine ⟨⟨Units.map (Algebra.TensorProduct.lid F B).toAlgHom.toMonoidHom u, fun p => ?_⟩, ?_⟩
  · have h1 := congrArg (Algebra.TensorProduct.lid F B) (hu ((1 : F) ⊗ₜ[F] p))
    rw [key, key, map_mul, map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply,
      Algebra.TensorProduct.lid_tmul, one_smul] at h1
    exact h1
  · intro x hx
    have hx' : ∀ y, (Algebra.TensorProduct.lid F B).symm x * extend F F f y =
        extend F F f y * (Algebra.TensorProduct.lid F B).symm x := by
      intro y
      rw [key, ← map_mul, ← map_mul, hx]
    obtain ⟨y, hy⟩ := (AlgHom.mem_range _).1 (hc _ hx')
    rw [key] at hy
    exact ⟨Algebra.TensorProduct.lid F P y, (Algebra.TensorProduct.lid F B).symm.injective hy⟩

end Tensor

/-- Every completion of a number field is a field. -/
theorem placeCompletion_isField (F : Type u) [Field F] [NumberField F] (v : Global.Place F) :
    IsField (Global.placeCompletion F v) := by
  rcases v with w | v
  · exact Field.toIsField w.Completion
  · exact Field.toIsField (Global.FiniteCompletion F v)

end UnitaryEmbeddingReduction

open UnitaryEmbeddingReduction in
/-- Proof of `NumberFieldUnitaryEmbeddingReductionStatement`. -/
theorem numberFieldUnitaryEmbeddingReduction :
    NumberFieldUnitaryEmbeddingReductionStatement.{u} := by
  intro hLand hLG hConj hClass F E B P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ τ σ hτE hσE hdim hloc
  have : FiniteDimensional F E :=
    .of_finrank_pos (by rw [Algebra.IsQuadraticExtension.finrank_eq_two F E]; decide)
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
  have : Algebra.IsSeparable E P := Algebra.IsAlgebraic.isSeparable_of_perfectField
  -- a global embedding of `P` into `B`
  obtain ⟨ε⟩ := hLG F E B P hdim fun v => by
    obtain ⟨φ, h1, h2, -⟩ := hloc v
    exact ⟨φ, h1, h2⟩
  have hε : Function.Injective ε := ε.toRingHom.injective
  -- the embedding `τ ∘ ε ∘ σ`
  let ε' : P →ₐ[E] B :=
    { toFun := fun p => τ (ε (σ p))
      map_one' := by simp
      map_mul' := fun p q => by
        simp only [FirstKindInvolution.map_mul, map_mul]
      map_zero' := by simp
      map_add' := fun p q => by simp
      commutes' := fun e => by
        simp only [hσE, AlgHom.commutes, hτE, conjugation_involutive F E e] }
  have hε' : Function.Injective ε' := ε'.toRingHom.injective
  obtain ⟨⟨g₀, hg₀⟩, hcent⟩ := global_conjugacy (F := F) hConj hdim ε ε' hε hε'
  -- `σ` is nontrivial
  obtain ⟨δ, hδ⟩ : ∃ δ : E, conjugation F E δ ≠ δ := by
    by_contra h
    push Not at h
    exact conjugation_ne_one F E (AlgEquiv.ext h)
  have hθ : σ (algebraMap E P δ) ≠ algebraMap E P δ := by
    rw [hσE]
    exact fun h => hδ ((algebraMap E P).injective h)
  -- a symmetric twisting unit
  obtain ⟨t, ht, htw⟩ := exists_symmetric_twist τ σ (ε.restrictScalars F) hε
    (algebraMap E P δ) hθ g₀ hg₀ hcent
  -- local twist classes
  have hlocal : ∀ v : Global.Place F,
      ∃ a : (Global.placeCompletion F v ⊗[F] P)ˣ,
        σ.baseChange (Global.placeCompletion F v) a = a ∧
        ∃ h : (Global.placeCompletion F v ⊗[F] B)ˣ,
          (1 : Global.placeCompletion F v) ⊗ₜ[F] (t : B) *
              Algebra.TensorProduct.map (AlgHom.id (Global.placeCompletion F v)
                (Global.placeCompletion F v)) (ε.restrictScalars F) a =
            h * τ.baseChange (Global.placeCompletion F v) h := by
    intro v
    let : Field (Global.placeCompletion F v) := (placeCompletion_isField F v).toField
    obtain ⟨φ, hφinj, hφE, hφσ⟩ := hloc v
    have hεv := extend_injective (F := F) (Global.placeCompletion F v) ε hε
    obtain ⟨⟨u, hu⟩, hc⟩ := hConj F E B P (Global.placeCompletion F v) hdim
      (extend F (Global.placeCompletion F v) ε) φ hεv hφinj
      (fun e => by rw [extend_tmul, AlgHom.commutes]) hφE
    have ht' : τ.baseChange (Global.placeCompletion F v)
        (tensorUnit F (Global.placeCompletion F v) t :
          Global.placeCompletion F v ⊗[F] B) = tensorUnit F (Global.placeCompletion F v) t := by
      rw [tensorUnit_val, FirstKindInvolution.baseChange_tmul, ht]
    obtain ⟨a, ha, h, hh⟩ := exists_class_of_conjugate (τ.baseChange (Global.placeCompletion F v))
      (σ.baseChange (Global.placeCompletion F v)) (extend F (Global.placeCompletion F v) ε) hεv
      (tensorUnit F (Global.placeCompletion F v) t) ht'
      (extend_twist (F := F) (Global.placeCompletion F v) τ σ ε t htw)
      (fun x hx => (AlgHom.mem_range _).1 (hc x hx)) u
      (fun y => by rw [← hu, ← hu]; exact hφσ y)
    exact ⟨a, ha, h, hh⟩
  -- a global twist class
  obtain ⟨a, ha0, haσ, hloc₂⟩ := hClass F E B P τ σ hτE hσE hdim ε t ht htw hlocal
  set a' : Pˣ := Units.mk0 a ha0
  set y : Bˣ := t * Units.map ε.toMonoidHom a' with hy
  have hyτ : τ (y : B) = y := by
    rw [hy, Units.val_mul, FirstKindInvolution.map_mul, ht]
    change τ (ε a) * t = t * ε a
    have htw' : ∀ p, τ (ε p) = t * ε (σ p) * ↑t⁻¹ := htw
    rw [htw' a, haσ, mul_assoc, Units.inv_mul, mul_one]
  -- Landherr's theorem
  obtain ⟨x, hx⟩ := hLand F E B τ hτE y hyτ (fun v => hloc₂ v)
  refine ⟨conjugateHom (involutionUnit τ x) ε, fun p => ?_⟩
  exact (conjugate_intertwines τ σ (ε.restrictScalars F) t htw a' x hx p).symm

end Langlands.CentralSimple
