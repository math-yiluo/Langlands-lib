import Langlands.Shimura.Unitary.Similitude
import Langlands.Shimura.PEL.InvariantOrbits
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-! # B-linear similitudes and isomorphisms with a line-valued form -/

universe u v w z t

namespace Langlands.Shimura.PEL

variable {R : Type u} {B : Type v} {V : Type w} {W : Type z} {L : Type t}
variable [CommRing R] [Ring B]
variable [AddCommGroup V] [Module R V] [Module B V]
variable [AddCommGroup W] [Module R W] [Module B W]
variable [AddCommGroup L] [Module R L]

/-- Compatibility of a form with the specified algebra involution. -/
def FormRespectsInvolution [Algebra R B] (σ : AlgebraInvolution R B)
    (ψ : V →ₗ[R] V →ₗ[R] R) : Prop :=
  ∀ (b : B) (x y : V), ψ (b • x) y = ψ x (σ b • y)

/-- The actual subgroup of B-linear automorphisms and unit multipliers preserving a form. -/
def bilinearSimilitudes (B : Type v) [Ring B] [Module B V]
    (ψ : V →ₗ[R] V →ₗ[R] R) : Subgroup ((V ≃ₗ[B] V) × Rˣ) where
  carrier := {g | ∀ x y, ψ (g.1 x) (g.1 y) = (g.2 : R) * ψ x y}
  one_mem' := by intro x y; simp
  mul_mem' {g h} hg hh := by
    intro x y
    change ψ (g.1 (h.1 x)) (g.1 (h.1 y)) =
      ((g.2 : R) * (h.2 : R)) * ψ x y
    rw [hg, hh, mul_assoc]
  inv_mem' {g} hg := by
    intro x y
    have h := hg (g.1.symm x) (g.1.symm y)
    simp only [LinearEquiv.apply_symm_apply] at h
    change ψ (g.1.symm x) (g.1.symm y) = (↑g.2⁻¹ : R) * ψ x y
    rw [h, ← mul_assoc, Units.inv_mul, one_mul]

namespace bilinearSimilitudes

variable (ψ : V →ₗ[R] V →ₗ[R] R)

/-- Forget the multiplier, retaining the actual B-linear automorphism. -/
def underlying : bilinearSimilitudes B ψ →* (V ≃ₗ[B] V) :=
  (MonoidHom.fst _ _).comp (bilinearSimilitudes B ψ).subtype

/-- The multiplier character. -/
def multiplier : bilinearSimilitudes B ψ →* Rˣ :=
  (MonoidHom.snd _ _).comp (bilinearSimilitudes B ψ).subtype

@[simp] theorem form_apply (g : bilinearSimilitudes B ψ) (x y : V) :
    ψ (underlying ψ g x) (underlying ψ g y) =
      (multiplier ψ g : R) * ψ x y := g.property x y

/-- A form taking the value one determines its similitude multiplier uniquely. -/
theorem underlying_injective (hψ : ∃ x y, ψ x y = 1) :
    Function.Injective (underlying (B := B) ψ) := by
  rintro g h heq
  apply Subtype.ext
  apply Prod.ext heq
  apply Units.ext
  obtain ⟨x, y, hxy⟩ := hψ
  have hg := form_apply ψ g x y
  have hh := form_apply ψ h x y
  rw [heq] at hg
  rw [hh, hxy, mul_one, mul_one] at hg
  exact hg.symm

end bilinearSimilitudes

/-- Automorphisms of a module and its form-value module that preserve the form together. -/
def twistedSimilitudes (B : Type v) [Ring B] [Module B W]
    (φ : W →ₗ[R] W →ₗ[R] L) : Subgroup ((W ≃ₗ[B] W) × (L ≃ₗ[R] L)) where
  carrier := {g | ∀ x y, φ (g.1 x) (g.1 y) = g.2 (φ x y)}
  one_mem' := by intro x y; rfl
  mul_mem' {g h} hg hh := by
    intro x y
    change φ (g.1 (h.1 x)) (g.1 (h.1 y)) = g.2 (h.2 (φ x y))
    rw [hg, hh]
  inv_mem' {g} hg := by
    intro x y
    have h := hg (g.1.symm x) (g.1.symm y)
    simp only [LinearEquiv.apply_symm_apply] at h
    change φ (g.1.symm x) (g.1.symm y) = g.2.symm (φ x y)
    rw [h, LinearEquiv.symm_apply_apply]

/-- Form compatibility retains the value module explicitly and quantifies over a
trivialization, without choosing one as part of the isomorphism. -/
def FormCompatible (ψ : V →ₗ[R] V →ₗ[R] R) (φ : W →ₗ[R] W →ₗ[R] L)
    (η : V ≃ₗ[B] W) : Prop :=
  ∃ t : R ≃ₗ[R] L, ∀ x y, φ (η x) (η y) = t (ψ x y)

/-- Every linear automorphism of the scalar module is multiplication by its value at one. -/
theorem scalarEquiv_apply (e : R ≃ₗ[R] R) (r : R) : e r = e 1 * r := by
  simpa [smul_eq_mul, mul_comm] using e.map_smul r 1

/-- The scalar unit attached to an automorphism of the rank-one scalar module. -/
def scalarEquivUnit (e : R ≃ₗ[R] R) : Rˣ where
  val := e 1
  inv := e.symm 1
  val_inv := (scalarEquiv_apply e _).symm.trans (e.apply_symm_apply 1)
  inv_val := (scalarEquiv_apply e.symm _).symm.trans (e.symm_apply_apply 1)

/-- Relative to any chosen trivialization, compatibility means preservation up to a unit.
The definition itself does not retain this choice. -/
theorem formCompatible_iff (ψ : V →ₗ[R] V →ₗ[R] R) (φ : W →ₗ[R] W →ₗ[R] L)
    (η : V ≃ₗ[B] W) (t₀ : R ≃ₗ[R] L) :
    FormCompatible ψ φ η ↔
      ∃ c : Rˣ, ∀ x y, φ (η x) (η y) = t₀ ((c : R) * ψ x y) := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨scalarEquivUnit (t.trans t₀.symm), ?_⟩
    intro x y
    rw [ht]
    apply t₀.symm.injective
    simpa [scalarEquivUnit] using scalarEquiv_apply (t.trans t₀.symm) (ψ x y)
  · rintro ⟨c, hc⟩
    exact ⟨(LinearEquiv.smulOfUnit c).trans t₀, hc⟩

/-- B-linear isomorphisms compatible with a scalar-valued and a line-valued form. -/
def FormIso (B : Type v) [Ring B] [Module B V] [Module B W]
    (ψ : V →ₗ[R] V →ₗ[R] R) (φ : W →ₗ[R] W →ₗ[R] L) :=
  {η : V ≃ₗ[B] W // FormCompatible ψ φ η}

namespace FormIso

variable {ψ : V →ₗ[R] V →ₗ[R] R} {φ : W →ₗ[R] W →ₗ[R] L}

/-- Right composition with a similitude. -/
def precomp (η : FormIso B ψ φ) (g : bilinearSimilitudes B ψ) : FormIso B ψ φ :=
  ⟨g.1.1.trans η.1, by
    obtain ⟨t, ht⟩ := η.2
    refine ⟨(LinearEquiv.smulOfUnit g.1.2).trans t, ?_⟩
    intro x y
    change φ (η.1 (g.1.1 x)) (η.1 (g.1.1 y)) = t ((g.1.2 : R) * ψ x y)
    rw [ht, g.2]⟩

@[simp] theorem precomp_apply (η : FormIso B ψ φ) (g : bilinearSimilitudes B ψ)
    (x : V) : (precomp η g).1 x = η.1 (g.1.1 x) := rfl

@[simp] theorem precomp_one (η : FormIso B ψ φ) : precomp η 1 = η := by
  apply Subtype.ext
  ext x
  rfl

theorem precomp_mul (η : FormIso B ψ φ) (g h : bilinearSimilitudes B ψ) :
    precomp (precomp η g) h = precomp η (g * h) := by
  apply Subtype.ext
  ext x
  rfl

/-- Left composition includes the action on the form-value module. -/
def postcomp (a : twistedSimilitudes B φ) (η : FormIso B ψ φ) : FormIso B ψ φ :=
  ⟨η.1.trans a.1.1, by
    obtain ⟨t, ht⟩ := η.2
    refine ⟨t.trans a.1.2, ?_⟩
    intro x y
    change φ (a.1.1 (η.1 x)) (a.1.1 (η.1 y)) = a.1.2 (t (ψ x y))
    rw [a.2, ht]⟩

@[simp] theorem postcomp_apply (a : twistedSimilitudes B φ) (η : FormIso B ψ φ)
    (x : V) : (postcomp a η).1 x = a.1.1 (η.1 x) := rfl

@[simp] theorem postcomp_one (η : FormIso B ψ φ) : postcomp 1 η = η := by
  apply Subtype.ext
  ext x
  rfl

theorem postcomp_mul (a b : twistedSimilitudes B φ) (η : FormIso B ψ φ) :
    postcomp (a * b) η = postcomp a (postcomp b η) := by
  apply Subtype.ext
  ext x
  rfl

theorem postcomp_precomp (a : twistedSimilitudes B φ) (η : FormIso B ψ φ)
    (g : bilinearSimilitudes B ψ) :
    postcomp a (precomp η g) = precomp (postcomp a η) g := by
  apply Subtype.ext
  ext x
  rfl

instance : MulAction (bilinearSimilitudes B ψ)ᵐᵒᵖ (FormIso B ψ φ) where
  smul g η := precomp η g.unop
  one_smul := precomp_one
  mul_smul g h η := (precomp_mul η h.unop g.unop).symm

instance : MulAction (twistedSimilitudes B φ) (FormIso B ψ φ) where
  smul := postcomp
  one_smul := postcomp_one
  mul_smul := postcomp_mul

instance : SMulCommClass (twistedSimilitudes B φ)
    (bilinearSimilitudes B ψ)ᵐᵒᵖ (FormIso B ψ φ) where
  smul_comm a g η := postcomp_precomp a η g.unop

/-- Every two compatible isomorphisms differ by a source similitude. -/
theorem exists_precomp_eq (η ξ : FormIso B ψ φ) :
    ∃ g : bilinearSimilitudes B ψ, precomp η g = ξ := by
  obtain ⟨t, ht⟩ := η.2
  obtain ⟨c, hc⟩ := (formCompatible_iff ψ φ ξ.1 t).mp ξ.2
  let g : bilinearSimilitudes B ψ := ⟨(ξ.1.trans η.1.symm, c), by
    intro x y
    apply t.injective
    rw [← ht]
    simpa using hc x y⟩
  refine ⟨g, ?_⟩
  apply Subtype.ext
  ext x
  exact η.1.apply_symm_apply (ξ.1 x)

/-- If the source form takes the value one, the right action is free. -/
theorem precomp_injective (hψ : ∃ x y, ψ x y = 1) (η : FormIso B ψ φ) :
    Function.Injective (precomp η) := by
  intro g h heq
  apply bilinearSimilitudes.underlying_injective ψ hψ
  ext x
  apply η.1.injective
  exact congrArg (fun ζ : FormIso B ψ φ => ζ.1 x) heq

end FormIso
end Langlands.Shimura.PEL
