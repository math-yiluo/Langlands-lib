import Langlands.Geometry.FormalGroup.ModuleMorphism
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Localization.FractionRing

/-! # Rational formal homomorphisms and quasi-isogenies -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw

open TensorProduct

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable (F : Type w) [Field F] [Algebra O F]
variable {σ τ υ ω : Type} [Finite σ] [Finite τ] [Finite υ] [Finite ω]

/-- Rational Hom is the actual scalar extension of integral formal Hom.
The field is placed on the left to use the standard F-module structure. -/
abbrev RationalHom (M : ModuleLaw O R σ) (N : ModuleLaw O R τ) :=
  F ⊗[O] Hom M N

namespace RationalHom

variable {F}
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable {P : ModuleLaw O R υ} {Q : ModuleLaw O R ω}

/-- The canonical equivalence with the tensor order used by Drinfeld. -/
def sourceTensorEquiv : RationalHom F M N ≃ₗ[O] (Hom M N) ⊗[O] F :=
  TensorProduct.comm O F (Hom M N)

/-- Send an integral formal homomorphism to its rationalization. -/
def ofHom : Hom M N →ₗ[O] RationalHom F M N :=
  TensorProduct.mk O F (Hom M N) 1

@[simp]
theorem ofHom_apply (f : Hom M N) : (ofHom (F := F)) f = 1 ⊗ₜ[O] f := rfl

/-- Extend composition and multiplication of field scalars by tensor bilinearity. -/
def compLinearO : RationalHom F N P →ₗ[O] RationalHom F M N →ₗ[O] RationalHom F M P :=
  TensorProduct.map₂ (LinearMap.mul O F) Hom.compLinear

/-- Composition of rational formal homomorphisms. -/
def comp (g : RationalHom F N P) (f : RationalHom F M N) : RationalHom F M P :=
  compLinearO g f

@[simp]
theorem comp_tmul (a b : F) (g : Hom N P) (f : Hom M N) :
    comp (a ⊗ₜ[O] g) (b ⊗ₜ[O] f) = (a * b) ⊗ₜ[O] g.comp f := rfl

@[simp]
theorem comp_add (g : RationalHom F N P) (f₁ f₂ : RationalHom F M N) :
    comp g (f₁ + f₂) = comp g f₁ + comp g f₂ :=
  (compLinearO g).map_add f₁ f₂

@[simp]
theorem add_comp (g₁ g₂ : RationalHom F N P) (f : RationalHom F M N) :
    comp (g₁ + g₂) f = comp g₁ f + comp g₂ f :=
  compLinearO.map_add₂ g₁ g₂ f

@[simp]
theorem comp_zero (g : RationalHom F N P) :
    comp g (0 : RationalHom F M N) = 0 := (compLinearO g).map_zero

@[simp]
theorem zero_comp (f : RationalHom F M N) :
    comp (0 : RationalHom F N P) f = 0 := compLinearO.map_zero₂ f

/-- The rational identity is the tensor of one and the integral identity. -/
def id (M : ModuleLaw O R σ) : RationalHom F M M :=
  ofHom (Hom.id M)

@[simp]
theorem comp_id (f : RationalHom F M N) : comp f (id M) = f := by
  induction f using TensorProduct.inductionOn with
  | tmul a f => simp [id, ofHom]
  | add f g hf hg => simp only [add_comp, hf, hg]

@[simp]
theorem id_comp (f : RationalHom F M N) : comp (id N) f = f := by
  induction f using TensorProduct.inductionOn with
  | tmul a f => simp [id, ofHom]
  | add f g hf hg => simp only [comp_add, hf, hg]

theorem comp_assoc (h : RationalHom F P Q) (g : RationalHom F N P)
    (f : RationalHom F M N) : comp (comp h g) f = comp h (comp g f) := by
  induction h using TensorProduct.inductionOn with
  | add h₁ h₂ hh₁ hh₂ => simp only [add_comp, hh₁, hh₂]
  | tmul a h =>
    induction g using TensorProduct.inductionOn with
    | add g₁ g₂ hg₁ hg₂ => simp only [comp_add, add_comp, hg₁, hg₂]
    | tmul b g =>
      induction f using TensorProduct.inductionOn with
      | add f₁ f₂ hf₁ hf₂ => simp only [comp_add, hf₁, hf₂]
      | tmul c f => simp only [comp_tmul, mul_assoc, Hom.comp_assoc]

@[simp]
theorem comp_smul (g : RationalHom F N P) (a : F) (f : RationalHom F M N) :
    comp g (a • f) = a • comp g f := by
  induction g using TensorProduct.inductionOn with
  | add g₁ g₂ hg₁ hg₂ => simp only [add_comp, hg₁, hg₂, smul_add]
  | tmul b g =>
    induction f using TensorProduct.inductionOn with
    | add f₁ f₂ hf₁ hf₂ => simp only [smul_add, comp_add, hf₁, hf₂]
    | tmul c f => simp only [smul_tmul', smul_eq_mul, comp_tmul, mul_left_comm]

@[simp]
theorem smul_comp (a : F) (g : RationalHom F N P) (f : RationalHom F M N) :
    comp (a • g) f = a • comp g f := by
  induction g using TensorProduct.inductionOn with
  | add g₁ g₂ hg₁ hg₂ => simp only [smul_add, add_comp, hg₁, hg₂]
  | tmul b g =>
    induction f using TensorProduct.inductionOn with
    | add f₁ f₂ hf₁ hf₂ => simp only [comp_add, hf₁, hf₂, smul_add]
    | tmul c f => simp only [smul_tmul', smul_eq_mul, comp_tmul, mul_assoc]

/-- Composition is bilinear over the field of rational scalars. -/
def compLinear : RationalHom F N P →ₗ[F] RationalHom F M N →ₗ[F] RationalHom F M P where
  toFun g := {
    toFun := comp g
    map_add' := comp_add g
    map_smul' := comp_smul g }
  map_add' g₁ g₂ := by
    apply LinearMap.ext
    intro f
    exact add_comp g₁ g₂ f
  map_smul' a g := by
    apply LinearMap.ext
    intro f
    exact smul_comp a g f

@[simp]
theorem ofHom_id : ofHom (F := F) (Hom.id M) = id M := rfl

@[simp]
theorem ofHom_comp (g : Hom N P) (f : Hom M N) :
    ofHom (F := F) (g.comp f) = comp (ofHom g) (ofHom f) := by
  simp only [ofHom_apply, comp_tmul, one_mul]

/-- Changing the coefficient O-algebra on the actual tensor Hom. -/
def map {S : Type*} [CommRing S] [Algebra O S] (φ : R →ₐ[O] S) :
    RationalHom F M N →ₗ[F] RationalHom F (M.map φ) (N.map φ) :=
  (Hom.mapLinear φ).baseChange F

end RationalHom

/-- A quasi-isogeny is a rational homomorphism together with its two-sided inverse. -/
structure QuasiIsogeny [IsDomain O] [IsFractionRing O F] (M : ModuleLaw O R σ) (N : ModuleLaw O R τ) where
  hom : RationalHom F M N
  inv : RationalHom F N M
  inv_hom : RationalHom.comp inv hom = RationalHom.id M
  hom_inv : RationalHom.comp hom inv = RationalHom.id N

namespace QuasiIsogeny

variable [IsDomain O] [IsFractionRing O F]
variable {F}
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {P : ModuleLaw O R υ}

/-- Identity quasi-isogeny. -/
def refl (M : ModuleLaw O R σ) : QuasiIsogeny F M M where
  hom := RationalHom.id M
  inv := RationalHom.id M
  inv_hom := RationalHom.id_comp _
  hom_inv := RationalHom.id_comp _

/-- Inverse quasi-isogeny. -/
def symm (f : QuasiIsogeny F M N) : QuasiIsogeny F N M where
  hom := f.inv
  inv := f.hom
  inv_hom := f.hom_inv
  hom_inv := f.inv_hom

/-- Compose invertible rational homomorphisms. -/
def trans (f : QuasiIsogeny F M N) (g : QuasiIsogeny F N P) : QuasiIsogeny F M P where
  hom := RationalHom.comp g.hom f.hom
  inv := RationalHom.comp f.inv g.inv
  inv_hom := by
    rw [RationalHom.comp_assoc, ← RationalHom.comp_assoc g.inv, g.inv_hom,
      RationalHom.id_comp, f.inv_hom]
  hom_inv := by
    rw [RationalHom.comp_assoc, ← RationalHom.comp_assoc f.hom, f.hom_inv,
      RationalHom.id_comp, g.hom_inv]

/-- An integral formal O-module isomorphism gives a quasi-isogeny. -/
def ofIso (f : Iso M N) : QuasiIsogeny F M N where
  hom := RationalHom.ofHom f.hom
  inv := RationalHom.ofHom f.inv
  inv_hom := by
    rw [← RationalHom.ofHom_comp, f.inv_hom, RationalHom.ofHom_id]
  hom_inv := by
    rw [← RationalHom.ofHom_comp, f.hom_inv, RationalHom.ofHom_id]

/-- The inverse rational homomorphism is uniquely determined. -/
theorem inv_unique (f : QuasiIsogeny F M N) (g : RationalHom F N M)
    (h : RationalHom.comp g f.hom = RationalHom.id M) : g = f.inv := by
  calc
    g = RationalHom.comp g (RationalHom.id N) := (RationalHom.comp_id g).symm
    _ = RationalHom.comp g (RationalHom.comp f.hom f.inv) := by rw [f.hom_inv]
    _ = RationalHom.comp (RationalHom.comp g f.hom) f.inv :=
      (RationalHom.comp_assoc _ _ _).symm
    _ = f.inv := by rw [h, RationalHom.id_comp]

end QuasiIsogeny

end Langlands.FormalGroup.ModuleLaw
