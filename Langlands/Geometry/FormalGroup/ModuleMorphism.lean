import Langlands.Geometry.FormalGroup.FormalModule

/-! # O-linear formal homomorphisms -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {S : Type w} [CommRing S] [Algebra O S]
variable {σ τ υ ω κ : Type} [Finite σ] [Finite τ] [Finite υ] [Finite ω]

/-- A homomorphism of formal O-modules commutes with every formal scalar action. -/
@[ext]
structure Hom (M : ModuleLaw O R σ) (N : ModuleLaw O R τ) where
  toHom : CommLaw.Hom M.groupLaw N.groupLaw
  commutes : ∀ a : O, toHom.comp (M.action a) = (N.action a).comp toHom

namespace Hom

variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable {P : ModuleLaw O R υ} {Q : ModuleLaw O R ω}

/-- Evaluate an O-linear formal homomorphism on series points. -/
def onPoints (f : Hom M N) : M.Point κ →ₗ[O] N.Point κ where
  toFun := f.toHom.onPoints
  map_add' := f.toHom.onPoints.map_add
  map_smul' a x := by
    change M.groupLaw.Point κ at x
    have h := congrArg (fun h => h.onPoints x) (f.commutes a)
    change f.toHom.onPoints ((M.action a).onPoints x) =
      (N.action a).onPoints (f.toHom.onPoints x)
    simpa only [CommLaw.Hom.onPoints_comp] using h

@[simp]
theorem onPoints_apply (f : Hom M N) (x : M.Point κ) :
    f.onPoints x = f.toHom.onPoints x := rfl

/-- Pointwise O-linearity on all series points recovers formal scalar commutation. -/
def ofPointLinear (f : CommLaw.Hom M.groupLaw N.groupLaw)
    (h : ∀ (κ : Type) (a : O) (x : M.Point κ),
      f.onPoints ((M.action a).onPoints x) =
        (N.action a).onPoints (f.onPoints x)) : Hom M N where
  toHom := f
  commutes a := by
    apply CommLaw.Hom.ext_onPoints
    intro x
    simpa only [CommLaw.Hom.onPoints_comp] using h σ a x

/-- Evaluation at the generic series point detects O-linear formal homomorphisms. -/
theorem ext_onPoints {f g : Hom M N}
    (h : ∀ x : M.Point σ, f.onPoints x = g.onPoints x) : f = g := by
  apply Hom.ext
  exact CommLaw.Hom.ext_onPoints h

/-- Identity O-linear formal homomorphism. -/
def id (M : ModuleLaw O R σ) : Hom M M where
  toHom := CommLaw.Hom.id M.groupLaw
  commutes a := by simp

/-- Composition, with the map on the right applied first. -/
def comp (g : Hom N P) (f : Hom M N) : Hom M P where
  toHom := g.toHom.comp f.toHom
  commutes a := by
    rw [CommLaw.Hom.comp_assoc, f.commutes,
      ← CommLaw.Hom.comp_assoc, g.commutes, CommLaw.Hom.comp_assoc]

@[simp]
theorem id_toHom : (id M).toHom = CommLaw.Hom.id M.groupLaw := rfl

@[simp]
theorem comp_toHom (g : Hom N P) (f : Hom M N) :
    (g.comp f).toHom = g.toHom.comp f.toHom := rfl

@[simp]
theorem onPoints_id (x : M.Point κ) : (id M).onPoints x = x :=
  CommLaw.Hom.onPoints_id x

@[simp]
theorem onPoints_comp (g : Hom N P) (f : Hom M N) (x : M.Point κ) :
    (g.comp f).onPoints x = g.onPoints (f.onPoints x) :=
  CommLaw.Hom.onPoints_comp _ _ x

@[simp]
theorem comp_id (f : Hom M N) : f.comp (id M) = f := by
  apply Hom.ext
  exact CommLaw.Hom.comp_id _

@[simp]
theorem id_comp (f : Hom M N) : (id N).comp f = f := by
  apply Hom.ext
  exact CommLaw.Hom.id_comp _

theorem comp_assoc (h : Hom P Q) (g : Hom N P) (f : Hom M N) :
    (h.comp g).comp f = h.comp (g.comp f) := by
  apply Hom.ext
  exact CommLaw.Hom.comp_assoc _ _ _

instance : Zero (Hom M N) :=
  ⟨{ toHom := 0, commutes := by intro a; simp }⟩

instance : Add (Hom M N) :=
  ⟨fun f g => {
    toHom := f.toHom + g.toHom
    commutes := by
      intro a
      rw [CommLaw.Hom.add_comp, CommLaw.Hom.comp_add, f.commutes, g.commutes] }⟩

instance : Neg (Hom M N) :=
  ⟨fun f => ofPointLinear (-f.toHom) (by
    intro κ a x
    change M.groupLaw.Point κ at x
    simp only [CommLaw.Hom.onPoints_neg]
    change M.Point κ at x
    change -(f.onPoints (a • x)) = a • (-f.onPoints x)
    rw [_root_.map_smul, smul_neg])⟩

@[simp]
theorem zero_toHom : (0 : Hom M N).toHom = 0 := rfl

@[simp]
theorem add_toHom (f g : Hom M N) : (f + g).toHom = f.toHom + g.toHom := rfl

@[simp]
theorem neg_toHom (f : Hom M N) : (-f).toHom = -f.toHom := rfl

@[simp]
theorem onPoints_zero (x : M.Point κ) : (0 : Hom M N).onPoints x = 0 :=
  CommLaw.Hom.onPoints_zero x

@[simp]
theorem onPoints_add (f g : Hom M N) (x : M.Point κ) :
    (f + g).onPoints x = f.onPoints x + g.onPoints x :=
  CommLaw.Hom.onPoints_add _ _ x

@[simp]
theorem onPoints_neg (f : Hom M N) (x : M.Point κ) :
    (-f).onPoints x = -(f.onPoints x) :=
  CommLaw.Hom.onPoints_neg _ x

instance : AddCommGroup (Hom M N) where
  add_assoc f g h := ext_onPoints (by intro x; simp only [onPoints_add, _root_.add_assoc])
  zero_add f := ext_onPoints (by intro x; simp only [onPoints_add, onPoints_zero, _root_.zero_add])
  add_zero f := ext_onPoints (by intro x; simp only [onPoints_add, onPoints_zero, _root_.add_zero])
  neg_add_cancel f := ext_onPoints (by
    intro x
    simp only [onPoints_add, onPoints_neg, onPoints_zero, neg_add_cancel])
  add_comm f g := ext_onPoints (by intro x; simp only [onPoints_add, _root_.add_comm])
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- Multiply a formal homomorphism by postcomposing with target scalar action. -/
instance : SMul O (Hom M N) :=
  ⟨fun a f => ofPointLinear ((N.action a).comp f.toHom) (by
    intro κ b x
    change M.groupLaw.Point κ at x
    simp only [CommLaw.Hom.onPoints_comp]
    change M.Point κ at x
    change a • (f.onPoints (b • x)) = b • (a • f.onPoints x)
    rw [_root_.map_smul, smul_comm])⟩

@[simp]
theorem smul_toHom (a : O) (f : Hom M N) :
    (a • f).toHom = (N.action a).comp f.toHom := rfl

@[simp]
theorem onPoints_smul (a : O) (f : Hom M N) (x : M.Point κ) :
    (a • f).onPoints x = a • f.onPoints x :=
  CommLaw.Hom.onPoints_comp _ _ x

instance : Module O (Hom M N) where
  one_smul f := ext_onPoints (by intro x; simp only [onPoints_smul, _root_.one_smul])
  mul_smul a b f := ext_onPoints (by
    intro x
    simp only [onPoints_smul, SemigroupAction.mul_smul])
  smul_zero a := ext_onPoints (by intro x; simp only [onPoints_smul, onPoints_zero, smul_zero])
  smul_add a f g := ext_onPoints (by intro x; simp only [onPoints_smul, onPoints_add, smul_add])
  add_smul a b f := ext_onPoints (by intro x; simp only [onPoints_smul, onPoints_add, add_smul])
  zero_smul f := ext_onPoints (by intro x; simp only [onPoints_smul, onPoints_zero, zero_smul])

/-- Evaluation is O-linear in the formal homomorphism as well as in the point. -/
def onPointsLinear : Hom M N →ₗ[O] (M.Point κ →ₗ[O] N.Point κ) where
  toFun := onPoints
  map_add' f g := by ext x; exact onPoints_add f g x
  map_smul' a f := by ext x; exact onPoints_smul a f x

@[simp]
theorem comp_add (g : Hom N P) (f₁ f₂ : Hom M N) :
    g.comp (f₁ + f₂) = g.comp f₁ + g.comp f₂ := by
  apply ext_onPoints
  intro x
  simp only [onPoints_comp, onPoints_add, _root_.map_add]

@[simp]
theorem add_comp (g₁ g₂ : Hom N P) (f : Hom M N) :
    (g₁ + g₂).comp f = g₁.comp f + g₂.comp f := by
  apply ext_onPoints
  intro x
  simp only [onPoints_comp, onPoints_add]

@[simp]
theorem comp_smul (g : Hom N P) (a : O) (f : Hom M N) :
    g.comp (a • f) = a • g.comp f := by
  apply ext_onPoints
  intro x
  simp only [onPoints_comp, onPoints_smul, _root_.map_smul]

@[simp]
theorem smul_comp (a : O) (g : Hom N P) (f : Hom M N) :
    (a • g).comp f = a • g.comp f := by
  apply ext_onPoints
  intro x
  simp only [onPoints_comp, onPoints_smul]

@[simp]
theorem comp_zero (g : Hom N P) : g.comp (0 : Hom M N) = 0 := by
  apply ext_onPoints
  intro x
  simp only [onPoints_comp, onPoints_zero, _root_.map_zero]

@[simp]
theorem zero_comp (f : Hom M N) : (0 : Hom N P).comp f = 0 := by
  apply ext_onPoints
  intro x
  simp only [onPoints_comp, onPoints_zero]

/-- Composition is an O-bilinear operation on actual formal homomorphisms. -/
def compLinear : Hom N P →ₗ[O] Hom M N →ₗ[O] Hom M P where
  toFun g := {
    toFun := g.comp
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

/-- O-linear formal endomorphisms form a ring under composition. -/
instance : Ring (Hom M M) where
  mul := comp
  one := id M
  mul_assoc := comp_assoc
  one_mul := id_comp
  mul_one := comp_id
  left_distrib := comp_add
  right_distrib := add_comp
  zero_mul := zero_comp
  mul_zero := comp_zero

/-- Extend coefficients of an O-linear formal homomorphism. -/
def map (f : Hom M N) (φ : R →ₐ[O] S) : Hom (M.map φ) (N.map φ) where
  toHom := f.toHom.map φ.toRingHom
  commutes a := by
    change (f.toHom.map φ.toRingHom).comp ((M.action a).map φ.toRingHom) =
      ((N.action a).map φ.toRingHom).comp (f.toHom.map φ.toRingHom)
    rw [← CommLaw.Hom.map_comp, f.commutes, CommLaw.Hom.map_comp]

/-- Coefficient extension preserves the O-module structure of formal Hom. -/
def mapLinear (φ : R →ₐ[O] S) : Hom M N →ₗ[O] Hom (M.map φ) (N.map φ) where
  toFun f := f.map φ
  map_add' f g := by
    apply Hom.ext
    exact CommLaw.Hom.map_add_hom _ _ _
  map_smul' a f := by
    apply Hom.ext
    exact CommLaw.Hom.map_comp _ _ _

end Hom

/-- An isomorphism of formal O-modules with an O-linear inverse. -/
structure Iso (M : ModuleLaw O R σ) (N : ModuleLaw O R τ) where
  hom : Hom M N
  inv : Hom N M
  inv_hom : inv.comp hom = Hom.id M
  hom_inv : hom.comp inv = Hom.id N

namespace Iso

variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}

/-- An isomorphism of formal O-modules gives O-linear equivalences on points. -/
def onPoints (f : Iso M N) : M.Point κ ≃ₗ[O] N.Point κ where
  toFun := f.hom.onPoints
  invFun := f.inv.onPoints
  map_add' := f.hom.onPoints.map_add
  map_smul' := f.hom.onPoints.map_smul
  left_inv x := by rw [← Hom.onPoints_comp, f.inv_hom, Hom.onPoints_id]
  right_inv x := by rw [← Hom.onPoints_comp, f.hom_inv, Hom.onPoints_id]

end Iso

end Langlands.FormalGroup.ModuleLaw
