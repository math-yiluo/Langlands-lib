import Langlands.Geometry.FormalGroup.OrderAction

/-! # Rational maps commuting with actual formal order actions -/

noncomputable section

universe u v w z q

namespace Langlands.FormalGroup.ModuleLaw.OrderAction

variable {O : Type u} [CommRing O]
variable {A : Type v} [Ring A] [Algebra O A]
variable {R : Type w} [CommRing R] [Algebra O R]
variable {S : Type z} [CommRing S] [Algebra O S]
variable (F : Type q) [Field F] [Algebra O F]
variable {σ τ υ ω : Type} [Finite σ] [Finite τ] [Finite υ] [Finite ω]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable {P : ModuleLaw O R υ} {Q : ModuleLaw O R ω}
variable (E : OrderAction A M) (E' : OrderAction A N)
variable (E'' : OrderAction A P) (E''' : OrderAction A Q)

/-- The rational O-linear formal maps commuting with the given actual order actions. -/
def rationalHomSubmodule : Submodule F (ModuleLaw.RationalHom F M N) where
  carrier := {f | ∀ a : A,
    ModuleLaw.RationalHom.comp f (ModuleLaw.RationalHom.ofHom (E.action a)) =
      ModuleLaw.RationalHom.comp (ModuleLaw.RationalHom.ofHom (E'.action a)) f}
  zero_mem' := by intro a; simp
  add_mem' := by
    intro f g hf hg a
    simp only [ModuleLaw.RationalHom.add_comp, ModuleLaw.RationalHom.comp_add, hf a, hg a]
  smul_mem' := by
    intro a f hf b
    simp only [ModuleLaw.RationalHom.smul_comp, ModuleLaw.RationalHom.comp_smul, hf b]

/-- Order-equivariant maps inside the actual rational formal Hom. -/
def RationalHom : Type _ := ↥(rationalHomSubmodule F E E')

instance : AddCommGroup (RationalHom F E E') :=
  inferInstanceAs (AddCommGroup ↥(rationalHomSubmodule F E E'))

instance : Module F (RationalHom F E E') :=
  inferInstanceAs (Module F ↥(rationalHomSubmodule F E E'))

namespace RationalHom

variable {F E E' E'' E'''}

/-- Forgetting equivariance is an injective linear map into the actual tensor Hom. -/
def toLinearMap : RationalHom F E E' →ₗ[F] ModuleLaw.RationalHom F M N :=
  (rationalHomSubmodule F E E').subtype

@[ext]
theorem ext {f g : RationalHom F E E'} (h : f.val = g.val) : f = g :=
  Subtype.ext h

theorem commutes (f : RationalHom F E E') (a : A) :
    ModuleLaw.RationalHom.comp f.val (ModuleLaw.RationalHom.ofHom (E.action a)) =
      ModuleLaw.RationalHom.comp (ModuleLaw.RationalHom.ofHom (E'.action a)) f.val :=
  f.property a

/-- Rationalize an actual integral order-linear homomorphism. -/
def ofHom (f : Hom E E') : RationalHom F E E' :=
  ⟨ModuleLaw.RationalHom.ofHom f.val, by
    intro a
    rw [← ModuleLaw.RationalHom.ofHom_comp, f.commutes,
      ModuleLaw.RationalHom.ofHom_comp]⟩

/-- Identity order-equivariant rational map. -/
def id (E : OrderAction A M) : RationalHom F E E :=
  ⟨ModuleLaw.RationalHom.id M, by intro a; simp⟩

/-- Composition uses the actual rational formal composition. -/
def comp (g : RationalHom F E' E'') (f : RationalHom F E E') :
    RationalHom F E E'' :=
  ⟨ModuleLaw.RationalHom.comp g.val f.val, by
    intro a
    rw [ModuleLaw.RationalHom.comp_assoc, f.commutes,
      ← ModuleLaw.RationalHom.comp_assoc, g.commutes, ModuleLaw.RationalHom.comp_assoc]⟩

@[simp]
theorem comp_val (g : RationalHom F E' E'') (f : RationalHom F E E') :
    (g.comp f).val = ModuleLaw.RationalHom.comp g.val f.val := rfl

@[simp]
theorem ofHom_val (f : Hom E E') :
    (ofHom (F := F) f).val = ModuleLaw.RationalHom.ofHom f.val := rfl

@[simp]
theorem id_val (E : OrderAction A M) :
    (id (F := F) E).val = ModuleLaw.RationalHom.id M := rfl

@[simp]
theorem comp_id (f : RationalHom F E E') : f.comp (id E) = f := by
  apply ext
  exact ModuleLaw.RationalHom.comp_id f.val

@[simp]
theorem id_comp (f : RationalHom F E E') : (id E').comp f = f := by
  apply ext
  exact ModuleLaw.RationalHom.id_comp f.val

theorem comp_assoc (h : RationalHom F E'' E''') (g : RationalHom F E' E'')
    (f : RationalHom F E E') : (h.comp g).comp f = h.comp (g.comp f) := by
  apply ext
  exact ModuleLaw.RationalHom.comp_assoc h.val g.val f.val

@[simp]
theorem comp_add (g : RationalHom F E' E'') (f₁ f₂ : RationalHom F E E') :
    g.comp (f₁ + f₂) = g.comp f₁ + g.comp f₂ := by
  apply ext
  exact ModuleLaw.RationalHom.comp_add g.val f₁.val f₂.val

@[simp]
theorem add_comp (g₁ g₂ : RationalHom F E' E'') (f : RationalHom F E E') :
    (g₁ + g₂).comp f = g₁.comp f + g₂.comp f := by
  apply ext
  exact ModuleLaw.RationalHom.add_comp g₁.val g₂.val f.val

@[simp]
theorem comp_smul (g : RationalHom F E' E'') (a : F) (f : RationalHom F E E') :
    g.comp (a • f) = a • g.comp f := by
  apply ext
  exact ModuleLaw.RationalHom.comp_smul g.val a f.val

@[simp]
theorem smul_comp (a : F) (g : RationalHom F E' E'') (f : RationalHom F E E') :
    (a • g).comp f = a • g.comp f := by
  apply ext
  exact ModuleLaw.RationalHom.smul_comp a g.val f.val

@[simp]
theorem comp_zero (g : RationalHom F E' E'') :
    g.comp (0 : RationalHom F E E') = 0 := by
  apply ext
  exact ModuleLaw.RationalHom.comp_zero g.val

@[simp]
theorem zero_comp (f : RationalHom F E E') :
    (0 : RationalHom F E' E'').comp f = 0 := by
  apply ext
  exact ModuleLaw.RationalHom.zero_comp f.val

/-- The rational endomorphisms commuting with the order form a ring. -/
instance : Ring (RationalHom F E E) where
  mul := comp
  one := id E
  mul_assoc := comp_assoc
  one_mul := id_comp
  mul_one := comp_id
  left_distrib := comp_add
  right_distrib := add_comp
  zero_mul := zero_comp
  mul_zero := comp_zero

/-- Composition is bilinear over the rational scalar field. -/
def compLinear :
    RationalHom F E' E'' →ₗ[F] RationalHom F E E' →ₗ[F] RationalHom F E E'' where
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

@[simp]
theorem ofHom_id : ofHom (F := F) (Hom.id E) = id E := rfl

@[simp]
theorem ofHom_comp (g : Hom E' E'') (f : Hom E E') :
    ofHom (F := F) (g.comp f) = (ofHom g).comp (ofHom f) := by
  apply ext
  exact ModuleLaw.RationalHom.ofHom_comp g.val f.val

/-- Coefficient extension preserves the rational commutation equation. -/
def map (θ : R →ₐ[O] S) :
    RationalHom F E E' →ₗ[F] RationalHom F (E.map θ) (E'.map θ) where
  toFun f := ⟨ModuleLaw.RationalHom.map θ f.val, by
    intro a
    have h := congrArg (ModuleLaw.RationalHom.map θ) (f.commutes a)
    simpa only [ModuleLaw.RationalHom.map_comp, ModuleLaw.RationalHom.map_ofHom,
      OrderAction.map_action] using h⟩
  map_add' f g := by
    apply ext
    exact (ModuleLaw.RationalHom.map θ).map_add f.val g.val
  map_smul' a f := by
    apply ext
    exact (ModuleLaw.RationalHom.map θ).map_smul a f.val

@[simp]
theorem map_id (θ : R →ₐ[O] S) :
    map θ (id (F := F) E) = id (E.map θ) := by
  apply ext
  exact ModuleLaw.RationalHom.map_id θ

@[simp]
theorem map_comp (θ : R →ₐ[O] S) (g : RationalHom F E' E'')
    (f : RationalHom F E E') : map θ (g.comp f) = (map θ g).comp (map θ f) := by
  apply ext
  exact ModuleLaw.RationalHom.map_comp θ g.val f.val

@[simp]
theorem map_ofHom (θ : R →ₐ[O] S) (f : Hom E E') :
    map θ (ofHom (F := F) f) = ofHom (f.map θ) := by
  apply ext
  exact ModuleLaw.RationalHom.map_ofHom θ f.val

end RationalHom

/-- An order-equivariant quasi-isogeny is an invertible actual rational formal map. -/
structure QuasiIsogeny [IsDomain O] [IsFractionRing O F] where
  hom : RationalHom F E E'
  inv : RationalHom F E' E
  inv_hom : inv.comp hom = RationalHom.id E
  hom_inv : hom.comp inv = RationalHom.id E'

namespace QuasiIsogeny

variable [IsDomain O] [IsFractionRing O F]
variable {F E E' E''}

/-- Forget the order action while retaining the actual invertible rational map. -/
def toModuleQuasiIsogeny (f : QuasiIsogeny F E E') : ModuleLaw.QuasiIsogeny F M N where
  hom := f.hom.val
  inv := f.inv.val
  inv_hom := congrArg Subtype.val f.inv_hom
  hom_inv := congrArg Subtype.val f.hom_inv

/-- An inverse rational map commutes with the order whenever the forward map does. -/
theorem inverse_commutes (f : ModuleLaw.QuasiIsogeny F M N)
    (h : ∀ a : A,
      ModuleLaw.RationalHom.comp f.hom (ModuleLaw.RationalHom.ofHom (E.action a)) =
        ModuleLaw.RationalHom.comp (ModuleLaw.RationalHom.ofHom (E'.action a)) f.hom)
    (a : A) :
    ModuleLaw.RationalHom.comp f.inv (ModuleLaw.RationalHom.ofHom (E'.action a)) =
      ModuleLaw.RationalHom.comp (ModuleLaw.RationalHom.ofHom (E.action a)) f.inv := by
  calc
    ModuleLaw.RationalHom.comp f.inv (ModuleLaw.RationalHom.ofHom (E'.action a)) =
        ModuleLaw.RationalHom.comp
          (ModuleLaw.RationalHom.comp f.inv (ModuleLaw.RationalHom.ofHom (E'.action a)))
          (ModuleLaw.RationalHom.id N) := (ModuleLaw.RationalHom.comp_id _).symm
    _ = ModuleLaw.RationalHom.comp
          (ModuleLaw.RationalHom.comp f.inv (ModuleLaw.RationalHom.ofHom (E'.action a)))
          (ModuleLaw.RationalHom.comp f.hom f.inv) := by rw [f.hom_inv]
    _ = ModuleLaw.RationalHom.comp
          (ModuleLaw.RationalHom.comp f.inv
            (ModuleLaw.RationalHom.comp (ModuleLaw.RationalHom.ofHom (E'.action a)) f.hom))
          f.inv := by simp only [ModuleLaw.RationalHom.comp_assoc]
    _ = ModuleLaw.RationalHom.comp
          (ModuleLaw.RationalHom.comp f.inv
            (ModuleLaw.RationalHom.comp f.hom (ModuleLaw.RationalHom.ofHom (E.action a))))
          f.inv := by rw [h a]
    _ = ModuleLaw.RationalHom.comp (ModuleLaw.RationalHom.ofHom (E.action a)) f.inv := by
      rw [← ModuleLaw.RationalHom.comp_assoc f.inv, f.inv_hom,
        ModuleLaw.RationalHom.id_comp]

/-- Upgrade an actual quasi-isogeny using equivariance of its forward map alone. -/
def ofModuleQuasiIsogeny (f : ModuleLaw.QuasiIsogeny F M N)
    (h : ∀ a : A,
      ModuleLaw.RationalHom.comp f.hom (ModuleLaw.RationalHom.ofHom (E.action a)) =
        ModuleLaw.RationalHom.comp (ModuleLaw.RationalHom.ofHom (E'.action a)) f.hom) :
    QuasiIsogeny F E E' where
  hom := ⟨f.hom, h⟩
  inv := ⟨f.inv, inverse_commutes f h⟩
  inv_hom := RationalHom.ext f.inv_hom
  hom_inv := RationalHom.ext f.hom_inv

@[simp]
theorem toModule_ofModuleQuasiIsogeny (f : ModuleLaw.QuasiIsogeny F M N)
    (h : ∀ a : A,
      ModuleLaw.RationalHom.comp f.hom (ModuleLaw.RationalHom.ofHom (E.action a)) =
        ModuleLaw.RationalHom.comp (ModuleLaw.RationalHom.ofHom (E'.action a)) f.hom) :
    (ofModuleQuasiIsogeny f h).toModuleQuasiIsogeny = f := by
  apply ModuleLaw.QuasiIsogeny.ext
  rfl

/-- Identity order-equivariant quasi-isogeny. -/
def refl (E : OrderAction A M) : QuasiIsogeny F E E where
  hom := RationalHom.id E
  inv := RationalHom.id E
  inv_hom := RationalHom.id_comp _
  hom_inv := RationalHom.id_comp _

/-- Invert an order-equivariant quasi-isogeny. -/
def symm (f : QuasiIsogeny F E E') : QuasiIsogeny F E' E where
  hom := f.inv
  inv := f.hom
  inv_hom := f.hom_inv
  hom_inv := f.inv_hom

/-- Compose order-equivariant quasi-isogenies. -/
def trans (f : QuasiIsogeny F E E') (g : QuasiIsogeny F E' E'') :
    QuasiIsogeny F E E'' where
  hom := g.hom.comp f.hom
  inv := f.inv.comp g.inv
  inv_hom := by
    rw [RationalHom.comp_assoc, ← RationalHom.comp_assoc g.inv, g.inv_hom,
      RationalHom.id_comp, f.inv_hom]
  hom_inv := by
    rw [RationalHom.comp_assoc, ← RationalHom.comp_assoc f.hom, f.hom_inv,
      RationalHom.id_comp, g.hom_inv]

/-- Rationalize an actual order-linear formal isomorphism. -/
def ofIso (f : Iso E E') : QuasiIsogeny F E E' where
  hom := RationalHom.ofHom f.hom
  inv := RationalHom.ofHom f.inv
  inv_hom := by
    rw [← RationalHom.ofHom_comp, f.inv_hom, RationalHom.ofHom_id]
  hom_inv := by
    rw [← RationalHom.ofHom_comp, f.hom_inv, RationalHom.ofHom_id]

/-- An inverse is determined by the forward rational map. -/
theorem inv_unique (f : QuasiIsogeny F E E') (g : RationalHom F E' E)
    (h : g.comp f.hom = RationalHom.id E) : g = f.inv := by
  apply RationalHom.ext
  exact f.toModuleQuasiIsogeny.inv_unique g.val (congrArg Subtype.val h)

@[ext]
theorem ext {f g : QuasiIsogeny F E E'} (h : f.hom = g.hom) : f = g := by
  have hi : f.inv = g.inv := g.inv_unique f.inv (by rw [← h]; exact f.inv_hom)
  cases f
  cases g
  cases h
  cases hi
  rfl

/-- Extend coefficients of an actual order-equivariant quasi-isogeny. -/
def map (θ : R →ₐ[O] S) (f : QuasiIsogeny F E E') :
    QuasiIsogeny F (E.map θ) (E'.map θ) where
  hom := RationalHom.map θ f.hom
  inv := RationalHom.map θ f.inv
  inv_hom := by rw [← RationalHom.map_comp, f.inv_hom, RationalHom.map_id]
  hom_inv := by rw [← RationalHom.map_comp, f.hom_inv, RationalHom.map_id]

@[simp]
theorem map_refl (θ : R →ₐ[O] S) :
    (refl (F := F) E).map θ = refl (E.map θ) := by
  apply ext
  exact RationalHom.map_id θ

@[simp]
theorem map_symm (θ : R →ₐ[O] S) (f : QuasiIsogeny F E E') :
    f.symm.map θ = (f.map θ).symm := rfl

@[simp]
theorem map_trans (θ : R →ₐ[O] S) (f : QuasiIsogeny F E E')
    (g : QuasiIsogeny F E' E'') :
    (f.trans g).map θ = (f.map θ).trans (g.map θ) := by
  apply ext
  exact RationalHom.map_comp θ g.hom f.hom

@[simp]
theorem map_ofIso (θ : R →ₐ[O] S) (f : Iso E E') :
    (ofIso (F := F) f).map θ = ofIso (f.map θ) := by
  apply ext
  exact RationalHom.map_ofHom θ f.hom

end QuasiIsogeny

end Langlands.FormalGroup.ModuleLaw.OrderAction
