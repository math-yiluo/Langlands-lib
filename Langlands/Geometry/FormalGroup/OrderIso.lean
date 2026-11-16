import Langlands.Geometry.FormalGroup.OrderAction

/-! # Actual formal isomorphisms commuting with an acting order -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw.OrderAction

variable {O : Type u} [CommRing O]
variable {D : Type v} [Ring D] [Algebra O D]
variable {R : Type w} [CommRing R] [Algebra O R]
variable {σ τ υ ω : Type} [Finite σ] [Finite τ] [Finite υ] [Finite ω]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
  {P : ModuleLaw O R υ} {Q : ModuleLaw O R ω}
variable {E : OrderAction D M} {E' : OrderAction D N}
  {E'' : OrderAction D P} {E''' : OrderAction D Q}

namespace Hom

@[simp]
theorem comp_id (f : Hom E E') : f.comp (id E) = f :=
  Subtype.ext (ModuleLaw.Hom.comp_id f.val)

@[simp]
theorem id_comp (f : Hom E E') : (id E').comp f = f :=
  Subtype.ext (ModuleLaw.Hom.id_comp f.val)

theorem comp_assoc (q : Hom E'' E''') (g : Hom E' E'') (f : Hom E E') :
    (q.comp g).comp f = q.comp (g.comp f) :=
  Subtype.ext (ModuleLaw.Hom.comp_assoc q.val g.val f.val)

end Hom

namespace Iso

/-- The inverse of an actual formal isomorphism commutes with the order
whenever its forward formal map does. -/
theorem inverse_commutes (f : ModuleLaw.Iso M N)
    (h : ∀ d : D, f.hom.comp (E.action d) = (E'.action d).comp f.hom)
    (d : D) :
    f.inv.comp (E'.action d) = (E.action d).comp f.inv := by
  calc
    f.inv.comp (E'.action d) =
        (f.inv.comp (E'.action d)).comp (f.hom.comp f.inv) := by
      rw [f.hom_inv, ModuleLaw.Hom.comp_id]
    _ = (f.inv.comp ((E'.action d).comp f.hom)).comp f.inv := by
      simp only [ModuleLaw.Hom.comp_assoc]
    _ = (f.inv.comp (f.hom.comp (E.action d))).comp f.inv := by rw [h d]
    _ = (E.action d).comp f.inv := by
      rw [← ModuleLaw.Hom.comp_assoc f.inv, f.inv_hom, ModuleLaw.Hom.id_comp]

/-- Upgrade the actual formal isomorphism from order commutation of its forward map. -/
def ofModuleIso (f : ModuleLaw.Iso M N)
    (h : ∀ d : D, f.hom.comp (E.action d) = (E'.action d).comp f.hom) :
    Iso E E' where
  hom := ⟨f.hom, h⟩
  inv := ⟨f.inv, inverse_commutes f h⟩
  inv_hom := Subtype.ext f.inv_hom
  hom_inv := Subtype.ext f.hom_inv

@[simp]
theorem toModuleIso_ofModuleIso (f : ModuleLaw.Iso M N)
    (h : ∀ d : D, f.hom.comp (E.action d) = (E'.action d).comp f.hom) :
    (ofModuleIso f h).toModuleIso = f := rfl

/-- The identity actual full-order formal isomorphism. -/
def refl (E : OrderAction D M) : Iso E E where
  hom := Hom.id E
  inv := Hom.id E
  inv_hom := Hom.comp_id _
  hom_inv := Hom.comp_id _

/-- Reverse both actual order-linear maps. -/
def symm (f : Iso E E') : Iso E' E where
  hom := f.inv
  inv := f.hom
  inv_hom := f.hom_inv
  hom_inv := f.inv_hom

/-- Compose actual full-order formal isomorphisms. -/
def trans (f : Iso E E') (g : Iso E' E'') : Iso E E'' where
  hom := g.hom.comp f.hom
  inv := f.inv.comp g.inv
  inv_hom := by
    rw [Hom.comp_assoc, ← Hom.comp_assoc g.inv, g.inv_hom, Hom.id_comp, f.inv_hom]
  hom_inv := by
    rw [Hom.comp_assoc, ← Hom.comp_assoc f.hom, f.hom_inv, Hom.id_comp, g.hom_inv]

@[simp]
theorem toModuleIso_refl (E : OrderAction D M) :
    (refl E).toModuleIso = ModuleLaw.Iso.refl M := rfl

@[simp]
theorem toModuleIso_symm (f : Iso E E') :
    f.symm.toModuleIso = f.toModuleIso.symm := rfl

@[simp]
theorem toModuleIso_trans (f : Iso E E') (g : Iso E' E'') :
    (f.trans g).toModuleIso = f.toModuleIso.trans g.toModuleIso := rfl

theorem inv_unique (f : Iso E E') (g : Hom E' E)
    (h : g.comp f.hom = Hom.id E) : g = f.inv := by
  calc
    g = g.comp (Hom.id E') := (Hom.comp_id _).symm
    _ = g.comp (f.hom.comp f.inv) := by rw [f.hom_inv]
    _ = (g.comp f.hom).comp f.inv := (Hom.comp_assoc _ _ _).symm
    _ = f.inv := by rw [h, Hom.id_comp]

@[ext]
theorem ext_hom {f g : Iso E E'} (h : f.hom = g.hom) : f = g := by
  have hi : f.inv = g.inv := g.inv_unique f.inv (by rw [← h]; exact f.inv_hom)
  cases f
  cases g
  cases h
  cases hi
  rfl

end Iso

end Langlands.FormalGroup.ModuleLaw.OrderAction
