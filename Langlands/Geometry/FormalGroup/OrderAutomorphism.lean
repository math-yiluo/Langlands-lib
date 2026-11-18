import Langlands.Geometry.FormalGroup.OrderIso
import Langlands.Geometry.FormalGroup.GlobalAtlasOrderBaseChange

/-! # Actual integral full-order formal automorphisms -/

noncomputable section

universe u v w x y

namespace Langlands.FormalGroup.ModuleLaw.OrderAction

variable {O : Type u} [CommRing O]
variable {D : Type v} [Ring D] [Algebra O D]
variable {R : Type w} [CommRing R] [Algebra O R]
variable {S : Type w} [CommRing S] [Algebra O S]
variable {T : Type w} [CommRing T] [Algebra O T]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {P : ModuleLaw O R υ}
variable {E : OrderAction D M} {E' : OrderAction D N} {E'' : OrderAction D P}

namespace Iso

/-- Integral full-order isomorphisms compose associatively. -/
theorem trans_assoc (a : Iso E E') (b : Iso E' E'')
    {ω : Type} [Finite ω] {Q : ModuleLaw O R ω} {E''' : OrderAction D Q} (c : Iso E'' E''') :
    (a.trans b).trans c = a.trans (b.trans c) := by
  apply ext_hom
  exact (Hom.comp_assoc c.hom b.hom a.hom).symm

@[simp]
theorem refl_trans (a : Iso E E') : (refl E).trans a = a := by
  apply ext_hom
  exact Hom.comp_id _

@[simp]
theorem trans_refl (a : Iso E E') : a.trans (refl E') = a := by
  apply ext_hom
  exact Hom.id_comp _

@[simp]
theorem self_trans_symm (a : Iso E E') : a.trans a.symm = refl E := by
  apply ext_hom
  exact a.inv_hom

@[simp]
theorem symm_trans_self (a : Iso E E') : a.symm.trans a = refl E' := by
  apply ext_hom
  exact a.hom_inv

@[simp]
theorem map_refl (E : OrderAction D M) (f : R →ₐ[O] S) :
    (refl E).map f = refl (E.map f) := by
  apply ext_hom
  exact Hom.map_id f

@[simp]
theorem map_trans (a : Iso E E') (b : Iso E' E'') (f : R →ₐ[O] S) :
    (a.trans b).map f = (a.map f).trans (b.map f) := by
  apply ext_hom
  exact Hom.map_comp f b.hom a.hom

@[simp]
theorem map_symm (a : Iso E E') (f : R →ₐ[O] S) : a.symm.map f = (a.map f).symm := rfl

/-- The actual coefficient-composition comparison is natural in integral full-order isomorphisms. -/
theorem mapComp_natural (a : Iso E E') (f : R →ₐ[O] S) (g : S →ₐ[O] T) :
    ((a.map f).map g).trans (E'.mapCompIso f g) =
      (E.mapCompIso f g).trans (a.map (g.comp f)) := by
  apply ext_hom
  apply Subtype.ext
  apply ModuleLaw.Hom.ext
  apply CommLaw.Hom.ext
  change CoordinateMap.id.comp
    ((a.hom.val.toHom.toCoordinateMap.map f.toRingHom).map g.toRingHom) =
      (a.hom.val.toHom.toCoordinateMap.map (g.comp f).toRingHom).comp CoordinateMap.id
  rw [CoordinateMap.id_comp, CoordinateMap.comp_id, CoordinateMap.map_ringHom_comp]
  rfl

end Iso

/-- Automorphisms are the actual integral full-order formal isomorphisms from the module to itself. -/
def Automorphism (E : OrderAction D M) := Iso E E

namespace Automorphism

instance (E : OrderAction D M) : Group (Automorphism E) where
  one := Iso.refl E
  mul a b := b.trans a
  inv a := a.symm
  one_mul a := Iso.trans_refl a
  mul_one a := Iso.refl_trans a
  mul_assoc a b c := (Iso.trans_assoc c b a).symm
  inv_mul_cancel a := Iso.self_trans_symm a

/-- View the same actual forward and inverse formal maps as an isomorphism. -/
def toIso (a : Automorphism E) : Iso E E := a

@[simp]
theorem toIso_one : toIso (1 : Automorphism E) = Iso.refl E := rfl

@[simp]
theorem toIso_mul (a b : Automorphism E) : (a * b).toIso = b.toIso.trans a.toIso := rfl

@[simp]
theorem toIso_inv (a : Automorphism E) : a⁻¹.toIso = a.toIso.symm := rfl

/-- Extend both actual inverse formal maps; this is a homomorphism of automorphism groups. -/
def mapHom (f : R →ₐ[O] S) : Automorphism E →* Automorphism (E.map f) where
  toFun a := a.toIso.map f
  map_one' := Iso.map_refl E f
  map_mul' a b := Iso.map_trans b.toIso a.toIso f

@[simp]
theorem toIso_mapHom (a : Automorphism E) (f : R →ₐ[O] S) :
    (mapHom f a).toIso = a.toIso.map f := rfl

end Automorphism

end Langlands.FormalGroup.ModuleLaw.OrderAction
