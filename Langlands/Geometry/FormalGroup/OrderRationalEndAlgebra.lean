import Langlands.Geometry.FormalGroup.OrderRationalMorphism

/-! # The actual rational full-order endomorphism algebra and its units -/

noncomputable section

universe u v w z q

namespace Langlands.FormalGroup.ModuleLaw.OrderAction

variable {O : Type u} [CommRing O]
variable {D : Type v} [Ring D] [Algebra O D]
variable {R : Type w} [CommRing R] [Algebra O R]
variable {S : Type z} [CommRing S] [Algebra O S]
variable {F : Type q} [Field F] [Algebra O F]
variable {σ : Type} [Finite σ] {M : ModuleLaw O R σ} {E : OrderAction D M}

namespace RationalHom

/-- The existing actual rational full-order endomorphism ring is an algebra over its rational scalar field. -/
instance : Algebra F (RationalHom F E E) :=
  Algebra.ofModule (fun a f g => smul_comp a f g) (fun a f g => comp_smul f a g)

/-- Scalar endomorphisms are precisely the scalar multiples of the actual rational identity. -/
@[simp]
theorem algebraMap_eq_smul_id (a : F) :
    algebraMap F (RationalHom F E E) a = a • id E := rfl

/-- Actual coefficient extension is a homomorphism of rational full-order endomorphism algebras. -/
def mapEnd (θ : R →ₐ[O] S) : RationalHom F E E →ₐ[F] RationalHom F (E.map θ) (E.map θ) where
  toFun := map θ
  map_zero' := (map θ).map_zero
  map_add' := (map θ).map_add
  map_one' := map_id θ
  map_mul' := fun f g => map_comp θ f g
  commutes' a := by
    change map (F := F) (E := E) (E' := E) θ (a • id E) = a • id (E.map θ)
    rw [(map (F := F) (E := E) (E' := E) θ).map_smul, map_id]

@[simp]
theorem mapEnd_apply (θ : R →ₐ[O] S) (f : RationalHom F E E) : mapEnd θ f = map θ f := rfl

end RationalHom

namespace QuasiIsogeny

variable [IsDomain O] [IsFractionRing O F]

/-- A unit of the actual rational centralizer gives the actual forward and inverse formal maps. -/
def ofUnit (a : (RationalHom F E E)ˣ) : QuasiIsogeny F E E where
  hom := a.val
  inv := a.inv
  inv_hom := a.inv_val
  hom_inv := a.val_inv

/-- The actual inverse rational maps form a unit in the same rational endomorphism ring. -/
def toUnit (a : QuasiIsogeny F E E) : (RationalHom F E E)ˣ where
  val := a.hom
  inv := a.inv
  val_inv := a.hom_inv
  inv_val := a.inv_hom

@[simp]
theorem ofUnit_hom (a : (RationalHom F E E)ˣ) : (ofUnit a).hom = a.val := rfl

@[simp]
theorem ofUnit_inv (a : (RationalHom F E E)ˣ) : (ofUnit a).inv = a.inv := rfl

@[simp]
theorem toUnit_ofUnit (a : (RationalHom F E E)ˣ) : (ofUnit a).toUnit = a := by
  apply Units.ext
  rfl

@[simp]
theorem ofUnit_toUnit (a : QuasiIsogeny F E E) : ofUnit a.toUnit = a := by
  apply ext
  rfl

/-- Actual rational automorphisms are exactly the units of the actual rational full-order endomorphism algebra. -/
def unitEquiv : (RationalHom F E E)ˣ ≃ QuasiIsogeny F E E where
  toFun := ofUnit
  invFun := toUnit
  left_inv := toUnit_ofUnit
  right_inv := ofUnit_toUnit

/-- Functional unit multiplication corresponds to reversed `trans` composition order. -/
theorem ofUnit_mul (a b : (RationalHom F E E)ˣ) :
    ofUnit (a * b) = (ofUnit b).trans (ofUnit a) := by
  apply ext
  rfl

@[simp]
theorem ofUnit_one : ofUnit (1 : (RationalHom F E E)ˣ) = refl E := by
  apply ext
  rfl

@[simp]
theorem ofUnit_inv_unit (a : (RationalHom F E E)ˣ) : ofUnit a⁻¹ = (ofUnit a).symm := by
  apply ext
  rfl

/-- Extending both inverse maps is exactly mapping their actual endomorphism-ring unit. -/
theorem ofUnit_map (a : (RationalHom F E E)ˣ) (θ : R →ₐ[O] S) :
    (ofUnit a).map θ = ofUnit (Units.map (RationalHom.mapEnd θ).toMonoidHom a) := by
  apply ext
  rfl

end QuasiIsogeny

end Langlands.FormalGroup.ModuleLaw.OrderAction
