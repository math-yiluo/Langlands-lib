import Langlands.Geometry.FormalGroup.GlobalAtlasRationalMorphism
import Langlands.Geometry.FormalGroup.OrderAction

/-! # Scalar algebra on the whole rational formal endomorphism ring -/

noncomputable section

universe u v w z

namespace Langlands.FormalGroup.ModuleLaw.RationalHom

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {S : Type w} [CommRing S] [Algebra O S]
variable {F : Type z} [Field F] [Algebra O F]
variable {σ : Type} [Finite σ] {M : ModuleLaw O R σ}

/-- The existing rational formal composition ring carries its scalar field algebra. -/
instance : Algebra F (RationalHom F M M) :=
  Algebra.ofModule smul_comp (fun a f g => comp_smul f a g)

@[simp]
theorem algebraMap_eq_smul_id (a : F) :
    algebraMap F (RationalHom F M M) a = a • id M := rfl

/-- Rationalization is a ring map on actual formal endomorphisms. -/
def ofHomEnd : Hom M M →+* RationalHom F M M where
  toFun := ofHom
  map_zero' := ofHom.map_zero
  map_add' := ofHom.map_add
  map_one' := ofHom_id
  map_mul' := ofHom_comp

@[simp]
theorem ofHomEnd_apply (f : Hom M M) :
    ofHomEnd (F := F) f = ofHom f := rfl

/-- Extending coefficients gives a map of the actual rational formal endomorphism algebras. -/
def mapEnd (φ : R →ₐ[O] S) : RationalHom F M M →ₐ[F] RationalHom F (M.map φ) (M.map φ) where
  toFun := map φ
  map_zero' := (map φ).map_zero
  map_add' := (map φ).map_add
  map_one' := map_id φ
  map_mul' := map_comp φ
  commutes' a := by
    change map (F := F) φ (a • id M) = a • id (M.map φ)
    rw [LinearMap.map_smul, map_id]

@[simp]
theorem mapEnd_apply (φ : R →ₐ[O] S) (f : RationalHom F M M) :
    mapEnd φ f = map φ f := rfl

end Langlands.FormalGroup.ModuleLaw.RationalHom
