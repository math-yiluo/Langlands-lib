import Langlands.Geometry.FormalGroup.AtlasRationalBaseChange
import Langlands.Geometry.FormalGroup.RationalEndAlgebra

/-! # Scalar algebra of whole rational formal atlas endomorphisms -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.RationalHom

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {F : Type w} [Field F] [Algebra O F]
variable {σ : Type} [Finite σ] {X : BasicAtlas O R σ}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- The existing composition ring of whole rational atlas maps is an `F`-algebra. -/
instance : Algebra F (RationalHom F X X rfl) :=
  Algebra.ofModule smul_comp (fun a f g => comp_smul f a g)

@[simp]
theorem algebraMap_eq_smul_id (a : F) :
    algebraMap F (RationalHom F X X rfl) a = a • id X := rfl

/-- Rationalization is a ring homomorphism on actual formal atlas endomorphisms. -/
def ofHomEnd : Hom X X rfl →+* RationalHom F X X rfl where
  toFun := ofHom
  map_zero' := ofHom.map_zero
  map_add' := ofHom.map_add
  map_one' := ofHom_id
  map_mul' := ofHom_comp

@[simp]
theorem ofHomEnd_apply (f : Hom X X rfl) :
    ofHomEnd (F := F) f = ofHom f := rfl

/-- Taking the actual coordinate endomorphism on a test chart is an `F`-algebra map. -/
def onChartEnd (A : CommAlgCat.{v} R) (b : X.opens)
    (hb : IsUnit (algebraMap R A b.val)) :
    RationalHom F X X rfl →ₐ[F]
      ModuleLaw.RationalHom F
        ((X.chart b).map (coefficientLift (O := O) b.val A hb))
        ((X.chart b).map (coefficientLift (O := O) b.val A hb)) where
  toFun := onChart (X := X) (h := rfl) A b hb
  map_zero' := (onChart (X := X) (h := rfl) A b hb).map_zero
  map_add' := (onChart (X := X) (h := rfl) A b hb).map_add
  map_one' := onChart_id A b hb
  map_mul' g f := onChart_comp g f A b hb
  commutes' a := by
    change onChart (F := F) (X := X) (h := rfl) A b hb (a • id (F := F) X) =
      a • ModuleLaw.RationalHom.id (F := F) _
    rw [_root_.map_smul, onChart_id]

@[simp]
theorem onChartEnd_apply (A : CommAlgCat.{v} R) (b : X.opens)
    (hb : IsUnit (algebraMap R A b.val)) (f : RationalHom F X X rfl) :
    onChartEnd (F := F) A b hb f = onChart (F := F) (X := X) (h := rfl) A b hb f := rfl

/-- Extending the atlas coefficients preserves the whole rational endomorphism algebra. -/
def baseChangeEnd (X : BasicAtlas O R σ) (S : CommAlgCat.{v} R) :
    RationalHom F X X rfl →ₐ[F] RationalHom F (X.baseChange S) (X.baseChange S) rfl where
  toRingHom := baseChangeRingHom X S
  commutes' a := by
    change baseChange (F := F) (X := X) (h := rfl) S (a • id (F := F) X) =
      a • id (F := F) (X.baseChange S)
    rw [_root_.map_smul, baseChange_id]

@[simp]
theorem baseChangeEnd_apply (S : CommAlgCat.{v} R) (f : RationalHom F X X rfl) :
    baseChangeEnd (F := F) X S f = baseChange (F := F) (X := X) (h := rfl) S f := rfl

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.RationalHom
