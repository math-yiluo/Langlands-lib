import Langlands.CategoryTheory.Rationalization
import Mathlib.CategoryTheory.Linear.LinearFunctor

/-! # The category with homomorphisms `R ⊗[ℤ] Hom` for a commutative ring `R` -/

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe v₁ v₂ u₁ u₂

namespace Langlands

/-- The objects of the coefficient extension by `R` are precisely wrapped objects of `C`. -/
structure CoefficientExtension (R : Type) (C : Type u₁) where
  of ::
  obj : C

namespace CoefficientExtension

variable (R : Type) [CommRing R] {C : Type u₁} [Category.{v₁} C] [Preadditive C]

/-- The group of morphisms with coefficients in `R`. -/
abbrev Hom (X Y : C) := R ⊗[ℤ] (X ⟶ Y)

/-- Composition obtained from the tensor universal property. -/
def comp (X Y Z : C) : Hom R X Y →ₗ[ℤ] Hom R Y Z →ₗ[ℤ] Hom R X Z :=
  TensorProduct.map₂ (LinearMap.mul ℤ R) (CategoryTheory.Linear.comp (S := ℤ) X Y Z)

variable {R}

@[simp] theorem comp_tmul {X Y Z : C} (r s : R) (f : X ⟶ Y) (g : Y ⟶ Z) :
    comp R X Y Z (r ⊗ₜ[ℤ] f) (s ⊗ₜ[ℤ] g) = (r * s) ⊗ₜ[ℤ] (f ≫ g) := rfl

variable (R) in
/-- The identity with coefficient one. -/
def identity (X : C) : Hom R X X := (1 : R) ⊗ₜ[ℤ] 𝟙 X

@[simp] theorem identity_comp {X Y : C} (f : Hom R X Y) :
    comp R X X Y (identity R X) f = f := by
  induction f using TensorProduct.inductionOn with
  | tmul r f => simp [identity]
  | add f g hf hg => simp [hf, hg]

@[simp] theorem comp_identity {X Y : C} (f : Hom R X Y) :
    comp R X Y Y f (identity R Y) = f := by
  induction f using TensorProduct.inductionOn with
  | tmul r f => simp [identity]
  | add f g hf hg => simp [hf, hg]

theorem comp_assoc {W X Y Z : C} (f : Hom R W X) (g : Hom R X Y) (h : Hom R Y Z) :
    comp R W Y Z (comp R W X Y f g) h = comp R W X Z f (comp R X Y Z g h) := by
  induction f using TensorProduct.inductionOn with
  | add f f' hf hf' => simp [hf, hf']
  | tmul q f =>
    induction g using TensorProduct.inductionOn with
    | add g g' hg hg' => simp [hg, hg']
    | tmul r g =>
      induction h using TensorProduct.inductionOn with
      | add h h' hh hh' => simp only [map_add, hh, hh']
      | tmul s h => simp [mul_assoc, Category.assoc]

/-- Composition is `R`-linear in its first argument. -/
theorem comp_smul_left {X Y Z : C} (r : R) (f : Hom R X Y) (g : Hom R Y Z) :
    comp R X Y Z (r • f) g = r • comp R X Y Z f g := by
  induction f using TensorProduct.inductionOn with
  | add f f' hf hf' => simp only [smul_add, map_add, LinearMap.add_apply, hf, hf']
  | tmul s f =>
    induction g using TensorProduct.inductionOn with
    | add g g' hg hg' => simp only [map_add, smul_add, hg, hg']
    | tmul t g => simp [TensorProduct.smul_tmul', mul_assoc]

/-- Composition is `R`-linear in its second argument. -/
theorem comp_smul_right {X Y Z : C} (r : R) (f : Hom R X Y) (g : Hom R Y Z) :
    comp R X Y Z f (r • g) = r • comp R X Y Z f g := by
  induction f using TensorProduct.inductionOn with
  | add f f' hf hf' => simp only [smul_add, map_add, LinearMap.add_apply, hf, hf']
  | tmul s f =>
    induction g using TensorProduct.inductionOn with
    | add g g' hg hg' => simp only [map_add, smul_add, hg, hg']
    | tmul t g => simp [TensorProduct.smul_tmul', mul_left_comm]

variable (R) in
/-- Composition bundled as an `R`-bilinear map. -/
def compLinear (X Y Z : C) : Hom R X Y →ₗ[R] Hom R Y Z →ₗ[R] Hom R X Z :=
  LinearMap.mk₂ R (fun f g => comp R X Y Z f g)
    (fun f f' g => (comp R X Y Z).map_add₂ f f' g)
    (fun r f g => comp_smul_left r f g)
    (fun f g g' => (comp R X Y Z f).map_add g g')
    (fun r f g => comp_smul_right r f g)

@[simp] theorem compLinear_apply {X Y Z : C} (f : Hom R X Y) (g : Hom R Y Z) :
    compLinear R X Y Z f g = comp R X Y Z f g := rfl

instance : Category.{v₁} (CoefficientExtension R C) where
  Hom X Y := Hom R X.obj Y.obj
  id X := identity R X.obj
  comp f g := comp R _ _ _ f g
  id_comp := identity_comp
  comp_id := comp_identity
  assoc := comp_assoc

instance : Preadditive (CoefficientExtension R C) where
  homGroup X Y := inferInstanceAs (AddCommGroup (Hom R X.obj Y.obj))
  add_comp X Y Z f f' g := (comp R X.obj Y.obj Z.obj).map_add₂ f f' g
  comp_add X Y Z f g g' := (comp R X.obj Y.obj Z.obj f).map_add g g'

instance (X Y : CoefficientExtension R C) : Module R (X ⟶ Y) :=
  inferInstanceAs (Module R (Hom R X.obj Y.obj))

instance : Linear R (CoefficientExtension R C) where
  homModule X Y := inferInstanceAs (Module R (Hom R X.obj Y.obj))
  smul_comp _ _ _ r f g := comp_smul_left r f g
  comp_smul _ _ _ f r g := comp_smul_right r f g

variable (R) in
/-- Ordinary morphisms map to tensors with coefficient one. -/
def ofHom {X Y : C} : (X ⟶ Y) →ₗ[ℤ] Hom R X Y :=
  TensorProduct.mk ℤ R (X ⟶ Y) 1

@[simp] theorem ofHom_apply {X Y : C} (f : X ⟶ Y) :
    ofHom R f = (1 : R) ⊗ₜ[ℤ] f := rfl

@[simp] theorem comp_ofHom {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    comp R X Y Z (ofHom R f) (ofHom R g) = ofHom R (f ≫ g) := by
  simp

/-- A pure tensor is the coefficient times the image of the ordinary morphism. -/
theorem tmul_eq_smul_ofHom {X Y : C} (r : R) (f : X ⟶ Y) :
    r ⊗ₜ[ℤ] f = r • ofHom R f := by
  simp [TensorProduct.smul_tmul']

variable (R) in
/-- The canonical additive functor to the coefficient extension. -/
def inclusion : C ⥤ CoefficientExtension R C where
  obj := of
  map := ofHom R
  map_id X := rfl
  map_comp f g := by
    change ofHom R (f ≫ g) = comp R _ _ _ (ofHom R f) (ofHom R g)
    simp

instance : (inclusion R (C := C)).Additive where
  map_add {_X _Y f g} := map_add (ofHom R) f g

variable (R) in
/-- The actual endomorphism `R`-algebra of an object of the coefficient extension. -/
abbrev End (X : C) := CategoryTheory.End (of (R := R) X)

/-- The `R`-algebra structure uses the tensor identity as its unit. -/
@[simp] theorem algebraMap_eq (X : C) (r : R) :
    algebraMap R (End R X) r = CategoryTheory.End.of (r ⊗ₜ[ℤ] 𝟙 X) := by
  apply CategoryTheory.End.ext
  change r • ((1 : R) ⊗ₜ[ℤ] 𝟙 X) = _
  simp [TensorProduct.smul_tmul']

variable (R) in
/-- The canonical unital ring map of endomorphism rings. -/
def ofEnd (X : C) : CategoryTheory.End X →+* End R X where
  toFun f := CategoryTheory.End.of (ofHom R f.asHom)
  map_zero' := by apply CategoryTheory.End.ext; exact map_zero (ofHom R)
  map_one' := rfl
  map_add' f g := by apply CategoryTheory.End.ext; exact map_add (ofHom R) f.asHom g.asHom
  map_mul' f g := by
    apply CategoryTheory.End.ext
    change ofHom R (g.asHom ≫ f.asHom) = comp R X X X (ofHom R g.asHom) (ofHom R f.asHom)
    simp

@[simp] theorem ofEnd_apply (X : C) (f : CategoryTheory.End X) :
    ofEnd R X f = CategoryTheory.End.of ((1 : R) ⊗ₜ[ℤ] f.asHom) := rfl

section Lift

variable {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear R D]
  (F : C ⥤ D) [F.Additive]

variable (R) in
/-- Extend the map on ordinary morphisms by `R`-scalar multiplication. -/
def liftHom {X Y : C} : Hom R X Y →ₗ[R] (F.obj X ⟶ F.obj Y) :=
  TensorProduct.AlgebraTensorModule.lift
    ((LinearMap.id : R →ₗ[R] R).smulRight (F.mapLinearMap ℤ))

@[simp] theorem liftHom_tmul {X Y : C} (r : R) (f : X ⟶ Y) :
    liftHom R F (r ⊗ₜ[ℤ] f) = r • F.map f := rfl

@[simp] theorem liftHom_ofHom {X Y : C} (f : X ⟶ Y) :
    liftHom R F (ofHom R f) = F.map f := by
  simp

theorem liftHom_comp {X Y Z : C} (f : Hom R X Y) (g : Hom R Y Z) :
    liftHom R F (comp R X Y Z f g) = liftHom R F f ≫ liftHom R F g := by
  induction f using TensorProduct.inductionOn with
  | add f f' hf hf' => simp [hf, hf', Preadditive.add_comp]
  | tmul q f =>
    induction g using TensorProduct.inductionOn with
    | add g g' hg hg' => simp [hg, hg', Preadditive.comp_add]
    | tmul r g =>
      simp only [comp_tmul, liftHom_tmul, Functor.map_comp,
        Linear.smul_comp, Linear.comp_smul]
      rw [← mul_smul, mul_comm q r]

variable (R) in
/-- The extension of an additive functor to an `R`-linear category. -/
def lift : CoefficientExtension R C ⥤ D where
  obj X := F.obj X.obj
  map := liftHom R F
  map_id X := by
    change liftHom R F ((1 : R) ⊗ₜ[ℤ] 𝟙 X.obj) = 𝟙 (F.obj X.obj)
    simp
  map_comp := liftHom_comp F

instance : (lift R F).Additive where
  map_add {_X _Y f g} := (liftHom R F).map_add f g

instance : (lift R F).Linear R where
  map_smul {_X _Y} f r := (liftHom R F).map_smul r f

@[simp] theorem lift_map_tmul {X Y : C} (r : R) (f : X ⟶ Y) :
    (lift R F).map (r ⊗ₜ[ℤ] f : of X ⟶ of Y) = r • F.map f := rfl

variable (R) in
/-- Restricting the extension along the inclusion recovers the original functor. -/
def inclusionLiftIso : inclusion R ⋙ lift R F ≅ F :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y f
    change liftHom R F (ofHom R f) ≫ 𝟙 _ = 𝟙 _ ≫ F.map f
    simp)

variable (R) in
/-- The induced `R`-algebra map on actual endomorphism rings. -/
def liftEnd (X : C) : End R X →ₐ[R] CategoryTheory.End (F.obj X) where
  toFun f := CategoryTheory.End.of (liftHom R F f.asHom)
  map_zero' := by apply CategoryTheory.End.ext; exact map_zero (liftHom R F)
  map_one' := by apply CategoryTheory.End.ext; exact (lift R F).map_id (of X)
  map_add' f g := by apply CategoryTheory.End.ext; exact map_add (liftHom R F) f.asHom g.asHom
  map_mul' f g := by apply CategoryTheory.End.ext; exact liftHom_comp F g.asHom f.asHom
  commutes' r := by
    apply CategoryTheory.End.ext
    rw [algebraMap_eq]
    change liftHom R F (r ⊗ₜ[ℤ] 𝟙 X) = _
    rw [liftHom_tmul, F.map_id]
    rfl

@[simp] theorem liftEnd_ofEnd (X : C) (f : CategoryTheory.End X) :
    liftEnd R F X (ofEnd R X f) = CategoryTheory.End.of (F.map f.asHom) := by
  apply CategoryTheory.End.ext
  change liftHom R F (ofHom R f.asHom) = _
  simp

@[simp] theorem liftEnd_tmul (X : C) (r : R) (f : CategoryTheory.End X) :
    liftEnd R F X (CategoryTheory.End.of (r ⊗ₜ[ℤ] f.asHom)) =
      CategoryTheory.End.of (r • F.map f.asHom) := rfl

end Lift

section Extend

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]

variable (R) in
/-- The `R`-linear extension `r ⊗ x ↦ r ⊗ φ x` of an additive map of abelian groups. -/
def extendAddHom (φ : M →+ N) : R ⊗[ℤ] M →ₗ[R] R ⊗[ℤ] N where
  toFun := LinearMap.lTensor R φ.toIntLinearMap
  map_add' := map_add _
  map_smul' r x := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [smul_add, map_add, hx, hy, RingHom.id_apply]
    | tmul s m => simp [TensorProduct.smul_tmul']

@[simp] theorem extendAddHom_tmul (φ : M →+ N) (r : R) (m : M) :
    extendAddHom R φ (r ⊗ₜ[ℤ] m) = r ⊗ₜ[ℤ] φ m := rfl

end Extend

section ChangeOfCoefficients

variable {R' : Type} [CommRing R'] (φ : R →+* R')

/-- The map of morphism groups induced by a ring homomorphism of coefficients. -/
def changeHom (X Y : C) : Hom R X Y →ₗ[ℤ] Hom R' X Y :=
  LinearMap.rTensor (X ⟶ Y) φ.toAddMonoidHom.toIntLinearMap

@[simp] theorem changeHom_tmul {X Y : C} (r : R) (f : X ⟶ Y) :
    changeHom φ X Y (r ⊗ₜ[ℤ] f) = φ r ⊗ₜ[ℤ] f := rfl

@[simp] theorem changeHom_ofHom {X Y : C} (f : X ⟶ Y) :
    changeHom φ X Y (ofHom R f) = ofHom R' f := by
  simp

/-- Change of coefficients is semilinear along the ring homomorphism. -/
theorem changeHom_smul {X Y : C} (r : R) (f : Hom R X Y) :
    changeHom φ X Y (r • f) = φ r • changeHom φ X Y f := by
  induction f using TensorProduct.inductionOn with
  | add f f' hf hf' => simp only [smul_add, map_add, hf, hf']
  | tmul s f => simp [TensorProduct.smul_tmul']

@[simp] theorem changeHom_identity (X : C) :
    changeHom φ X X (identity R X) = identity R' X := by
  simp [identity]

theorem changeHom_comp {X Y Z : C} (f : Hom R X Y) (g : Hom R Y Z) :
    changeHom φ X Z (comp R X Y Z f g) =
      comp R' X Y Z (changeHom φ X Y f) (changeHom φ Y Z g) := by
  induction f using TensorProduct.inductionOn with
  | add f f' hf hf' => simp only [map_add, LinearMap.add_apply, hf, hf']
  | tmul q f =>
    induction g using TensorProduct.inductionOn with
    | add g g' hg hg' => simp only [map_add, hg, hg']
    | tmul r g => simp

/-- The additive functor changing the coefficients along a ring homomorphism. -/
def changeCoefficients : CoefficientExtension R C ⥤ CoefficientExtension R' C where
  obj X := of X.obj
  map {X Y} f := changeHom φ X.obj Y.obj f
  map_id X := changeHom_identity φ X.obj
  map_comp f g := changeHom_comp φ f g

instance : (changeCoefficients (C := C) φ).Additive where
  map_add {_X _Y f g} := map_add (changeHom φ _ _) f g

/-- The change of coefficients commutes with the two inclusions. -/
def inclusionChangeIso :
    inclusion R ⋙ changeCoefficients (C := C) φ ≅ inclusion R' :=
  NatIso.ofComponents (fun X => Iso.refl (of (R := R') X)) (by
    intro X Y f
    change (changeHom φ X Y (ofHom R f) : of (R := R') X ⟶ of (R := R') Y) ≫
        𝟙 (of (R := R') Y) =
      𝟙 (of (R := R') X) ≫ (ofHom R' f : of (R := R') X ⟶ of (R := R') Y)
    rw [Category.comp_id, Category.id_comp]
    simp)

/-- The induced unital ring map on actual endomorphism rings. -/
def changeEnd (X : C) : End R X →+* End R' X where
  toFun f := CategoryTheory.End.of (changeHom φ X X f.asHom)
  map_zero' := by apply CategoryTheory.End.ext; exact map_zero (changeHom φ X X)
  map_one' := by apply CategoryTheory.End.ext; exact changeHom_identity φ X
  map_add' f g := by
    apply CategoryTheory.End.ext; exact map_add (changeHom φ X X) f.asHom g.asHom
  map_mul' f g := by apply CategoryTheory.End.ext; exact changeHom_comp φ g.asHom f.asHom

@[simp] theorem changeEnd_ofEnd (X : C) (f : CategoryTheory.End X) :
    changeEnd φ X (ofEnd R X f) = ofEnd R' X f := by
  apply CategoryTheory.End.ext
  change changeHom φ X X (ofHom R f.asHom) = ofHom R' f.asHom
  simp

end ChangeOfCoefficients

section Rationalization

variable (φ : R →+* ℚ)

/-- The comparison functor to the rationalization along a ring homomorphism to `ℚ`.
Both morphism groups are tensor products over `ℤ` with the same ordinary group. -/
def toRationalization : CoefficientExtension R C ⥤ Langlands.Rationalization C where
  obj X := Langlands.Rationalization.of X.obj
  map {X Y} f := changeHom φ X.obj Y.obj f
  map_id X := changeHom_identity φ X.obj
  map_comp f g := changeHom_comp φ f g

instance : (toRationalization (C := C) φ).Additive where
  map_add {_X _Y f g} := map_add (changeHom φ _ _) f g

@[simp] theorem toRationalization_map_tmul {X Y : C} (r : R) (f : X ⟶ Y) :
    (toRationalization φ).map (r ⊗ₜ[ℤ] f : of X ⟶ of Y) = φ r ⊗ₜ[ℤ] f := rfl

/-- The comparison commutes with the two inclusions of `C`. -/
def inclusionToRationalizationIso :
    inclusion R ⋙ toRationalization (C := C) φ ≅ Langlands.Rationalization.inclusion :=
  NatIso.ofComponents (fun X => Iso.refl (Langlands.Rationalization.of X)) (by
    intro X Y f
    change (changeHom φ X Y (ofHom R f) :
        Langlands.Rationalization.of X ⟶ Langlands.Rationalization.of Y) ≫
          𝟙 (Langlands.Rationalization.of Y) =
      𝟙 (Langlands.Rationalization.of X) ≫ (Langlands.Rationalization.ofHom f :
        Langlands.Rationalization.of X ⟶ Langlands.Rationalization.of Y)
    rw [Category.comp_id, Category.id_comp]
    simp)

/-- The induced unital ring map to the actual rational endomorphism ring. -/
def toRationalEnd (X : C) : End R X →+* Langlands.Rationalization.End X where
  toFun f := CategoryTheory.End.of (changeHom φ X X f.asHom)
  map_zero' := by apply CategoryTheory.End.ext; exact map_zero (changeHom φ X X)
  map_one' := by apply CategoryTheory.End.ext; exact changeHom_identity φ X
  map_add' f g := by
    apply CategoryTheory.End.ext; exact map_add (changeHom φ X X) f.asHom g.asHom
  map_mul' f g := by apply CategoryTheory.End.ext; exact changeHom_comp φ g.asHom f.asHom

@[simp] theorem toRationalEnd_ofEnd (X : C) (f : CategoryTheory.End X) :
    toRationalEnd φ X (ofEnd R X f) = Langlands.Rationalization.ofEnd X f := by
  apply CategoryTheory.End.ext
  change changeHom φ X X (ofHom R f.asHom) = Langlands.Rationalization.ofHom f.asHom
  simp

end Rationalization

end CoefficientExtension
end Langlands
