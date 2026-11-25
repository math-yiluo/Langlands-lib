/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Module.ULift
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution

/-!

# The tensor product of abelian groups and rings as monoid objects of `Ab`

Mathlib equips `Ab = AddCommGrpCat` only with its cartesian monoidal structure. The ring
objects of `WeilConjectures.CategoryTheory.RingObjects` need the monoidal structure given by
the tensor product `M ⊗ N = M ⊗[ℤ] N` of abelian groups, with unit `ℤ`: for that structure the
monoid objects of `Ab` are exactly the rings, and the monoid objects of the categories of
abelian presheaves and abelian sheaves on a site are the presheaves and sheaves of rings.

Mathlib's `ModuleCat.{u} ℤ` carries this structure only for `u = 0`, since `ModuleCat.{u} R`
is monoidal only for `R : Type u`, the unit having to be an object. Here the unit is `ℤ`
lifted to `Type u`, and the construction of mathlib (`ModuleCat.MonoidalCategory`) is
repeated for `Ab.{u}` with `ℤ`-linear maps.

## Main definitions

* `AddCommGrpCat.monoidalCategory`: the tensor product monoidal structure on `Ab.{u}`, with
  `M ⊗ N = M ⊗[ℤ] N` and unit `ULift ℤ`.
* `AddCommGrpCat.symmetricCategory`, `AddCommGrpCat.monoidalPreadditive`: it is symmetric and
  additive in each variable.
* `AddCommGrpCat.monoidalClosed`: it is closed, with internal hom `Hom(M, N) = (M ⟶ N)`.
  Closedness is what makes the localized monoidal structure on sheaves available
  (`CategoryTheory.GrothendieckTopology.W.monoidal`).
* `AddCommGrpCat.ringMonObj`: a ring `R` is a monoid object of `Ab`, with unit the map
  `ℤ ⟶ R` and multiplication the `ℤ`-bilinear map `R ⊗ R ⟶ R`. A ring homomorphism is a
  morphism of monoid objects (`AddCommGrpCat.isMonHom_ofHom_ringHom`), and `R` is a
  commutative monoid object when it is a commutative ring
  (`AddCommGrpCat.isCommMonObj_of_commRing`). These are the counterparts for `Ab` of
  mathlib's `ModuleCat.monModuleEquivalenceAlgebra` (`Mon (ModuleCat R) ≌ AlgCat R`).

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Opposite TensorProduct

namespace AddCommGrpCat

/-- Two morphisms of abelian groups agree when the underlying `ℤ`-linear maps agree. -/
lemma hom_ext_toIntLinearMap {M N : Ab.{u}} {f g : M ⟶ N}
    (h : f.hom.toIntLinearMap = g.hom.toIntLinearMap) : f = g :=
  hom_ext (AddMonoidHom.toIntLinearMap_injective h)

namespace MonoidalCategory

/-- (implementation) the tensor product of abelian groups -/
def tensorObj (M N : Ab.{u}) : Ab.{u} :=
  of (M ⊗[ℤ] N)

/-- (implementation) the tensor product of morphisms of abelian groups -/
def tensorHom {M N M' N' : Ab.{u}} (f : M ⟶ N) (g : M' ⟶ N') :
    tensorObj M M' ⟶ tensorObj N N' :=
  ofHom (TensorProduct.map f.hom.toIntLinearMap g.hom.toIntLinearMap).toAddMonoidHom

/-- (implementation) left whiskering for abelian groups -/
def whiskerLeft (M : Ab.{u}) {N₁ N₂ : Ab.{u}} (f : N₁ ⟶ N₂) :
    tensorObj M N₁ ⟶ tensorObj M N₂ :=
  ofHom (f.hom.toIntLinearMap.lTensor M).toAddMonoidHom

/-- (implementation) right whiskering for abelian groups -/
def whiskerRight {M₁ M₂ : Ab.{u}} (f : M₁ ⟶ M₂) (N : Ab.{u}) :
    tensorObj M₁ N ⟶ tensorObj M₂ N :=
  ofHom (f.hom.toIntLinearMap.rTensor N).toAddMonoidHom

/-- (implementation) the unit `ℤ` of the tensor product, lifted to `Type u` -/
def tensorUnit : Ab.{u} :=
  of (ULift.{u} ℤ)

/-- (implementation) the associator for abelian groups -/
def associator (M N K : Ab.{u}) : tensorObj (tensorObj M N) K ≅ tensorObj M (tensorObj N K) :=
  (TensorProduct.assoc ℤ M N K).toAddEquiv.toAddCommGrpIso

/-- (implementation) the left unitor for abelian groups -/
def leftUnitor (M : Ab.{u}) : tensorObj tensorUnit M ≅ M :=
  ((TensorProduct.congr ULift.moduleEquiv (LinearEquiv.refl ℤ M)).trans
    (TensorProduct.lid ℤ M)).toAddEquiv.toAddCommGrpIso

/-- (implementation) the right unitor for abelian groups -/
def rightUnitor (M : Ab.{u}) : tensorObj M tensorUnit ≅ M :=
  ((TensorProduct.congr (LinearEquiv.refl ℤ M) ULift.moduleEquiv).trans
    (TensorProduct.rid ℤ M)).toAddEquiv.toAddCommGrpIso

@[simps -isSimp]
instance instMonoidalCategoryStruct : MonoidalCategoryStruct Ab.{u} where
  tensorObj := tensorObj
  whiskerLeft := whiskerLeft
  whiskerRight := whiskerRight
  tensorHom := tensorHom
  tensorUnit := tensorUnit
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor

theorem id_tensorHom_id (M N : Ab.{u}) : tensorHom (𝟙 M) (𝟙 N) = 𝟙 (tensorObj M N) :=
  hom_ext_toIntLinearMap (TensorProduct.ext' fun _ _ ↦ rfl)

theorem tensorHom_comp_tensorHom {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : Ab.{u}} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
    tensorHom f₁ f₂ ≫ tensorHom g₁ g₂ = tensorHom (f₁ ≫ g₁) (f₂ ≫ g₂) :=
  hom_ext_toIntLinearMap (TensorProduct.ext' fun _ _ ↦ rfl)

theorem associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Ab.{u}} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (f₃ : X₃ ⟶ Y₃) :
    tensorHom (tensorHom f₁ f₂) f₃ ≫ (associator Y₁ Y₂ Y₃).hom =
      (associator X₁ X₂ X₃).hom ≫ tensorHom f₁ (tensorHom f₂ f₃) :=
  hom_ext_toIntLinearMap (TensorProduct.ext_threefold fun _ _ _ ↦ rfl)

theorem pentagon (W X Y Z : Ab.{u}) :
    whiskerRight (associator W X Y).hom Z ≫
        (associator W (tensorObj X Y) Z).hom ≫ whiskerLeft W (associator X Y Z).hom =
      (associator (tensorObj W X) Y Z).hom ≫ (associator W X (tensorObj Y Z)).hom :=
  hom_ext_toIntLinearMap (TensorProduct.ext_fourfold fun _ _ _ _ ↦ rfl)

theorem leftUnitor_naturality {M N : Ab.{u}} (f : M ⟶ N) :
    tensorHom (𝟙 tensorUnit) f ≫ (leftUnitor N).hom = (leftUnitor M).hom ≫ f :=
  hom_ext_toIntLinearMap (TensorProduct.ext' fun n m ↦
    (map_zsmul f.hom n.down m).symm)

theorem rightUnitor_naturality {M N : Ab.{u}} (f : M ⟶ N) :
    tensorHom f (𝟙 tensorUnit) ≫ (rightUnitor N).hom = (rightUnitor M).hom ≫ f :=
  hom_ext_toIntLinearMap (TensorProduct.ext' fun m n ↦
    (map_zsmul f.hom n.down m).symm)

theorem triangle (M N : Ab.{u}) :
    (associator M tensorUnit N).hom ≫ tensorHom (𝟙 M) (leftUnitor N).hom =
      tensorHom (rightUnitor M).hom (𝟙 N) :=
  hom_ext_toIntLinearMap (TensorProduct.ext_threefold fun m n k ↦
    ((TensorProduct.tmul_smul n.down m k).trans (TensorProduct.smul_tmul' n.down m k)))

end MonoidalCategory

open MonoidalCategory in
/-- The monoidal structure on `Ab` given by the tensor product of abelian groups, with unit
`ℤ`. -/
instance monoidalCategory : MonoidalCategory Ab.{u} := MonoidalCategory.ofTensorHom
  (id_tensorHom_id := id_tensorHom_id)
  (tensorHom_comp_tensorHom := tensorHom_comp_tensorHom)
  (associator_naturality := associator_naturality)
  (leftUnitor_naturality := leftUnitor_naturality)
  (rightUnitor_naturality := rightUnitor_naturality)
  (pentagon := pentagon)
  (triangle := triangle)

namespace MonoidalCategory

@[simp]
theorem tensorHom_tmul {K L M N : Ab.{u}} (f : K ⟶ L) (g : M ⟶ N) (k : K) (m : M) :
    (f ⊗ₘ g).hom (k ⊗ₜ[ℤ] m) = f.hom k ⊗ₜ[ℤ] g.hom m :=
  rfl

@[simp]
theorem whiskerLeft_tmul (L : Ab.{u}) {M N : Ab.{u}} (f : M ⟶ N) (l : L) (m : M) :
    (L ◁ f).hom (l ⊗ₜ[ℤ] m) = l ⊗ₜ[ℤ] f.hom m :=
  rfl

@[simp]
theorem whiskerRight_tmul {L M : Ab.{u}} (f : L ⟶ M) (N : Ab.{u}) (l : L) (n : N) :
    (f ▷ N).hom (l ⊗ₜ[ℤ] n) = f.hom l ⊗ₜ[ℤ] n :=
  rfl

@[simp]
theorem associator_hom_tmul (M N K : Ab.{u}) (m : M) (n : N) (k : K) :
    (α_ M N K).hom.hom ((m ⊗ₜ[ℤ] n) ⊗ₜ[ℤ] k) = m ⊗ₜ[ℤ] (n ⊗ₜ[ℤ] k) :=
  rfl

@[simp]
theorem associator_inv_tmul (M N K : Ab.{u}) (m : M) (n : N) (k : K) :
    (α_ M N K).inv.hom (m ⊗ₜ[ℤ] (n ⊗ₜ[ℤ] k)) = (m ⊗ₜ[ℤ] n) ⊗ₜ[ℤ] k :=
  rfl

@[simp]
theorem leftUnitor_hom_tmul (M : Ab.{u}) (n : ULift.{u} ℤ) (m : M) :
    (λ_ M).hom.hom (n ⊗ₜ[ℤ] m) = n.down • m :=
  rfl

@[simp]
theorem rightUnitor_hom_tmul (M : Ab.{u}) (m : M) (n : ULift.{u} ℤ) :
    (ρ_ M).hom.hom (m ⊗ₜ[ℤ] n) = n.down • m :=
  rfl

/-- (implementation) the braiding for abelian groups -/
def braiding (M N : Ab.{u}) : M ⊗ N ≅ N ⊗ M :=
  (TensorProduct.comm ℤ M N).toAddEquiv.toAddCommGrpIso

@[simp]
theorem braiding_hom_tmul (M N : Ab.{u}) (m : M) (n : N) :
    (braiding M N).hom.hom (m ⊗ₜ[ℤ] n) = n ⊗ₜ[ℤ] m :=
  rfl

end MonoidalCategory

open MonoidalCategory in
/-- The tensor product of abelian groups is symmetric. -/
instance symmetricCategory : SymmetricCategory Ab.{u} where
  braiding := braiding
  braiding_naturality_left _ _ := hom_ext_toIntLinearMap (TensorProduct.ext' fun _ _ ↦ rfl)
  braiding_naturality_right _ _ _ _ := hom_ext_toIntLinearMap (TensorProduct.ext' fun _ _ ↦ rfl)
  hexagon_forward _ _ _ := hom_ext_toIntLinearMap (TensorProduct.ext_threefold fun _ _ _ ↦ rfl)
  hexagon_reverse _ _ _ := hom_ext_toIntLinearMap (TensorProduct.ext_threefold' fun _ _ _ ↦ rfl)
  symmetry _ _ := hom_ext_toIntLinearMap (TensorProduct.ext' fun _ _ ↦ rfl)

/-- The tensor product of abelian groups is additive in each variable. -/
instance monoidalPreadditive : MonoidalPreadditive Ab.{u} where
  whiskerLeft_zero {_ _ Z} := hom_ext_toIntLinearMap (TensorProduct.ext' fun x _ ↦
    (TensorProduct.tmul_zero (R := ℤ) (N := Z) x :))
  zero_whiskerRight {_ _ Z} := hom_ext_toIntLinearMap (TensorProduct.ext' fun _ y ↦
    (TensorProduct.zero_tmul (R := ℤ) (M := Z) y :))
  whiskerLeft_add f g := hom_ext_toIntLinearMap (TensorProduct.ext' fun x y ↦
    (TensorProduct.tmul_add (R := ℤ) x (f.hom y) (g.hom y) :))
  add_whiskerRight f g := hom_ext_toIntLinearMap (TensorProduct.ext' fun x y ↦
    (TensorProduct.add_tmul (R := ℤ) (f.hom x) (g.hom x) y :))

/-- (implementation) the bijection `(M ⊗ N ⟶ P) ≃ (N ⟶ Hom(M, P))` exhibiting `Hom(M, -)` as
right adjoint to `M ⊗ -` -/
def monoidalClosedHomEquiv (M N P : Ab.{u}) :
    ((tensorLeft M).obj N ⟶ P) ≃ (N ⟶ (preadditiveCoyoneda.obj (op M)).obj P) where
  toFun f := ofHom
    { toFun n := ofHom (AddMonoidHom.mk' (fun m ↦ f.hom (m ⊗ₜ[ℤ] n)) fun _ _ ↦
        (congrArg f.hom (add_tmul _ _ n)).trans (map_add f.hom _ _))
      map_zero' := hom_ext (AddMonoidHom.ext fun m ↦
        (congrArg f.hom (tmul_zero N m)).trans (map_zero f.hom))
      map_add' _ _ := hom_ext (AddMonoidHom.ext fun m ↦
        (congrArg f.hom (tmul_add m _ _)).trans (map_add f.hom _ _)) }
  invFun g := ofHom (TensorProduct.lift (LinearMap.mk₂ ℤ (fun m n ↦ (g.hom n).hom m)
    (fun _ _ _ ↦ by simp) (fun _ _ _ ↦ by simp) (fun _ _ _ ↦ by rw [map_add]; rfl)
    (fun _ _ _ ↦ by rw [map_zsmul]; rfl))).toAddMonoidHom
  left_inv _ := hom_ext_toIntLinearMap (TensorProduct.ext' fun _ _ ↦ rfl)
  right_inv _ := by ext; rfl

/-- The tensor product of abelian groups is closed: the internal hom `Hom(M, N)` is the group of
morphisms `M ⟶ N` with its pointwise group structure. -/
instance monoidalClosed : MonoidalClosed Ab.{u} where
  closed M :=
    { rightAdj := preadditiveCoyoneda.obj (op M)
      adj := Adjunction.mkOfHomEquiv
        { homEquiv := monoidalClosedHomEquiv M
          homEquiv_naturality_left_symm _ _ :=
            hom_ext_toIntLinearMap (TensorProduct.ext' fun _ _ ↦ rfl)
          homEquiv_naturality_right _ _ := rfl } }

theorem ihom_obj (M N : Ab.{u}) : (ihom M).obj N = of (M ⟶ N) :=
  rfl

theorem ihom_map_apply {M N P : Ab.{u}} (f : N ⟶ P) (g : M ⟶ N) :
    ((ihom M).map f).hom g = g ≫ f :=
  rfl


@[simp]
theorem monoidalClosed_curry {M N P : Ab.{u}} (f : M ⊗ N ⟶ P) (m : M) (n : N) :
    ((MonoidalClosed.curry f).hom n).hom m = f.hom (m ⊗ₜ[ℤ] n) :=
  rfl

@[simp]
theorem monoidalClosed_uncurry {M N P : Ab.{u}} (f : N ⟶ (ihom M).obj P) (m : M) (n : N) :
    (MonoidalClosed.uncurry f).hom (m ⊗ₜ[ℤ] n) = (f.hom n).hom m :=
  rfl

/-- The unit `ℤ` of the tensor product is a separator of `Ab`: a morphism out of an abelian
group `M` is determined by its composites with the maps `ℤ ⟶ M`, `n ↦ n • m`. -/
theorem isSeparator_tensorUnit : IsSeparator (𝟙_ Ab.{u}) := by
  rw [isSeparator_def]
  intro M N f g h
  ext m
  simpa using congrArg (fun k ↦ k.hom (ULift.up (1 : ℤ)))
    (h (ofHom (AddMonoidHom.mk' (fun n : ULift.{u} ℤ ↦ n.down • m) fun _ _ ↦ add_smul _ _ _)))

/-- `Ab` admits functorial flat resolutions: the unit `ℤ` is a flat separator. -/
instance : CategoryTheory.Abelian.HasFunctorialFlatResolution Ab.{u} :=
  CategoryTheory.Abelian.hasFunctorialFlatResolution_of_flat_separator _
    isSeparator_tensorUnit (ObjectProperty.prop_unit _)

section Ring

variable (R : Type u) [Ring R]

/-- A ring `R` is a monoid object of `Ab`: its unit is the map `ℤ ⟶ R` and its multiplication
is the `ℤ`-bilinear map `R ⊗ R ⟶ R` induced by the multiplication. -/
noncomputable instance ringMonObj : MonObj (of R) where
  one := ofHom ((Int.castAddHom R).comp
    (ULift.moduleEquiv (R := ℤ) (M := ℤ)).toLinearMap.toAddMonoidHom)
  mul := ofHom (LinearMap.mul' ℤ R).toAddMonoidHom
  one_mul := hom_ext_toIntLinearMap (TensorProduct.ext' fun (n : ULift.{u} ℤ) (r : R) ↦
    ((zsmul_eq_mul r n.down).symm :))
  mul_one := hom_ext_toIntLinearMap (TensorProduct.ext' fun (r : R) (n : ULift.{u} ℤ) ↦
    ((zsmul_eq_mul' r n.down).symm :))
  mul_assoc := hom_ext_toIntLinearMap (TensorProduct.ext_threefold fun a b c ↦
    (mul_assoc a b c :))

lemma ringMonObj_one_apply (n : ULift.{u} ℤ) :
    (η[of R] : of (ULift.{u} ℤ) ⟶ of R).hom n = n.down :=
  rfl

lemma ringMonObj_mul_tmul (a b : R) :
    (μ[of R] : of (R ⊗[ℤ] R) ⟶ of R).hom (a ⊗ₜ[ℤ] b) = a * b :=
  rfl


variable {R} {S : Type u} [Ring S]

/-- A ring homomorphism is a morphism of monoid objects of `Ab`. -/
instance isMonHom_ofHom_ringHom (f : R →+* S) : IsMonHom (ofHom f.toAddMonoidHom) where
  one_hom := hom_ext (AddMonoidHom.ext fun n ↦ map_intCast f n.down)
  mul_hom := hom_ext_toIntLinearMap (TensorProduct.ext' fun a b ↦ (map_mul f a b :))

/-- A ring with commutative multiplication is a commutative monoid object of `Ab`. -/
lemma isCommMonObj_of_mul_comm (R : Type u) [Ring R] (h : ∀ a b : R, a * b = b * a) :
    IsCommMonObj (of R) where
  mul_comm := hom_ext_toIntLinearMap (TensorProduct.ext' fun a b ↦ (h b a :))

/-- A commutative ring is a commutative monoid object of `Ab`. -/
instance isCommMonObj_of_commRing (R : Type u) [CommRing R] : IsCommMonObj (of R) :=
  isCommMonObj_of_mul_comm R mul_comm

end Ring

end AddCommGrpCat
