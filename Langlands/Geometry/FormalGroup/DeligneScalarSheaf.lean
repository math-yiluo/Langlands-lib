import Langlands.Geometry.FormalGroup.DeligneRationalSheaf

/-! # Actual coefficient scalar maps and the rational Pi relation -/

noncomputable section

universe u

namespace Langlands.DeligneFormalSpace

open CategoryTheory TopologicalSpace
open scoped ChangeOfRings

variable {R : Type u} [CommRing R] {X : TopCat.{u}}

/-- Pointwise coefficient multiplication on an actual module presheaf. -/
def coefficientPresheafScale (a : R) (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} R) : P ⟶ P where
  app U := ModuleCat.ofHom (LinearMap.lsmul R (P.obj U) a)
  naturality {U V} f := by
    ext x
    exact ((P.map f).hom.map_smul a x).symm

/-- Actual coefficient multiplication on a module sheaf. -/
def coefficientSheafScale (a : R) (M : X.Sheaf (ModuleCat.{u} R)) : M ⟶ M where
  hom := coefficientPresheafScale a M.obj

/-- Every module-presheaf map commutes with coefficient multiplication. -/
@[reassoc]
theorem coefficientPresheafScale_naturality (a : R)
    {P Q : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} R} (f : P ⟶ Q) :
    coefficientPresheafScale a P ≫ f = f ≫ coefficientPresheafScale a Q := by
  apply NatTrans.ext
  funext U
  ext x
  exact (f.app U).hom.map_smul a x

/-- Every actual module-sheaf map commutes with coefficient multiplication. -/
@[reassoc]
theorem coefficientSheafScale_naturality (a : R)
    {M N : X.Sheaf (ModuleCat.{u} R)} (f : M ⟶ N) :
    coefficientSheafScale a M ≫ f = f ≫ coefficientSheafScale a N := by
  apply Sheaf.hom_ext
  exact coefficientPresheafScale_naturality a f.hom

@[simp]
theorem coefficientPresheafScale_one (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} R) :
    coefficientPresheafScale (1 : R) P = 𝟙 P := by
  apply NatTrans.ext
  funext U
  ext x
  exact one_smul R x

/-- Composition is actual multiplication of coefficients. -/
theorem coefficientPresheafScale_mul (a b : R)
    (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} R) :
    coefficientPresheafScale (a * b) P =
      coefficientPresheafScale a P ≫ coefficientPresheafScale b P := by
  apply NatTrans.ext
  funext U
  ext x
  exact (mul_smul a b x).trans (smul_comm a b x)

@[simp]
theorem coefficientSheafScale_one (M : X.Sheaf (ModuleCat.{u} R)) :
    coefficientSheafScale (1 : R) M = 𝟙 M := by
  apply Sheaf.hom_ext
  exact coefficientPresheafScale_one M.obj

/-- Composition is actual multiplication of coefficients on sheaves. -/
theorem coefficientSheafScale_mul (a b : R) (M : X.Sheaf (ModuleCat.{u} R)) :
    coefficientSheafScale (a * b) M =
      coefficientSheafScale a M ≫ coefficientSheafScale b M := by
  apply Sheaf.hom_ext
  exact coefficientPresheafScale_mul a b M.obj

/-- An integral coefficient unit gives a genuine automorphism of the sheaf. -/
def coefficientSheafUnitIso (a : Rˣ) (M : X.Sheaf (ModuleCat.{u} R)) : M ≅ M where
  hom := coefficientSheafScale (a : R) M
  inv := coefficientSheafScale ((a⁻¹ : Rˣ) : R) M
  hom_inv_id := by rw [← coefficientSheafScale_mul, Units.mul_inv, coefficientSheafScale_one]
  inv_hom_id := by rw [← coefficientSheafScale_mul, Units.inv_mul, coefficientSheafScale_one]

/-- Sheafification carries a pointwise scalar map to actual scalar multiplication. -/
theorem sheafification_coefficientScale (a : R)
    (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} R) :
    (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)).map
        (coefficientPresheafScale a P) =
      coefficientSheafScale a
        ((presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)).obj P) := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (Opens.grothendieckTopology X) _ _
    (((presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)).obj P).property)
  exact (toSheafify_naturality (Opens.grothendieckTopology X)
    (coefficientPresheafScale a P)).symm.trans
      (coefficientPresheafScale_naturality a
        (toSheafify (Opens.grothendieckTopology X) P))

variable {O : Type u} [CommRing O] (F : Type u) [Field F] [Algebra O F]

set_option backward.isDefEq.respectTransparency false in
/-- Scalar extension sends an integral scalar to its actual field image. -/
theorem rationalPresheafFunctor_coefficientScale (a : O)
    (M : X.Sheaf (ModuleCat.{u} O)) :
    (rationalPresheafFunctor F X).map (coefficientSheafScale a M) =
      coefficientPresheafScale (algebraMap O F a) ((rationalPresheafFunctor F X).obj M) := by
  apply NatTrans.ext
  funext U
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  change (1 : F) ⊗ₜ[O, algebraMap O F] (a • m) =
    algebraMap O F a • ((1 : F) ⊗ₜ[O, algebraMap O F] m)
  exact ((ModuleCat.extendRestrictScalarsAdj (algebraMap O F)).unit.app
    (M.obj.obj U)).hom.map_smul a m

/-- Rationalization sends an integral scalar to the actual scalar sheaf map. -/
theorem rationalSheafFunctor_coefficientScale (a : O)
    (M : X.Sheaf (ModuleCat.{u} O)) :
    (rationalSheafFunctor F X).map (coefficientSheafScale a M) =
      coefficientSheafScale (algebraMap O F a) ((rationalSheafFunctor F X).obj M) := by
  change (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} F)).map
    ((rationalPresheafFunctor F X).map (coefficientSheafScale a M)) = _
  rw [rationalPresheafFunctor_coefficientScale, sheafification_coefficientScale]
  rfl

variable (d : ℕ) (π : O)

/-- The actual rational Pi presheaf has d-th power equal to pointwise scalar pi. -/
theorem rationalPiPresheaf_relation_coefficientScale
    (M : X.Sheaf (ModuleCat.{u} (PiAlgebra d π))) :
    rationalPiPresheaf F X d π M ^ d =
      coefficientPresheafScale (algebraMap O F π)
        ((rationalPresheafFunctor F X).obj (latticeScalarSheaf d π X M)) := by
  rw [rationalPiPresheaf_relation]
  rfl

variable [NeZero d]

/-- The forward map of the actual rational Pi automorphism has d-th power scalar pi. -/
theorem rationalPiAut_hom_pow
    (M : X.Sheaf (ModuleCat.{u} (PiAlgebra d π))) (hπ : algebraMap O F π ≠ 0) :
    (show End (rationalLattice F X d π M) from
      (rationalPiAut F X d π M hπ).hom) ^ d =
      coefficientSheafScale (algebraMap O F π) (rationalLattice F X d π M) := by
  let A := presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} F)
  have h : (rationalPiAut F X d π M hπ).hom = A.map (rationalPiPresheaf F X d π M) :=
    rationalPiAut_hom F X d π M hπ
  rw [h]
  change (A.mapEnd _ (rationalPiPresheaf F X d π M)) ^ d = _
  rw [← map_pow, rationalPiPresheaf_relation_coefficientScale]
  exact sheafification_coefficientScale _ _

/-- The actual d-th power of rational Pi is the genuine scalar-pi automorphism. -/
theorem rationalPiAut_pow
    (M : X.Sheaf (ModuleCat.{u} (PiAlgebra d π))) (hπ : algebraMap O F π ≠ 0) :
    rationalPiAut F X d π M hπ ^ d =
      coefficientSheafUnitIso (Units.mk0 (algebraMap O F π) hπ)
        (rationalLattice F X d π M) := by
  apply Aut.ext
  change Aut.toEnd _ (rationalPiAut F X d π M hπ ^ d) = _
  rw [map_pow]
  exact rationalPiAut_hom_pow F d π M hπ

end Langlands.DeligneFormalSpace
