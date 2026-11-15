import Langlands.Geometry.FormalGroup.DeligneScalarSheaf
import Langlands.Geometry.FormalGroup.DeligneValuedReframe

/-! # Actual integral scalar isomorphisms of Deligne's four data -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.DeligneFormalSpace

open CategoryTheory _root_.AlgebraicGeometry TopologicalSpace

variable {O : Type u} [CommRing O] {F : Type u} [Field F] [Algebra O F]
  {d : ℕ} {π : O} {X : TopCat.{u}}

/-- The actual scalar subgroup homomorphism into the general linear group. -/
def scalarReframeHom (d : ℕ) (F : Type u) [Field F] :
    Fˣ →* ((Fin d → F) ≃ₗ[F] (Fin d → F)) where
  toFun a := LinearEquiv.smulOfUnit a
  map_one' := by
    apply LinearEquiv.ext
    intro v
    exact one_smul F v
  map_mul' a b := by
    apply LinearEquiv.ext
    intro v
    exact mul_smul (a : F) (b : F) v

/-- The constant sheaf carries a scalar linear automorphism to actual scalar multiplication. -/
theorem constantSheaf_scalarReframeHom (a : Fˣ) :
    (constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} F)).map
        (scalarReframeHom d F a).toModuleIso.hom =
      coefficientSheafScale (a : F)
        ((constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} F)).obj
          (ModuleCat.of F (Fin d → F))) := by
  change (presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} F)).map
    (coefficientPresheafScale (a : F)
      ((Functor.const (Opens X)ᵒᵖ).obj (ModuleCat.of F (Fin d → F)))) = _
  exact sheafification_coefficientScale _ _

/-- Forgetting Pi-algebra scalars carries actual O-coefficient multiplication to itself. -/
theorem latticeScalarFunctor_coefficientScale (a : O)
    (M : X.Sheaf (ModuleCat.{u} (PiAlgebra d π))) :
    (latticeScalarFunctor d π X).map
      (coefficientSheafScale (algebraMap O (PiAlgebra d π) a) M) =
        coefficientSheafScale a (latticeScalarSheaf d π X M) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  ext x
  rfl

variable [NeZero d]

namespace LatticePiSheaf

/-- Scalar multiplication preserves every actual homogeneous lattice component. -/
def coefficientScale (a : O) (M : LatticePiSheaf d π X) : M ⟶ M where
  total := coefficientSheafScale (algebraMap O (PiAlgebra d π) a) M.sheaf
  component i := coefficientSheafScale a (M.component i)
  inclusion i := by
    rw [latticeScalarFunctor_coefficientScale]
    exact coefficientSheafScale_naturality a (M.inclusion i)

/-- An integral unit acts by a genuine homogeneous lattice isomorphism. -/
def coefficientUnitIso (a : Oˣ) (M : LatticePiSheaf d π X) : M ≅ M where
  hom := coefficientScale (a : O) M
  inv := coefficientScale ((a⁻¹ : Oˣ) : O) M
  hom_inv_id := Hom.ext_total (by
    change coefficientSheafScale _ _ ≫ coefficientSheafScale _ _ = _
    rw [← coefficientSheafScale_mul, ← map_mul, Units.mul_inv, map_one,
      coefficientSheafScale_one]
    rfl)
  inv_hom_id := Hom.ext_total (by
    change coefficientSheafScale _ _ ≫ coefficientSheafScale _ _ = _
    rw [← coefficientSheafScale_mul, ← map_mul, Units.inv_mul, map_one,
      coefficientSheafScale_one]
    rfl)

end LatticePiSheaf

variable {S : Scheme.{u}} {φ : O →+* Γ(S, ⊤)}

/-- Forgetting structural scalars sends actual multiplication by phi(a) to multiplication by a. -/
theorem structuralOSheafFunctor_structuralScalarEnd (a : O) (M : S.Modules) :
    (structuralOSheafFunctor S φ).map (structuralScalarEnd M (φ a)) =
      coefficientSheafScale a ((structuralOSheafFunctor S φ).obj M) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  ext x
  rfl

namespace GradedPiSheaf

variable {a : Γ(S, ⊤)}

/-- An actual structural scalar preserves the Pi operator and homogeneous subsheaves. -/
def structuralScale (b : Γ(S, ⊤))
    (M : GradedPiSheaf d S.sheaf (schemeScalar S a)) : M ⟶ M where
  val := {
    val := structuralScalarEnd M.module b
    comm := by
      apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro U
      ext x
      exact ((M.pi.val.app U).hom.map_smul ((schemeScalar S b).val U) x).symm }
  homogeneous U i x hx :=
    ((M.component i).toSubmodule.obj U).smul_mem ((schemeScalar S b).val U) hx

/-- The actual structural unit and its inverse give a homogeneous Pi-sheaf isomorphism. -/
def structuralUnitIso (b : Γ(S, ⊤)ˣ)
    (M : GradedPiSheaf d S.sheaf (schemeScalar S a)) : M ≅ M where
  hom := structuralScale (b : Γ(S, ⊤)) M
  inv := structuralScale ((b⁻¹ : Γ(S, ⊤)ˣ) : Γ(S, ⊤)) M
  hom_inv_id := Hom.ext (PiSheaf.Hom.ext (by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext x
    change (schemeScalar S ((b⁻¹ : Γ(S, ⊤)ˣ) : Γ(S, ⊤))).val U •
      ((schemeScalar S (b : Γ(S, ⊤))).val U • x) = x
    rw [← mul_smul]
    change ((S.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op).hom
      ((b⁻¹ : Γ(S, ⊤)ˣ) : Γ(S, ⊤)) *
      (S.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op).hom (b : Γ(S, ⊤))) • x = x
    rw [← map_mul, Units.inv_mul, map_one, one_smul]))
  inv_hom_id := Hom.ext (PiSheaf.Hom.ext (by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext x
    change (schemeScalar S (b : Γ(S, ⊤))).val U •
      ((schemeScalar S ((b⁻¹ : Γ(S, ⊤)ˣ) : Γ(S, ⊤))).val U • x) = x
    rw [← mul_smul]
    change ((S.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op).hom (b : Γ(S, ⊤)) *
      (S.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op).hom
        ((b⁻¹ : Γ(S, ⊤)ˣ) : Γ(S, ⊤))) • x = x
    rw [← map_mul, Units.mul_inv, map_one, one_smul]))

end GradedPiSheaf

namespace FramedLatticePiSheaf

/-- An integral-unit scalar frame change is undone by an actual inverse scalar lattice map. -/
def reframeIntegralUnitIso (M : FramedLatticePiSheaf d π X F) (a : Oˣ) :
    M.reframe F (scalarReframeHom d F (Units.map (algebraMap O F).toMonoidHom a)) ≅ M :=
  isoOfTotalFrame F (M.lattice.coefficientUnitIso a⁻¹) (by
    change (M.reframe F (scalarReframeHom d F
        (Units.map (algebraMap O F).toMonoidHom a))).frameToTotal F ≫
      (rationalSheafFunctor F X).map ((latticeScalarFunctor d π X).map
        (coefficientSheafScale (algebraMap O (PiAlgebra d π) ((a⁻¹ : Oˣ) : O))
          M.lattice.sheaf)) = _
    erw [latticeScalarFunctor_coefficientScale, rationalSheafFunctor_coefficientScale]
    change ((constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} F)).map
      (scalarReframeHom d F (Units.map (algebraMap O F).toMonoidHom a)).toModuleIso.hom ≫
        M.frameToTotal F) ≫ _ = _
    erw [constantSheaf_scalarReframeHom, Category.assoc,
      ← coefficientSheafScale_naturality, ← Category.assoc,
      ← coefficientSheafScale_mul, ← map_mul, Units.mul_inv, map_one,
      coefficientSheafScale_one, Category.id_comp])

end FramedLatticePiSheaf

namespace SheafPreDatum

/-- The full four data admit a genuine isomorphism undoing any integral-unit scalar reframe. -/
def reframeIntegralUnitIso (D : SheafPreDatum d π F φ) (a : Oˣ) :
    D.reframe (scalarReframeHom d F (Units.map (algebraMap O F).toMonoidHom a)) ≅ D := by
  let e := D.eta.reframeIntegralUnitIso a
  let t := D.tangent.graded.structuralUnitIso (Units.map φ.toMonoidHom a⁻¹)
  exact {
    hom := {
      eta := e.hom
      tangent := t.hom
      u := by
        change (latticeScalarFunctor d π (S : TopCat)).map
          (coefficientSheafScale (algebraMap O (PiAlgebra d π) ((a⁻¹ : Oˣ) : O))
            D.eta.lattice.sheaf) ≫ D.u =
          D.u ≫ (structuralOSheafFunctor S φ).map
            (structuralScalarEnd D.tangent.graded.module (φ ((a⁻¹ : Oˣ) : O)))
        erw [latticeScalarFunctor_coefficientScale, structuralOSheafFunctor_structuralScalarEnd]
        exact coefficientSheafScale_naturality _ D.u }
    inv := {
      eta := e.inv
      tangent := t.inv
      u := by
        change (latticeScalarFunctor d π (S : TopCat)).map
          (coefficientSheafScale (algebraMap O (PiAlgebra d π) (((a⁻¹)⁻¹ : Oˣ) : O))
            D.eta.lattice.sheaf) ≫ D.u =
          D.u ≫ (structuralOSheafFunctor S φ).map
            (structuralScalarEnd D.tangent.graded.module
              (((Units.map φ.toMonoidHom a⁻¹)⁻¹ : Γ(S, ⊤)ˣ) : Γ(S, ⊤)))
        simp only [map_inv, inv_inv, Units.coe_map]
        erw [latticeScalarFunctor_coefficientScale, structuralOSheafFunctor_structuralScalarEnd]
        exact coefficientSheafScale_naturality _ D.u }
    hom_inv_id := Hom.ext e.hom_inv_id t.hom_inv_id
    inv_hom_id := Hom.ext e.inv_hom_id t.inv_hom_id }

end SheafPreDatum

end Langlands.DeligneFormalSpace
