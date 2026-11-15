import Langlands.Geometry.FormalGroup.DeligneScalarIsomorphism

/-! # The actual scalar uniformizer period of Deligne's four data -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.DeligneFormalSpace

open CategoryTheory _root_.AlgebraicGeometry TopologicalSpace

section Graded

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {d : ℕ} [NeZero d] {R : Sheaf J CommRingCat.{u}}
  {a : (R.obj ⋙ CategoryTheory.forget CommRingCat).sections}

namespace GradedPiSheaf

/-- A zero cyclic shift is identified by actual identity maps on the total sheaf. -/
def shiftTrivialIso (M : GradedPiSheaf d R a) (k : ZMod d) (hk : k = 0) :
    M.shift k ≅ M where
  hom := {
    val := 𝟙 M.toPiSheaf
    homogeneous U i x hx := by
      change x ∈ (M.component i).toSubmodule.obj U
      simpa only [shift, hk, add_zero] using hx }
  inv := {
    val := 𝟙 M.toPiSheaf
    homogeneous U i x hx := by
      change x ∈ (M.component (i + k)).toSubmodule.obj U
      simpa only [hk, add_zero] using hx }
  hom_inv_id := Hom.ext (Category.id_comp _)
  inv_hom_id := Hom.ext (Category.id_comp _)

end GradedPiSheaf

end Graded

variable {O : Type u} [CommRing O] {F : Type u} [Field F] [Algebra O F]
  {d : ℕ} [NeZero d] {π : O} {X : TopCat.{u}}

namespace LatticePiSheaf

/-- A zero cyclic shift has total identity and actual component index transports. -/
def shiftTrivialIso (M : LatticePiSheaf d π X) (k : ZMod d) (hk : k = 0) :
    M.shift k ≅ M := by
  have hi (i : ZMod d) : i + k = i := by rw [hk, add_zero]
  exact {
    hom := {
      total := 𝟙 M.sheaf
      component i := eqToHom (congrArg M.component (hi i))
      inclusion i := by
        dsimp only [shift]
        exact (M.component_eqToHom_inclusion (hi i)).trans
          ((congrArg (fun t => M.inclusion (i + k) ≫ t)
            ((latticeScalarFunctor d π X).map_id M.sheaf)).trans
              (Category.comp_id _)).symm }
    inv := {
      total := 𝟙 M.sheaf
      component i := eqToHom (congrArg M.component (hi i).symm)
      inclusion i := by
        dsimp only [shift]
        exact (M.component_eqToHom_inclusion (hi i).symm).trans
          ((congrArg (fun t => M.inclusion i ≫ t)
            ((latticeScalarFunctor d π X).map_id M.sheaf)).trans
              (Category.comp_id _)).symm }
    hom_inv_id := Hom.ext_total (Category.id_comp _)
    inv_hom_id := Hom.ext_total (Category.id_comp _) }

end LatticePiSheaf

namespace FramedLatticePiSheaf

/-- Shift by d and reframe by pi inverse; the actual total identity preserves the frame. -/
def uniformizerInverseReframeIso (M : FramedLatticePiSheaf d π X F)
    (hπ : algebraMap O F π ≠ 0) :
    (M.shiftInt F hπ (d : ℤ)).reframe F
      (scalarReframeHom d F (Units.mk0 (algebraMap O F π) hπ)⁻¹) ≅ M :=
  isoOfTotalFrame F (M.lattice.shiftTrivialIso ((d : ℤ) : ZMod d) (by simp)) (by
    change ((M.shiftInt F hπ (d : ℤ)).reframe F
      (scalarReframeHom d F (Units.mk0 (algebraMap O F π) hπ)⁻¹)).frameToTotal F ≫
        (rationalSheafFunctor F X).map ((latticeScalarFunctor d π X).map (𝟙 _)) = _
    rw [frameToTotal_comp_totalId]
    change (constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} F)).map
        (scalarReframeHom d F (Units.mk0 (algebraMap O F π) hπ)⁻¹).toModuleIso.hom ≫
          (M.shiftInt F hπ (d : ℤ)).frameToTotal F = _
    erw [constantSheaf_scalarReframeHom, M.frameToTotal_shiftInt,
      zpow_natCast, rationalPiAut_pow]
    change coefficientSheafScale (algebraMap O F π)⁻¹ _ ≫
      (M.frameToTotal F ≫ coefficientSheafScale (algebraMap O F π) _) = _
    erw [← coefficientSheafScale_naturality, ← Category.assoc,
      ← coefficientSheafScale_mul, inv_mul_cancel₀ hπ,
      coefficientSheafScale_one, Category.id_comp])

end FramedLatticePiSheaf

variable {S : Scheme.{u}} {φ : O →+* Γ(S, ⊤)}

namespace SheafPreDatum

/-- The actual scalar uniformizer period is a genuine isomorphism of all four data. -/
def uniformizerInverseReframeIso (D : SheafPreDatum d π F φ)
    (hπ : algebraMap O F π ≠ 0) :
    D.shiftReframe hπ
      (scalarReframeHom d F (Units.mk0 (algebraMap O F π) hπ)⁻¹) (d : ℤ) ≅ D where
  hom := {
    eta := (D.eta.uniformizerInverseReframeIso hπ).hom
    tangent := (D.tangent.graded.shiftTrivialIso ((d : ℤ) : ZMod d) (by simp)).hom
    u := by
      change (latticeScalarFunctor d π (S : TopCat)).map (𝟙 _) ≫ D.u =
        D.u ≫ (structuralOSheafFunctor S φ).map (𝟙 _)
      simp }
  inv := {
    eta := (D.eta.uniformizerInverseReframeIso hπ).inv
    tangent := (D.tangent.graded.shiftTrivialIso ((d : ℤ) : ZMod d) (by simp)).inv
    u := by
      change (latticeScalarFunctor d π (S : TopCat)).map (𝟙 _) ≫ D.u =
        D.u ≫ (structuralOSheafFunctor S φ).map (𝟙 _)
      simp }
  hom_inv_id := Hom.ext (FramedLatticePiSheaf.Hom.ext
    (LatticePiSheaf.Hom.ext_total (Category.id_comp _)))
      (GradedPiSheaf.Hom.ext (Category.id_comp _))
  inv_hom_id := Hom.ext (FramedLatticePiSheaf.Hom.ext
    (LatticePiSheaf.Hom.ext_total (Category.id_comp _)))
      (GradedPiSheaf.Hom.ext (Category.id_comp _))

end SheafPreDatum

end Langlands.DeligneFormalSpace
