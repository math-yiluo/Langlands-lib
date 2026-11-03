import Langlands.AlgebraicGeometry.Modules.CoherentLineBundle
import Langlands.AlgebraicGeometry.Modules.StructureUnitScalars
import Langlands.AlgebraicGeometry.Modules.SerreVanishing.Mul

/-! # Comparing local tensor trivializations -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Langlands.Scheme.Modules Langlands.SchemeModule

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Modules

private lemma tensorContraction_change {Y : Scheme.{u}} (M N : Y.Modules)
    (t s : N ≅ SheafOfModules.unit Y.ringCatSheaf) :
    tensorMap (𝟙 M) s.hom ≫ (tensorRightUnitor M).hom =
      (tensorMap (𝟙 M) t.hom ≫ (tensorRightUnitor M).hom) ≫
        ((structureAutScalar (t.symm ≪≫ s) : Γ(Y, ⊤)) • 𝟙 M) := by
  have h := SerreVanishing.tensorMap_id_unitEnd M (t.inv ≫ s.hom)
  have ht : tensorMap (𝟙 M) t.hom ≫ tensorMap (𝟙 M) (t.inv ≫ s.hom) =
      tensorMap (𝟙 M) s.hom := by
    rw [tensorMap_comp, Category.id_comp, Iso.hom_inv_id_assoc]
  change _ = _ ≫ ((unitEndCoefficient (t.inv ≫ s.hom) ⊤) • 𝟙 M)
  rw [Category.assoc, ← h, ← Category.assoc, ht]

variable {S : Scheme.{u}} {N : S.Modules} {U : S.Opens}

/-- The unit that compares two trivializations of the same restricted line module. -/
def tensorTrivializationScalar
    (t s : N.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    Γ(U.toScheme, ⊤)ˣ :=
  structureAutScalar (t.symm ≪≫ s)

@[simp]
lemma tensorTrivializationScalar_self
    (t : N.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    tensorTrivializationScalar t t = 1 := by
  simp [tensorTrivializationScalar]

@[simp]
lemma tensorTrivializationScalar_reverse
    (t s : N.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    tensorTrivializationScalar s t = (tensorTrivializationScalar t s)⁻¹ := by
  exact structureAutScalar_symm (t.symm ≪≫ s)

lemma tensorTrivializationScalar_trans
    (t s r : N.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    tensorTrivializationScalar t r =
      tensorTrivializationScalar t s * tensorTrivializationScalar s r := by
  unfold tensorTrivializationScalar
  rw [← structureAutScalar_trans]
  congr 1
  simp

/-- Changing the line trivialization changes contraction by a scalar automorphism. -/
lemma tensorRestrictionTrivialization_change (M : S.Modules)
    (t s : N.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    (tensorRestrictionTrivialization M N U s).hom =
      (tensorRestrictionTrivialization M N U t).hom ≫
        ((tensorTrivializationScalar t s : Γ(U.toScheme, ⊤)) •
          𝟙 (M.restrict U.ι)) := by
  have := isIso_restrictTensorHom U M N
  have h := tensorContraction_change (M.restrict U.ι) (N.restrict U.ι) t s
  change _ =
    (inv (restrictTensorHom U M N) ≫
      tensorMap (𝟙 (M.restrict U.ι)) t.hom ≫
      (tensorRightUnitor (M.restrict U.ι)).hom) ≫ _
  unfold tensorTrivializationScalar
  rw [Category.assoc, ← h]
  rfl

/-- Contraction in one trivialization after expansion in another is scalar multiplication. -/
lemma tensorRestrictionTrivialization_inv_comp (M : S.Modules)
    (t s : N.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    (tensorRestrictionTrivialization M N U t).inv ≫
        (tensorRestrictionTrivialization M N U s).hom =
      (tensorTrivializationScalar t s : Γ(U.toScheme, ⊤)) •
        𝟙 (M.restrict U.ι) := by
  rw [tensorRestrictionTrivialization_change, Iso.inv_hom_id_assoc]

/-- The comparison acts on sections of every open of the trivializing subscheme. -/
lemma tensorRestrictionTrivialization_inv_comp_app (M : S.Modules)
    (t s : N.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (V : U.toScheme.Opens) (x : Γ(M.restrict U.ι, V)) :
    (tensorRestrictionTrivialization M N U s).hom.app V
        ((tensorRestrictionTrivialization M N U t).inv.app V x) =
      restrictScalar V (tensorTrivializationScalar t s : Γ(U.toScheme, ⊤)) • x := by
  have h := congrArg (fun f => f.app V x)
    (tensorRestrictionTrivialization_inv_comp M t s)
  exact h

end Langlands.AlgebraicGeometry.Modules
