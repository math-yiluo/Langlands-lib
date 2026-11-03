import Langlands.AlgebraicGeometry.ProjectiveBundle.RestrictionFrameCoordinates
import Langlands.AlgebraicGeometry.Modules.TensorTrivializationComparison

/-! # Coordinates of tensor frames -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Modules
open Langlands.SchemeModule Langlands.SchemeModule.SectionClearing

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.ProjectiveBundle

variable {S : Scheme.{u}} {M N : S.Modules} {n : ℕ} {U V : S.Opens}

namespace TensorFrames

/-- The comparing unit as a function on the original trivializing open. -/
def trivializationUnit
    (t s : N.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    Γ(S, U)ˣ :=
  Units.map U.topIso.hom.hom.toMonoidHom (tensorTrivializationScalar t s)

lemma trivializationUnit_val
    (t s : N.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    (trivializationUnit t s : Γ(S, U)) = chartCoeff (t.inv ≫ s.hom) := by
  rw [chartCoeff_eq]
  rfl

@[simp]
lemma trivializationUnit_self
    (t : N.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    trivializationUnit t t = 1 := by
  dsimp only [trivializationUnit]
  rw [tensorTrivializationScalar_self, map_one]

@[simp]
lemma trivializationUnit_reverse
    (t s : N.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    trivializationUnit s t = (trivializationUnit t s)⁻¹ := by
  dsimp only [trivializationUnit]
  rw [tensorTrivializationScalar_reverse, map_inv]

lemma trivializationUnit_trans
    (t s r : N.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    trivializationUnit t r = trivializationUnit t s * trivializationUnit s r := by
  dsimp only [trivializationUnit]
  rw [tensorTrivializationScalar_trans t s r, map_mul]

/-- The contraction comparison on every smaller original open is the restricted unit. -/
lemma contraction_change (M : S.Modules)
    (t s : N.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (h : V ≤ U) (x : Γ(tensorObj M N, V)) :
    SerreVanishing.modE (tensorRestrictionTrivialization M N U s) V h x =
      S.presheaf.map (homOfLE h).op (trivializationUnit t s : Γ(S, U)) •
        SerreVanishing.modE (tensorRestrictionTrivialization M N U t) V h x := by
  have hf : (Scheme.Modules.restrictFunctor U.ι).map (𝟙 (tensorObj M N)) ≫
      (tensorRestrictionTrivialization M N U s).hom =
      (tensorRestrictionTrivialization M N U t).hom ≫
        (unitEndCoefficient (t.inv ≫ s.hom) ⊤ • 𝟙 _) := by
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
    exact tensorRestrictionTrivialization_change M t s
  have he := SerreVanishing.modE_mul
    (tensorRestrictionTrivialization M N U t)
    (tensorRestrictionTrivialization M N U s)
    (𝟙 (tensorObj M N)) (t.inv ≫ s.hom) hf V h x
  rw [trivializationUnit_val]
  exact he

end TensorFrames

namespace LocalFrame

lemma tensor_coordinates (e : LocalFrame M n U)
    (t : N.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (h : V ≤ U) (x : Γ(tensorObj M N, V)) :
    (e.tensor t).coordinates V h x =
      e.coordinates V h
        (SerreVanishing.modE (tensorRestrictionTrivialization M N U t) V h x) := by
  exact ofRestrictIso_coordinates_apply e
    (tensorRestrictionTrivialization M N U t).symm h x

lemma tensor_basisSection (e : LocalFrame M n U)
    (t : N.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (h : V ≤ U) (i : Fin (n + 1)) :
    (e.tensor t).basisSection V h i =
      SerreVanishing.modE (tensorRestrictionTrivialization M N U t).symm V h
        (e.basisSection V h i) :=
  ofRestrictIso_basisSection e (tensorRestrictionTrivialization M N U t).symm h i

lemma tensor_coordinates_change_trivialization (e : LocalFrame M n U)
    (t s : N.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (h : V ≤ U) (x : Γ(tensorObj M N, V)) :
    (e.tensor s).coordinates V h x =
      S.presheaf.map (homOfLE h).op (TensorFrames.trivializationUnit t s : Γ(S, U)) •
        (e.tensor t).coordinates V h x := by
  rw [tensor_coordinates, tensor_coordinates, TensorFrames.contraction_change M t s,
    map_smul]

lemma tensor_dual_change_coefficient (e f : LocalFrame M n U)
    (t s : N.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (h : V ≤ U) (i j : Fin (n + 1)) :
    (e.tensor t).dual.change (f.tensor s).dual V h h (Pi.single j 1) i =
      S.presheaf.map (homOfLE h).op (TensorFrames.trivializationUnit s t : Γ(S, U)) *
        e.dual.change f.dual V h h (Pi.single j 1) i := by
  rw [dual_change_coefficient, dual_change_coefficient,
    tensor_coordinates_change_trivialization e s t]
  change _ * ((e.tensor s).coordinates V h ((f.tensor s).basisSection V h i)) j = _
  rw [tensor_coordinates, tensor_basisSection]
  have hc := SerreVanishing.modE_symm_modE
    (tensorRestrictionTrivialization M N U s).symm V h (f.basisSection V h i)
  simp only [Iso.symm_symm_eq] at hc
  rw [hc]

end LocalFrame

end Langlands.AlgebraicGeometry.ProjectiveBundle
