import Langlands.AlgebraicGeometry.Modules.RestrictionIsoSections
import Langlands.AlgebraicGeometry.ProjectiveBundle.TensorFrames
import Langlands.AlgebraicGeometry.ProjectiveBundle.EvaluationCoordinates

/-! # Frame coordinates under restriction isomorphisms -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Modules

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.ProjectiveBundle.LocalFrame

variable {S : Scheme.{u}} {M N : S.Modules} {n : ℕ} {U V : S.Opens}

lemma ofRestrictIso_coordinates (e : LocalFrame M n U)
    (f : M.restrict U.ι ≅ N.restrict U.ι) (h : V ≤ U) (x : Γ(M, V)) :
    (e.ofRestrictIso f).coordinates V h (SerreVanishing.modE f V h x) =
      e.coordinates V h x := by
  funext i
  rw [coordinates_apply, coordinates_apply, ← overRestrictionIso_hom_app]
  have he : (overRestrictionIso f).hom ≫
      localBasisCoordinate (e.ofRestrictIso f) ⟨i⟩ =
      localBasisCoordinate e ⟨i⟩ := by
    change (overRestrictionIso f).hom ≫
        ((overRestrictionIso f).inv ≫ e.inv) ≫ freeCoordinate U _ ⟨i⟩ =
      e.inv ≫ freeCoordinate U _ ⟨i⟩
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact congrArg (fun g => g.val.app (op (Over.mk (homOfLE h))) x) he

lemma ofRestrictIso_coordinates_apply (e : LocalFrame M n U)
    (f : M.restrict U.ι ≅ N.restrict U.ι) (h : V ≤ U) (x : Γ(N, V)) :
    (e.ofRestrictIso f).coordinates V h x =
      e.coordinates V h (SerreVanishing.modE f.symm V h x) := by
  have he := ofRestrictIso_coordinates e f h (SerreVanishing.modE f.symm V h x)
  have hc := SerreVanishing.modE_symm_modE f.symm V h x
  simp only [Iso.symm_symm_eq] at hc
  rw [hc] at he
  exact he

lemma ofRestrictIso_basisSection (e : LocalFrame M n U)
    (f : M.restrict U.ι ≅ N.restrict U.ι) (h : V ≤ U) (i : Fin (n + 1)) :
    (e.ofRestrictIso f).basisSection V h i =
      SerreVanishing.modE f V h (e.basisSection V h i) := by
  apply ((e.ofRestrictIso f).coordinates V h).injective
  rw [ofRestrictIso_coordinates]
  simp only [basisSection, LinearEquiv.apply_symm_apply]

end Langlands.AlgebraicGeometry.ProjectiveBundle.LocalFrame
