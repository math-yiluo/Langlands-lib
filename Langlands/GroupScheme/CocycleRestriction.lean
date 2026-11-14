import Langlands.GroupScheme.Torus.OpenSections

/-! # Restricting group-valued cocycles to a new base -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Cocycle

variable {S : Scheme.{u}} {G : GroupScheme S} {U : Over S}

/-- Precompose a cocycle with a map of its cover, retaining the base. -/
def comap (ξ : Cocycle G U) {V : Over S} (r : V ⟶ U) : Cocycle G V where
  toFun a b := ξ.toFun (a ≫ r) (b ≫ r)
  naturality t a b := by simpa only [Category.assoc] using ξ.naturality t (a ≫ r) (b ≫ r)
  cocycle a b c := ξ.cocycle (a ≫ r) (b ≫ r) (c ≫ r)

/-- Restrict a cocycle to a new base and a compatible cover. -/
def baseChangeAlong (ξ : Cocycle G U) {S' : Scheme.{u}} (b : S' ⟶ S)
    (V : Over S') (r : (Over.map b).obj V ⟶ U) :
    Cocycle ((GroupScheme.baseChange b).obj G) V where
  toFun a c := (baseChangePointsEquiv b G _).symm
    (ξ.toFun ((Over.map b).map a ≫ r) ((Over.map b).map c ≫ r))
  naturality t a c := by
    apply (baseChangePointsEquiv b G _).injective
    simp only [MulEquiv.apply_symm_apply, baseChangePointsEquiv_naturality]
    simpa only [Functor.map_comp, Category.assoc] using
      ξ.naturality ((Over.map b).map t) ((Over.map b).map a ≫ r) ((Over.map b).map c ≫ r)
  cocycle a c d := by
    apply (baseChangePointsEquiv b G _).injective
    simp only [MulEquiv.apply_symm_apply, map_mul]
    exact ξ.cocycle _ _ _

/-- For a monomorphic change of base, triviality over the new base already gives
triviality of the same cover and group points viewed over the old base. -/
theorem IsTrivial.of_baseChangeAlong {S' : Scheme.{u}} (b : S' ⟶ S) [Mono b]
    {V : Over S'} {ξ : Cocycle G ((Over.map b).obj V)}
    (h : (ξ.baseChangeAlong b V (𝟙 _)).IsTrivial) : ξ.IsTrivial := by
  obtain ⟨f, hf⟩ := h
  refine ⟨baseChangePointsEquiv b G V f, fun {Z} a c => ?_⟩
  have hac : c.left ≫ V.hom = a.left ≫ V.hom := by
    apply (cancel_mono b).mp
    simpa only [Over.map_obj_hom, Category.assoc] using (Over.w c).trans (Over.w a).symm
  let Z' : Over S' := Over.mk (a.left ≫ V.hom)
  let a' : Z' ⟶ V := Over.homMk a.left
  let c' : Z' ⟶ V := Over.homMk c.left hac
  let t : Z ⟶ (Over.map b).obj Z' := Over.homMk (𝟙 Z.left) (by
    simpa only [Over.map_obj_hom, Over.mk_hom, Category.id_comp, Category.assoc, Z'] using (Over.w a))
  have ha : t ≫ (Over.map b).map a' ≫ 𝟙 ((Over.map b).obj V) = a := by ext; simp [t, a']
  have hc : t ≫ (Over.map b).map c' ≫ 𝟙 ((Over.map b).obj V) = c := by ext; simp [t, c']
  have h' := congrArg (fun x => t ≫ baseChangePointsEquiv b G Z' x) (hf a' c')
  simp only [baseChangeAlong, MulEquiv.apply_symm_apply, map_mul, map_inv,
    baseChangePointsEquiv_naturality, MonObj.comp_mul, GrpObj.comp_inv,
    ← ξ.naturality, ha, hc, ← Category.assoc] at h'
  convert h' using 1
  congr 1

end Langlands.GroupScheme.Cocycle
