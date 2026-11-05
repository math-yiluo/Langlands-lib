import Langlands.GroupScheme.AffinePointCoordinateSmooth
import Langlands.GroupScheme.ProductProperties
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.Data.Finset.Dedup

/-! # Coordinate-smooth families of finite products of group schemes -/

noncomputable section

universe u v w z

open CategoryTheory Opposite AlgebraicGeometry CategoryTheory.Limits
open scoped Classical CategoryTheory.MonObj Manifold ContDiff

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

section Points

variable {S : Scheme.{u}} {J : Type u} [Finite J] (G : J → GroupScheme S)

/-- The actual relative scheme map inserting a factor into a finite product,
with group identity in every other component. -/
def piFactorInclusion (j : J) : (G j).X ⟶ (pi G).X :=
  (piPointsEquiv G (G j).X).symm (fun k =>
    if h : j = k then eqToHom (congrArg (fun i => (G i).X) h) else 1)

@[simp] theorem piFactorInclusion_self (j : J) :
    piFactorInclusion G j ≫ (Pi.π G j).hom.hom = 𝟙 (G j).X := by
  simp [piFactorInclusion]

theorem piFactorInclusion_ne (j k : J) (h : j ≠ k) :
    piFactorInclusion G j ≫ (Pi.π G k).hom.hom = 1 := by
  simp [piFactorInclusion, h]

/-- Any point of the product is an ordered product of its actual factor
insertions. Only one inserted factor survives in each projection. -/
theorem piPointsEquiv_symm_eq_list_prod (T : Over S)
    (p : ∀ j, T ⟶ (G j).X) (l : List J)
    (hl : l.Nodup) (hall : ∀ j, j ∈ l) :
    (piPointsEquiv G T).symm p =
      (l.map (fun j => p j ≫ piFactorInclusion G j)).prod := by
  apply (piPointsEquiv G T).injective
  rw [MulEquiv.apply_symm_apply]
  funext j
  let q : (T ⟶ (pi G).X) →* (T ⟶ (G j).X) :=
    (Pi.evalMonoidHom _ j).comp (piPointsEquiv G T).toMonoidHom
  change p j = q ((l.map (fun k => p k ≫ piFactorInclusion G k)).prod)
  rw [map_list_prod, List.map_map]
  simp only [Function.comp_def]
  have hq (k : J) (h : k ≠ j) :
      q (p k ≫ piFactorInclusion G k) = 1 := by
    change (p k ≫ piFactorInclusion G k) ≫ (Pi.π G j).hom.hom = 1
    rw [Category.assoc, piFactorInclusion_ne G k j h, MonObj.comp_one]
  rw [List.prod_map_eq_pow_single j _ (fun k h _ => hq k h),
    List.count_eq_one_of_mem hl (hall j), pow_one]
  change p j = (p j ≫ piFactorInclusion G j) ≫ (Pi.π G j).hom.hom
  rw [Category.assoc, piFactorInclusion_self, Category.comp_id]

end Points

section Smooth

variable {R : CommRingCat.{u}} {J : Type u} [Finite J]
  (G : J → GroupScheme (Spec R)) [∀ j, IsAffine (G j).X.left]
  (A : CommAlgCat.{u} R)
  {B : Type z} [NormedCommRing B] [NormedAlgebra ℝ B]
  (c : A →+* B)
  {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type v} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/-- The underlying scheme of the actual finite product is affine. -/
theorem isAffine_pi : IsAffine (pi G).X.left := by
  have : IsAffineHom (pi G).X.hom :=
    prop_pi_hom @IsAffineHom G (fun _ => inferInstance)
  exact isAffine_of_isAffineHom (pi G).X.hom

private theorem coordinateSmooth_list_prod (l : List J)
    (p : J → M → (pi G).affinePoints A)
    (hp : ∀ j, (pi G).CoordinateSmooth A c I (p j)) :
    (pi G).CoordinateSmooth A c I (fun x => (l.map (fun j => p j x)).prod) := by
  let : IsAffine (pi G).X.left := isAffine_pi G
  induction l with
  | nil => exact coordinateSmooth_const (pi G) A c I 1
  | cons j l ih => exact CoordinateSmooth.mul (pi G) A c I (hp j) ih

/-- Smooth families of factor points assemble to a smooth family of actual
product points. -/
theorem coordinateSmooth_piPointsEquiv_symm
    (p : ∀ j, M → (G j).affinePoints A)
    (hp : ∀ j, (G j).CoordinateSmooth A c I (p j)) :
    (pi G).CoordinateSmooth A c I
      (fun x => (piPointsEquiv G ((algSpec R).obj (op A))).symm (fun j => p j x)) := by
  let := Fintype.ofFinite J
  have h := coordinateSmooth_list_prod G A c I Finset.univ.toList
    (fun j x => p j x ≫ piFactorInclusion G j)
    (fun j => (hp j).postcomp (piFactorInclusion G j))
  have he (x : M) :=
    piPointsEquiv_symm_eq_list_prod G ((algSpec R).obj (op A)) (fun j => p j x)
      Finset.univ.toList (Finset.nodup_toList _) (by simp)
  simpa only [← he] using h

/-- The regular-function criterion on a finite product is equivalent to the
same criterion on every actual projected point family. -/
theorem coordinateSmooth_groupSchemePi_iff (p : M → (pi G).affinePoints A) :
    (pi G).CoordinateSmooth A c I p ↔
      ∀ j, (G j).CoordinateSmooth A c I
        (fun x => piPointsEquiv G ((algSpec R).obj (op A)) (p x) j) := by
  constructor
  · intro hp j
    exact hp.postcomp (Pi.π G j).hom.hom
  · intro hp
    have h := coordinateSmooth_piPointsEquiv_symm G A c I
      (fun j x => piPointsEquiv G ((algSpec R).obj (op A)) (p x) j) hp
    simpa only [MulEquiv.symm_apply_apply] using h

/-- The actual point equivalence restricts to the specified coordinate-smooth
parameter families. -/
def coordinateSmoothPiEquiv :
    {p : M → (pi G).affinePoints A // (pi G).CoordinateSmooth A c I p} ≃
      (∀ j, {p : M → (G j).affinePoints A // (G j).CoordinateSmooth A c I p}) where
  toFun p j := ⟨fun x => piPointsEquiv G ((algSpec R).obj (op A)) (p.1 x) j,
    (coordinateSmooth_groupSchemePi_iff G A c I p.1).mp p.2 j⟩
  invFun p := ⟨fun x => (piPointsEquiv G ((algSpec R).obj (op A))).symm (fun j => (p j).1 x),
    coordinateSmooth_piPointsEquiv_symm G A c I (fun j => (p j).1) (fun j => (p j).2)⟩
  left_inv p := by
    apply Subtype.ext
    funext x
    exact (piPointsEquiv G ((algSpec R).obj (op A))).symm_apply_apply (p.1 x)
  right_inv p := by
    funext j
    apply Subtype.ext
    funext x
    exact congrFun ((piPointsEquiv G ((algSpec R).obj (op A))).apply_symm_apply
      (fun k => (p k).1 x)) j

end Smooth

end Langlands.GroupScheme
