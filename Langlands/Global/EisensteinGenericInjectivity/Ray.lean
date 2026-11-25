import Langlands.Global.EisensteinGenericInjectivity.PlaceHeight
import Langlands.Global.PositiveRealIdeles
import Langlands.Global.PositiveRealTorusLog
import Langlands.GroupScheme.Dynamic.GeneralLinearCocharacterDiagonal
import Langlands.GroupScheme.MultiplicativePointTopology
import Langlands.Global.PositiveRealTorusEmbedding

/-! # An archimedean ray through a cocharacter -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Opposite
open scoped CategoryTheory.MonObj NNReal Matrix

set_option autoImplicit false

namespace Langlands.Global.EisensteinGenericInjectivity

open Langlands.GroupScheme AdelicGroupPoints RepresentationGrowth

variable {F : Type u} [Field F] [NumberField F]

local instance gmIsAffine : IsAffine (Gm (Spec (CommRingCat.of F))).X.left := by
  change IsAffine (CategoryTheory.Limits.pullback
    (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C (R := ULift.{u} ℤ))))
    (Gm.toSpecZ (Spec (CommRingCat.of F))))
  infer_instance

variable (F) in
/-- The adelic point of the multiplicative group with value `exp s` at every infinite place and
`1` at every finite place. -/
def gmRayPoint (s : ℝ) : AdelicGroupPoints F (Gm (Spec (CommRingCat.of F))).toGrp :=
  (Gm.affineUnitsEquiv (CommRingCat.of F) (CommAlgCat.of F (AdeleRing (𝓞 F) F))).symm
    (PositiveRealIdeles.full F (PositiveRealTorus.expUnit s))

theorem affineUnitsEquiv_gmRayPoint (s : ℝ) :
    Gm.affineUnitsEquiv (CommRingCat.of F) (CommAlgCat.of F (AdeleRing (𝓞 F) F))
      (gmRayPoint F s) = PositiveRealIdeles.full F (PositiveRealTorus.expUnit s) :=
  MulEquiv.apply_symm_apply _ _

theorem finite_gmRayPoint (s : ℝ) :
    finite F (Gm (Spec (CommRingCat.of F))).toGrp (gmRayPoint F s) = 1 := by
  apply (Gm.affineUnitsEquiv (CommRingCat.of F)
    (CommAlgCat.of F (FiniteAdeleRing (𝓞 F) F))).injective
  rw [map_one]
  change Gm.affineUnitsEquiv (CommRingCat.of F) (CommAlgCat.of F (FiniteAdeleRing (𝓞 F) F))
    (GroupScheme.affinePointMap _ (CommAlgCat.ofHom
      (AlgHom.snd F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))) (gmRayPoint F s)) = 1
  rw [Gm.affineUnitsEquiv_naturality, affineUnitsEquiv_gmRayPoint]
  apply Units.ext
  rfl

variable {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]

variable (F) in
/-- The ray `s ↦ c(exp s)` of a cocharacter `c`, at the infinite places. -/
def ray (c : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) (s : ℝ) : AdelicGroupPoints F G :=
  map F _ G c (gmRayPoint F s)

theorem finite_ray (c : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) (s : ℝ) :
    finite F G (ray F c s) = 1 := by
  rw [ray, finite_map, finite_gmRayPoint, map_one]

omit [IsAffine G.X.left] in
theorem ray_zero (c : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) : ray F c 0 = 1 := by
  have h : PositiveRealTorus.expUnit 0 = 1 := by
    apply Units.ext
    apply NNReal.eq
    simp
  rw [ray, gmRayPoint, h, map_one, map_one, map_one]

variable {N : ℕ}

omit [IsAffine G.X.left] in
/-- A diagonalized cocharacter acts on the ray by the diagonal of powers. -/
theorem adelicMatrix_ray (σ : MatrixRepresentation G (Fin N))
    (c : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) (e : Fin N → ℤ)
    (hc : c ≫ σ = GeneralLinear.diagonalCocharacter (Fin N) (CommRingCat.of F) e) (s : ℝ) :
    adelicMatrix F G σ (ray F c s) =
      GeneralLinear.diagonalUnits (AdeleRing (𝓞 F) F) e
        (PositiveRealIdeles.full F (PositiveRealTorus.expUnit s)) := by
  change σ.affineMatrix (CommAlgCat.of F (AdeleRing (𝓞 F) F))
    (gmRayPoint F s ≫ c.hom.hom) = _
  rw [MatrixRepresentation.affineMatrix_apply, Category.assoc, ← Grp.comp_hom_hom, hc,
    GeneralLinear.CocharacterDiagonal.affinePointsEquiv_diagonalCocharacter]
  exact congrArg _ (affineUnitsEquiv_gmRayPoint s)

theorem placeHom_full_expUnit (w : InfinitePlace F) (s : ℝ) :
    placeHom w ((PositiveRealIdeles.full F (PositiveRealTorus.expUnit s) : Ideles F) :
      AdeleRing (𝓞 F) F) = (Real.exp s : ℂ) := by
  rw [placeHom_apply, PositiveRealIdeles.extensionEmbedding_full, PositiveRealTorus.coe_expUnit]

omit [IsAffine G.X.left] in
/-- At every infinite place the inverse of the ray acts diagonally by inverse powers. -/
theorem placeMatrix_ray_inv (σ : MatrixRepresentation G (Fin N))
    (c : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) (e : Fin N → ℤ)
    (hc : c ≫ σ = GeneralLinear.diagonalCocharacter (Fin N) (CommRingCat.of F) e)
    (w : InfinitePlace F) (s : ℝ) :
    placeMatrix σ w (ray F c s)⁻¹ =
      Matrix.diagonal fun i => (Real.exp s : ℂ) ^ (-e i) := by
  rw [placeMatrix, map_inv, adelicMatrix_ray σ c e hc s, ← map_inv,
    GeneralLinear.coe_diagonalUnits, Matrix.diagonal_map (map_zero _)]
  congr 1
  funext i
  let u := PositiveRealIdeles.full F (PositiveRealTorus.expUnit s)
  have hu : (Units.map (placeHom (F := F) w).toMonoidHom u : ℂ) = (Real.exp s : ℂ) := by
    rw [Units.coe_map]
    exact placeHom_full_expUnit w s
  have h := congrArg Units.val (map_zpow (Units.map (placeHom (F := F) w).toMonoidHom) u⁻¹ (e i))
  rw [Units.coe_map, map_inv, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, hu] at h
  rw [zpow_neg, ← inv_zpow]
  exact h

omit [IsAffine G.X.left] in
/-- The ray is continuous: the source curve `s ↦ gmRayPoint F s` is the positive-real torus
point `PositiveRealTorus.continuousFull` of `𝔾_m`, split by `splitTorus.gmIso`, at the constant
family `exp s`, and `AdelicGroupPoints.map` is continuous. -/
theorem continuous_ray (c : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    Continuous (ray F c) := by
  have hpt : ∀ s, gmRayPoint F s = PositiveRealTorus.continuousFull F PUnit
      (Gm (Spec (CommRingCat.of F))) (splitTorus.gmIso _)
      (fun _ => PositiveRealTorus.expUnit s) := by
    intro s
    apply (PositiveRealTorus.coordinates F PUnit (Gm (Spec (CommRingCat.of F)))
      (splitTorus.gmIso _) (Adeles F)).injective
    rw [PositiveRealTorus.continuousFull_apply, PositiveRealTorus.coordinates_full]
    change splitTorus.algebraPointsEquiv PUnit _
      (gmRayPoint F s ≫ (splitTorus.gmIso _).hom.hom.hom) = _
    rw [GeneralLinear.CocharacterDiagonal.algebraPointsEquiv_comp_gmIso]
    funext _
    exact affineUnitsEquiv_gmRayPoint s
  have hsrc : Continuous (gmRayPoint F) := by
    rw [funext hpt]
    exact (PositiveRealTorus.continuousFull F PUnit (Gm (Spec (CommRingCat.of F)))
      (splitTorus.gmIso _)).continuous.comp
        (continuous_pi fun _ => PositiveRealTorus.continuous_expUnit)
  exact (map F _ G c).continuous.comp hsrc

end Langlands.Global.EisensteinGenericInjectivity
