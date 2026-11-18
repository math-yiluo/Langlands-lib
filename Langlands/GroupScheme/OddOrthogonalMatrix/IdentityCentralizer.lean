import Langlands.GroupScheme.OddOrthogonalMatrix.MatrixCentralizer
import Langlands.GroupScheme.OddOrthogonalMatrix.MatrixPointRange
import Langlands.GroupScheme.OddOrthogonalMatrix.ConnectedGenerators

/-! # Trivial rational centralizer of the actual odd identity component -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry Opposite
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.OddOrthogonalMatrix

variable {l : Type} [Fintype l] [DecidableEq l] (K : Type u) [Field K]

/-- Matrix over the original field of an actual base point. -/
def rationalMatrix
    (g : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ (groupScheme l K).X) : GL (Index l) K :=
  Matrix.GeneralLinearGroup.map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
    (pointMatrix K _ g)

/-- Every constant family is the scalar extension of its original matrix. -/
theorem pointMatrix_constantPoint_rational
    (g : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ (groupScheme l K).X)
    (T : Over (Spec (CommRingCat.of K))) :
    pointMatrix K T ((groupScheme l K).constantPoint g T) =
      Matrix.GeneralLinearGroup.map (scalarMap T) (rationalMatrix K g) := by
  rw [GroupScheme.constantPoint, pointMatrix_naturality]
  apply Units.ext
  apply Matrix.ext
  intro i j
  let e := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv
  change T.hom.appTop.hom ((pointMatrix K _ g).val i j) =
    T.hom.appTop.hom (e.symm (e ((pointMatrix K _ g).val i j)))
  rw [e.symm_apply_apply]

/-- Over an affine coefficient test, this is the ordinary coefficient-algebra map. -/
theorem affineMatrix_constantPoint_rational
    (g : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ (groupScheme l K).X)
    (A : CommAlgCat.{u} (CommRingCat.of K)) :
    affineMatrix K A ((groupScheme l K).constantPoint g ((algSpec (CommRingCat.of K)).obj (op A))) =
      Matrix.GeneralLinearGroup.map (algebraMap K A) (rationalMatrix K g) := by
  apply Units.ext
  rw [affineMatrix_val_eq_ambientMatrix_map]
  change (pointMatrix K _ ((groupScheme l K).constantPoint g _)).val.map _ = _
  rw [pointMatrix_constantPoint_rational]
  apply Matrix.ext
  intro i j
  exact (Corepresented.affineSectionsIso A).hom.hom.commutes _

/-- The affine diagonal-torus coefficient matrix. -/
theorem affineMatrix_diagonalTorus {A : Type u} [CommRing A] [Algebra K A]
    (t : Lie.AffinePoints
      (splitTorus.commGroupScheme (Spec (CommRingCat.of K)) (ULift.{u} l)).toGrp A) :
    (affineMatrix K (CommAlgCat.of (CommRingCat.of K) A) (t ≫ (diagonalTorus l K).hom.hom)).val =
      Matrix.diagonal (fun i => (torusWeights (GeneralLinear.torusCoords t) i : A)) := by
  have ht := affinePointsEquiv_diagonalTorus_inclusion t
  rw [Grp.comp_hom_hom, ← Category.assoc, affinePointsEquiv_inclusion] at ht
  exact congrArg Units.val ht

/-- A rational point commuting with every relative identity-component point
is the identity, over every field. -/
theorem eq_one_of_centralizes_identityComponent
    (g : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ (groupScheme l K).X)
    (hc : ∀ (T : Over (Spec (CommRingCat.of K)))
      (z : T ⟶ (identityComponent (groupScheme l K)).X),
      Commute ((groupScheme l K).constantPoint g T)
        (z ≫ (identityComponentι (groupScheme l K)).hom.hom)) : g = 1 := by
  let M := (rationalMatrix K g).val
  have hT : ∀ (R : Type u) [CommRing R] [Algebra K R] (τ : ULift.{u} l → Rˣ),
      M.map (algebraMap K R) * Matrix.diagonal (fun i => (torusWeights τ i : R)) =
        Matrix.diagonal (fun i => (torusWeights τ i : R)) * M.map (algebraMap K R) := by
    intro R _ _ τ
    let A := CommAlgCat.of (CommRingCat.of K) R
    let t := GeneralLinear.affineTorusPoint (R := CommRingCat.of K) τ
    have h := (hc ((algSpec (CommRingCat.of K)).obj (op A))
      (t ≫ (identityTorus l K).hom.hom)).eq
    rw [Category.assoc, ← Grp.comp_hom_hom, identityTorus_comp] at h
    have hm := congrArg (fun x => (affineMatrix K A x).val) h
    simp only [_root_.map_mul, Units.val_mul] at hm
    rw [affineMatrix_constantPoint_rational, affineMatrix_diagonalTorus,
      GeneralLinear.torusCoords_affineTorusPoint] at hm
    exact hm
  have hS (a : l ⊕ l) : M * shortMatrix a 1 = shortMatrix a 1 * M := by
    let A := CommAlgCat.of (CommRingCat.of K) K
    let T := (algSpec (CommRingCat.of K)).obj (op A)
    let t := additiveAffinePoint K A 1
    obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.mp
      (SymplecticMatrix.comp_mem_range_identityComponentι (shortMap K a) t)
    have h := (hc T z).eq
    rw [hz] at h
    have hm := congrArg (fun x => (affineMatrix K A x).val) h
    simp only [_root_.map_mul, Units.val_mul] at hm
    rw [affineMatrix_constantPoint_rational, affineMatrix_shortMap] at hm
    change M.map (algebraMap K K) * shortMatrix a 1 =
      shortMatrix a 1 * M.map (algebraMap K K) at hm
    simpa only [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id] using hm
  have hs := matrix_eq_scalar_of_commutes_torus_short M hT hS
  let T₀ := Over.mk (𝟙 (Spec (CommRingCat.of K)))
  have hbase : (pointMatrix K T₀ g).val =
      Matrix.diagonal (fun _ : Index l => scalarMap T₀ (M (Sum.inl ()) (Sum.inl ()))) := by
    have h := pointMatrix_constantPoint_rational K g T₀
    have hconst : (groupScheme l K).constantPoint g T₀ = g := by
      change (𝟙 T₀) ≫ g = g
      exact Category.id_comp g
    rw [hconst] at h
    have hm := congrArg Units.val h
    change (pointMatrix K T₀ g).val = M.map (scalarMap T₀) at hm
    rw [hs] at hm
    simpa using hm
  have hQ := (pointMatrix_equations K T₀ g).1
  have hdet := (pointMatrix_equations K T₀ g).2
  rw [hbase] at hQ hdet
  have hmat := scalar_matrix_eq_one (l := l) (scalarMap T₀) _ hQ hdet
  apply pointMatrix_injective K T₀
  rw [_root_.map_one]
  apply Units.ext
  exact hbase.trans hmat

end Langlands.GroupScheme.OddOrthogonalMatrix
