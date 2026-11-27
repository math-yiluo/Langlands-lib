import Langlands.TraceFormula.WeilGeneralLinearRationalSigmaEllipticityStatement
import Langlands.TraceFormula.CyclicAdelicTests
import Langlands.TraceFormula.RationalLocalGeneralLinear
import Langlands.GroupScheme.Dynamic.GeneralLinearBaseChange
import Langlands.BaseChange.CyclicNormLemma
import Mathlib.Algebra.Polynomial.Eval.Irreducible

/-! # Rational σ-ellipticity from a finite place of the base -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct Langlands.TraceFormula.PlaceCompletion
open Langlands.Global Langlands.GroupScheme Langlands.BaseChange
open Langlands.TraceFormula.AdelicGroupAutomorphism

namespace Langlands.TraceFormula

/-- An entry after the base-change isomorphism is evaluated on the projected point. -/
private theorem baseChange_affineEntry {R S : CommRingCat.{u}} (b : Spec S ⟶ Spec R)
    (n : ℕ) (A : CommAlgCat S)
    (x : (algSpec S).obj (op A) ⟶
      ((GroupScheme.baseChange b).obj (GroupScheme.GeneralLinear.groupScheme (Fin n) R)).X)
    (i j : Fin n) :
    GroupScheme.GeneralLinear.affinePointsEquiv (Fin n) S A
        (x ≫ (GroupScheme.GeneralLinear.baseChangeIso (Fin n) b).hom.hom.hom) i j =
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom
        ((x.left ≫ pullback.fst (GroupScheme.GeneralLinear.groupScheme (Fin n) R).X.hom b).appTop
          (GroupScheme.GeneralLinear.entrySection (Fin n) R i j)) := by
  let T := (algSpec S).obj (op A)
  let y := x ≫ (GroupScheme.GeneralLinear.baseChangeIso (Fin n) b).hom.hom.hom
  have h := congrArg (fun g : GL (Fin n) A => g i j)
    (Corepresented.map_affineSectionsIso_pointsEquiv (GroupScheme.GeneralLinear.functor (Fin n) S)
      (GroupScheme.GeneralLinear.corepresentableBy (Fin n) S) A y)
  change (Corepresented.affineSectionsIso A).hom.hom.toRingHom
      (GroupScheme.GeneralLinear.pointsEquiv (Fin n) S T y i j) =
      GroupScheme.GeneralLinear.affinePointsEquiv (Fin n) S A y i j at h
  rw [← h, Corepresented.affineSectionsIso_hom_ringHom]
  dsimp only [y]
  rw [GroupScheme.GeneralLinear.pointsEquiv_comp_baseChangeIso_hom,
    GroupScheme.GeneralLinear.pointsEquiv_apply_apply, baseChangePointsEquiv_left]
  rfl

section Coordinates

variable (K L : Type u) [Field K] [Field L] [Algebra K L] (n : ℕ)

set_option hygiene false in
local notation "GLK" => cyclicBaseGroup K n

set_option hygiene false in
local notation "BC" => AffineWeil.unitBaseChange K L GLK

set_option hygiene false in
local notation "GLiso" => GroupScheme.GeneralLinear.baseChangeIso (Fin n) (Spec.algebraMap K L)

private local instance (F : Type u) [Field F] (n : ℕ) :
    IsAffine (cyclicBaseGroup F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

private local instance (F : Type u) [Field F] (n : ℕ) :
    Smooth (cyclicBaseGroup F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

/-- The base-change isomorphism reads the same matrix as the projected ground point. -/
private theorem baseChange_rationalMatrix
    (x : (BC).affinePoints (CommAlgCat.of L L)) :
    GroupScheme.GeneralLinear.affinePointsEquiv (Fin n) (CommRingCat.of L) (CommAlgCat.of L L)
        ((BC).affinePointsTarget (GLiso).hom (CommAlgCat.of L L) x) =
      GroupScheme.GeneralLinear.affinePointsEquiv (Fin n) (CommRingCat.of K) (CommAlgCat.of K L)
        ((affinePointsBaseChangeMulEquiv K L L GLK).symm x) := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  change GroupScheme.GeneralLinear.affinePointsEquiv (Fin n) (CommRingCat.of L) (CommAlgCat.of L L)
      (x ≫ (GLiso).hom.hom.hom) i j =
    GroupScheme.GeneralLinear.affinePointsEquiv (Fin n) (CommRingCat.of K) (CommAlgCat.of K L)
      ((affinePointsBaseChangeMulEquiv K L L GLK).symm x) i j
  rw [baseChange_affineEntry, GroupScheme.GeneralLinear.affinePointsEquiv_entry_evaluation,
    affinePointEvaluation, affinePointsBaseChangeMulEquiv_symm_left]
  rfl

variable [NumberField K] [NumberField L] [FiniteDimensional K L]

/-- The adelic comparison of a principal Weil point is the diagonal image of its rational
matrix in the coordinates used by the local point comparison. -/
private theorem cyclicWeilAdelicMap_rational
    (q : RationalGroupPoints K (cyclicWeilGroup K L n)) :
    cyclicWeilAdelicMap K L n (AdelicGroupPoints.rational K (cyclicWeilGroup K L n) q) =
      AdelicGL.rational L n (rationalWeilGLEquiv K L n q) := by
  let upperPoint := AdelicWeilRestriction.rationalPointsEquiv K L BC q
  have hWeil : AdelicGaloisUnit.weilAdelicEquiv K L GLK
      (AdelicGroupPoints.rational K (cyclicWeilGroup K L n) q) =
      AdelicGroupPoints.rational L BC upperPoint :=
    AdelicWeilRestriction.adelicPointsEquiv_rational K L BC q
  have hMap := DFunLike.congr_fun (AdelicGroupPoints.rational_naturality L BC (GLiso).hom) upperPoint
  simp only [MonoidHom.comp_apply] at hMap
  unfold cyclicWeilAdelicMap
  rw [hWeil, AdelicGroupPoints.map_apply, ← hMap, GeneralLinearGroupPoints.adelicHomeomorph_rational]
  apply congrArg (AdelicGL.rational L n)
  rw [GeneralLinearGroupPoints.rationalEquiv, baseChange_rationalMatrix]
  let groundPoint := AffineWeil.unitGroundPointsEquiv K L GLK (CommAlgCat.of K K) q
  let rid := (Algebra.TensorProduct.rid K L L).toAlgHom
  have hRid : (affinePointsBaseChangeMulEquiv K L L GLK).symm upperPoint =
      (GLK).affinePointMap (CommAlgCat.ofHom (rid.restrictScalars K)) groundPoint := by
    apply (affinePointsBaseChangeMulEquiv K L L GLK).injective
    rw [MulEquiv.apply_symm_apply, ← affinePointsBaseChangeMulEquiv_naturality]
    change (BC).affinePointMap (CommAlgCat.ofHom rid) (AffineWeil.pointsEquiv K L BC K q) =
      (BC).affinePointMap (CommAlgCat.ofHom rid)
        (affinePointsBaseChangeMulEquiv K L (L ⊗[K] K) GLK
          (AffineWeil.unitGroundPointsEquiv K L GLK (CommAlgCat.of K K) q))
    rw [AffineWeil.unitGroundPointsEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  rw [hRid, GroupScheme.affinePointMap_apply, GroupScheme.GeneralLinear.affinePointsEquiv_naturality]
  rfl

end Coordinates

/-- Local σ-ellipticity at a finite place of the base gives rational σ-ellipticity. -/
theorem weilGeneralLinearRationalSigmaEllipticity :
    WeilGeneralLinearRationalSigmaEllipticityStatement.{u} := by
  intro K _ _ L _ _ _ _ σ l hcyc n Φ v r hr hell
  obtain ⟨q, rfl⟩ := hr
  rw [localPointsEquiv_atPlace_rational] at hell
  let δ := rationalWeilGLEquiv K L n q
  refine ⟨δ, cyclicWeilAdelicMap_rational K L n q, ?_⟩
  obtain ⟨baseMatrix, hBase⟩ := (cyclicNormLemma K L σ l n hcyc).1 δ
  obtain ⟨localMatrix, hLocal, hElliptic⟩ := hell
  let i : Place K := .inr v
  let f := algebraMap K (placeCompletion K i)
  let completedMatrix := Matrix.GeneralLinearGroup.map f baseMatrix
  obtain ⟨g, hg⟩ := (cyclicNormLemma (placeCompletion K i) (LocalBaseChangeAlgebra K L i)
      (localGalois K L σ i) l n (isCyclicAlgebra_localGalois K L σ l i hcyc)).2.1
        _ completedMatrix localMatrix (localize_normAssociated K L σ l n i δ baseMatrix hBase)
        hLocal
  have hpoly : localMatrix.val.charpoly = baseMatrix.val.charpoly.map f := by
    rw [← hg]
    simp only [Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj']
    change (baseMatrix.val.map f).charpoly = _
    exact Matrix.charpoly_map baseMatrix.val f
  refine ⟨baseMatrix, hBase, (Polynomial.separable_map f).mp ?_,
    Polynomial.Monic.irreducible_of_irreducible_map f _ baseMatrix.val.charpoly_monic ?_⟩
  · rw [← hpoly]
    exact hElliptic.1
  · rw [← hpoly]
    exact hElliptic.2

end Langlands.TraceFormula
