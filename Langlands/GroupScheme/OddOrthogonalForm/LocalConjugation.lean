import Langlands.GroupScheme.OddOrthogonalForm.GaloisStage
import Langlands.GroupScheme.EvenOrthogonalForm.AutomorphismCocycle

/-! # Exact isometric conjugators of local automorphisms of the full odd model -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.OddOrthogonalForm

open OddOrthogonalMatrix
open SpecialLinearInnerForm (pointScalars)

variable {K : Type u} [Field K] {N : Type u} [Field N] [Algebra K N] {n : ℕ}

/-- Matrices of points of the original full split odd group. -/
def splitMatrix {V : Over (Spec (CommRingCat.of K))} (x : V ⟶ (splitGroup K n).X) :
    Matrix (Index (Fin n)) (Index (Fin n)) Γ(V.left, ⊤) := (pointMatrix K V x).val

/-- The full odd model comparison preserves the projected local matrix. -/
theorem splitMatrix_coverPointsEquiv {V : Over (Spec (CommRingCat.of K))}
    (s : V ⟶ ringTest K N)
    (z : LocalGroupIso.coverTest s ⟶
      ((GroupScheme.baseChange (ringTest K N).hom).obj (splitGroup K n)).X) :
    (pointMatrix N (LocalGroupIso.coverTest s)
      (z ≫ (splitBaseChangeIso K N n).hom.hom.hom)).val =
      splitMatrix (LocalGroupIso.coverPointsEquiv (splitGroup K n) s z) := by
  have hb := pointMatrix_baseChangeModelIso_hom (l := Fin n) (algebraBaseMap K N)
    (LocalGroupIso.coverTest s) z
  have hid : ((LocalGroupIso.coverTestIso s).inv.left.appTop).hom =
      RingHom.id Γ(V.left, ⊤) := by
    change (Scheme.Hom.appTop (𝟙 V.left)).hom = _
    rw [Scheme.Hom.id_appTop]
    rfl
  refine (congrArg Units.val hb).trans ?_
  have hr : LocalGroupIso.coverPointsEquiv (splitGroup K n) s z =
      (LocalGroupIso.coverTestIso s).inv ≫
        baseChangePointsEquiv (algebraBaseMap K N) (splitGroup K n) (LocalGroupIso.coverTest s) z := rfl
  rw [splitMatrix, hr, pointMatrix_naturality, hid]
  rfl

/-- The original-field matrix of an actual odd point satisfies the exact defining equations. -/
theorem rationalMatrix_equations
    (g : Over.mk (𝟙 (Spec (CommRingCat.of N))) ⟶ (splitGroup N n).X) :
    OrthogonalMatrix.IsAlt ((rationalMatrix N g).val * formMatrix (Fin n) N *
      (rationalMatrix N g).val.transpose - formMatrix (Fin n) N) ∧ (rationalMatrix N g).val.det = 1 := by
  let A := CommAlgCat.of (CommRingCat.of N) N
  have h := affineMatrix_equations N A
    ((splitGroup N n).constantPoint g ((algSpec (CommRingCat.of N)).obj (Opposite.op A)))
  rw [affineMatrix_constantPoint_rational] at h
  change OrthogonalMatrix.IsAlt
    ((rationalMatrix N g).val.map (algebraMap N N) *
      (formMatrix (Fin n) N).map (algebraMap N N) *
        ((rationalMatrix N g).val.map (algebraMap N N)).transpose -
          (formMatrix (Fin n) N).map (algebraMap N N)) ∧
      ((rationalMatrix N g).val.map (algebraMap N N)).det = 1 at h
  simpa only [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id] using h

/-- The automorphism over the covering field associated with a natural local automorphism. -/
def coverAutomorphism (χ : LocalGroupIso (splitGroup K n) (splitGroup K n) (ringTest K N)) :
    CategoryTheory.Aut (splitGroup N n) :=
  Aut.of ((splitBaseChangeIso K N n).symm ≪≫ χ.toBaseChangeIso ≪≫ splitBaseChangeIso K N n)

/-- The unique actual conjugating point over the covering field. -/
def conjugatorPoint (hn : 2 ≤ n)
    (χ : LocalGroupIso (splitGroup K n) (splitGroup K n) (ringTest K N)) :
    Over.mk (𝟙 (Spec (CommRingCat.of N))) ⟶ (splitGroup N n).X :=
  (fullInnerAutEquiv hn).symm (coverAutomorphism χ)

/-- The actual matrix of that isometric conjugator, with determinant one. -/
def conjugatorMatrix (hn : 2 ≤ n)
    (χ : LocalGroupIso (splitGroup K n) (splitGroup K n) (ringTest K N)) : GL (Index (Fin n)) N :=
  rationalMatrix N (conjugatorPoint hn χ)

/-- It implements the complete covering-field group-scheme automorphism. -/
theorem conjugatorPoint_spec (hn : 2 ≤ n)
    (χ : LocalGroupIso (splitGroup K n) (splitGroup K n) (ringTest K N)) :
    (splitGroup N n).innerIso (conjugatorPoint hn χ) = (coverAutomorphism χ).asIso :=
  fullInnerAutEquiv_symm_spec hn _

/-- The chosen matrix obeys the exact quadratic and norm-one equations. -/
theorem conjugatorMatrix_equations (hn : 2 ≤ n)
    (χ : LocalGroupIso (splitGroup K n) (splitGroup K n) (ringTest K N)) :
    OrthogonalMatrix.IsAlt ((conjugatorMatrix hn χ).val * formMatrix (Fin n) N *
      (conjugatorMatrix hn χ).val.transpose - formMatrix (Fin n) N) ∧
        (conjugatorMatrix hn χ).val.det = 1 :=
  rationalMatrix_equations _

/-- The covering-field scalar map read on the relative test scheme's sections. -/
abbrev sectionScalars {V : Over (Spec (CommRingCat.of K))} (s : V ⟶ ringTest K N) :
    N →+* Γ(V.left, ⊤) := pointScalars s

/-- Every local automorphism is conjugation by the same covering-field isometry
on every relative test scheme. -/
theorem splitMatrix_localAutomorphism (hn : 2 ≤ n)
    (χ : LocalGroupIso (splitGroup K n) (splitGroup K n) (ringTest K N))
    {V : Over (Spec (CommRingCat.of K))} (s : V ⟶ ringTest K N)
    (x : V ⟶ (splitGroup K n).X) :
    splitMatrix (χ.toFun s x) =
      (conjugatorMatrix hn χ).val.map (sectionScalars s) * splitMatrix x *
        ((conjugatorMatrix hn χ)⁻¹).val.map (sectionScalars s) := by
  let c := splitBaseChangeIso K N n
  let α := coverAutomorphism χ
  let y := (LocalGroupIso.coverPointsEquiv (splitGroup K n) s).symm x
  have hα : c.hom.hom.hom ≫ α.asIso.hom.hom.hom = χ.toBaseChangeIso.hom.hom.hom ≫ c.hom.hom.hom := by
    have h : c.hom ≫ α.asIso.hom = χ.toBaseChangeIso.hom ≫ c.hom := by
      simp only [α, coverAutomorphism, c, Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]
    simpa only [Grp.comp_hom_hom] using congrArg (fun f => f.hom.hom) h
  have h1 : (pointMatrix N (LocalGroupIso.coverTest s)
      ((y ≫ c.hom.hom.hom) ≫ α.asIso.hom.hom.hom)).val =
      (conjugatorMatrix hn χ).val.map (scalarMap (LocalGroupIso.coverTest s)) *
        (pointMatrix N (LocalGroupIso.coverTest s) (y ≫ c.hom.hom.hom)).val *
          ((conjugatorMatrix hn χ)⁻¹).val.map (scalarMap (LocalGroupIso.coverTest s)) := by
    dsimp only [α]
    rw [← conjugatorPoint_spec hn χ, comp_innerIso_hom]
    simp only [_root_.map_mul, _root_.map_inv, pointMatrix_constantPoint_rational,
      Units.val_mul]
    rfl
  have h2 := splitMatrix_coverPointsEquiv s y
  have h3 : LocalGroupIso.coverPointsEquiv (splitGroup K n) s y = x :=
    (LocalGroupIso.coverPointsEquiv (splitGroup K n) s).apply_symm_apply x
  rw [h3] at h2
  rw [LocalGroupIso.toFun_eq_coverPointsEquiv χ, ← splitMatrix_coverPointsEquiv]
  have hl : (y ≫ χ.toBaseChangeIso.hom.hom.hom) ≫ c.hom.hom.hom =
      (y ≫ c.hom.hom.hom) ≫ α.asIso.hom.hom.hom := by
    simp only [Category.assoc]
    exact congrArg (fun f => y ≫ f) hα.symm
  rw [hl]
  refine h1.trans ?_
  rw [h2]
  rfl

end Langlands.GroupScheme.OddOrthogonalForm
