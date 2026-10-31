import Langlands.AlgebraicGeometry.Picard.PoincareDiagonalClasses
import Langlands.AlgebraicGeometry.Picard.PoincareSliceSymmetryBaseChange
import Langlands.AlgebraicGeometry.Picard.MumfordUnit
import Langlands.AlgebraicGeometry.FactorizationOfGlobalFunctionsProof

/-! # The Mumford map of the diagonal Poincaré pullback of a polarization -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

/-- A map from an abelian scheme to an abelian scheme which is trivial at the unit and at
enough points to cover every point of the source is trivial (rigidity). -/
lemma eq_one_of_forall_point {S : Scheme.{u}} (A D : AbelianScheme S) (d : A.X ⟶ D.X)
    (hu : (1 : Over.mk (𝟙 S) ⟶ A.X) ≫ d = 1)
    (hpts : ∀ x : A.X.left, ∃ (T : Over S) (t : T ⟶ A.X) (z : T.left),
      t.left z = x ∧ t ≫ d = 1) :
    d = 1 := by
  have hu' : unitSection A ≫ d.left = unitSection D := congrArg (fun f ↦ f.left) hu
  have hpt : ∀ y : A.X.left, d.left y = (unitSection A ≫ d.left) (A.X.hom y) := by
    intro y
    obtain ⟨T, t, z, rfl, ht⟩ := hpts y
    have h1 : t.left ≫ d.left = T.hom ≫ unitSection D := by
      rw [← Over.comp_left, ht, unitPoint_left]
    rw [hu', ← Scheme.Hom.comp_apply, h1, ← Over.w t]
    rfl
  apply Over.OverMorphism.ext
  rw [unitPoint_left D A.X, ← hu']
  exact Langlands.AlgebraicGeometry.factorizationOfGlobalFunctions A.X.left S D.X.left A.X.hom
    (unitSection A) d.left (unitSection_comp A)
    (Langlands.AlgebraicGeometry.smoothProperConnectedGlobalFunctions A.X.left S A.X.hom
      inferInstance inferInstance inferInstance) hpt

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable (square : MumfordBundlePicardZeroStatement.{u})
variable (universality : PicardZeroUniversalBaseChangeStatement.{u})
variable {S : Scheme.{u}} (A : AbelianScheme S)
variable (hA : HasDualScheme A) (geometryA : DualSchemeGeometry A hA)
variable (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
variable (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
  structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
variable (stability : PicardZeroPullbackStatement.{u})
variable (composition : PullbackTensorCompositionStatement.{u})
variable (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
variable (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
variable (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
variable (symmetry : PullbackTensorSymmetryStatement.{u})

/-- For a polarization `λ`, every point `x` of `A` is the image of a point `t` of `A` over a
one-point scheme at which the Poincaré slices of `λ` are symmetric. The point comes from a
geometric point at `x` followed by the field extension in the polarization condition. -/
lemma IsPolarization.exists_poincareSliceSymmetric
    {lam : A ⟶ dualAbelianSchemeFromEvaluation A hA geometryA preservation MA evaluationA
      stability composition unitCoherence associativity comparison symmetry}
    (h : IsPolarization preservation square universality A hA geometryA MA evaluationA
      stability composition unitCoherence associativity comparison symmetry lam)
    (x : A.X.left) :
    ∃ (T : Over S) (_ : Unique T.left) (t : T ⟶ A.X) (z : T.left),
      t.left z = x ∧ PoincareSliceSymmetric A hA (groupHom lam).hom.hom t := by
  let xK : Spec (.of (AlgebraicClosure (A.X.left.residueField x))) ⟶ A.X.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (A.X.left.residueField x)
      (AlgebraicClosure (A.X.left.residueField x)))) ≫ A.X.left.fromSpecResidueField x
  let s : Spec (.of (AlgebraicClosure (A.X.left.residueField x))) ⟶ S := xK ≫ A.X.hom
  obtain ⟨K', _, φ, L2, B2, evB2, M2, ev2, -, hf2⟩ :=
    h.2 (AlgebraicClosure (A.X.left.residueField x)) s
  let b : Spec (.of K') ⟶ Spec (.of (AlgebraicClosure (A.X.left.residueField x))) :=
    Spec.map (CommRingCat.ofHom φ)
  let A1 := (baseChange s).obj A
  let hA1 := hasDualScheme_baseChange universality s A hA
  let t1 : Spec (.of (AlgebraicClosure (A.X.left.residueField x))) ⟶ A1.X.left :=
    pullback.lift xK (𝟙 _) (Category.id_comp s).symm
  have e3 : t1 ≫ A1.X.hom = 𝟙 _ := pullback.lift_snd _ _ _
  let t2 : Over.mk (𝟙 (Spec (.of K'))) ⟶ ((baseChange b).obj A1).X :=
    Over.homMk (pullback.lift (b ≫ t1 : Spec (.of K') ⟶ A1.X.left) (𝟙 _)
      ((Category.assoc _ _ _).trans ((congrArg (b ≫ ·) e3).trans
        ((Category.comp_id b).trans (Category.id_comp b).symm))))
      (pullback.lift_snd _ _ _)
  have hs2 : PoincareSliceSymmetric ((baseChange b).obj A1)
      (hasDualScheme_baseChange universality b A1 hA1)
      (dualBaseChangeMap A1 hA1 universality b
        (dualBaseChangeMap A hA universality s (groupHom lam).hom.hom)) t2 := by
    rw [hf2]
    exact poincareSliceSymmetric_mumfordSchemeMap preservation _ L2 B2 evB2 M2 ev2 square _ t2
  have hs1 := poincareSliceSymmetric_of_baseChange universality b A1 hA1 _ t2 hs2
  have hs0 := poincareSliceSymmetric_of_baseChange universality s A hA _ _ hs1
  have hU : Unique ((Over.map s).obj ((Over.map b).obj (Over.mk (𝟙 (Spec (.of K')))))).left :=
    inferInstanceAs (Unique (Spec (.of K')))
  refine ⟨_, hU, _, default, ?_, hs0⟩
  have ht : ((Over.map s).map ((Over.map b).map t2 ≫ baseChangeParameterMap b A1.X) ≫
      baseChangeParameterMap s A.X).left = b ≫ xK := by
    have e1 : t2.left ≫ pullback.fst A1.X.hom b = b ≫ t1 := pullback.lift_fst _ _ _
    have e2 : t1 ≫ pullback.fst A.X.hom s = xK := pullback.lift_fst _ _ _
    exact (congrArg (· ≫ pullback.fst A.X.hom s) e1).trans
      ((Category.assoc _ _ _).trans (congrArg (b ≫ ·) e2))
  rw [ht]
  simp only [xK, Scheme.Hom.comp_apply]
  exact Scheme.fromSpecResidueField_apply _ _

section Diagonal

variable (lam0 : A.X ⟶ (dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry).X)
  [IsMonHom lam0]
variable (B : LineBundle S)
variable (evaluationB : tensorObj ((Scheme.Modules.pullback (unitSection A)).obj
  (poincareDiagonalBundle A hA lam0).obj) B.obj ≅ structureSheaf S)
variable (M : LineBundle A.X.left)
variable (evaluation : tensorObj (LineBundle.normalize preservation A.X.hom (unitSection A)
  (unitSection_comp A) (poincareDiagonalBundle A hA lam0) B evaluationB).obj.carrier M.obj ≅
    structureSheaf A.X.left)

/-- If every point of `A` is hit by a point over a one-point scheme with symmetric Poincaré
slices for `λ`, the Mumford map of `(1, λ)^* P` is `λ * λ`. -/
lemma mumfordSchemeMap_poincareDiagonal_eq_mul
    (hpts : ∀ x : A.X.left, ∃ (T : Over S) (_ : Unique T.left) (t : T ⟶ A.X) (z : T.left),
      t.left z = x ∧ PoincareSliceSymmetric A hA lam0 t) :
    mumfordSchemeMapOfLineBundle preservation A (poincareDiagonalBundle A hA lam0) B
        evaluationB M evaluation square hA =
      (lam0 * lam0 : A.X ⟶ (dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
        evaluationA stability composition unitCoherence associativity comparison
        symmetry).X) := by
  have hunit : η[A.X] ≫ mumfordSchemeMapOfLineBundle preservation A
      (poincareDiagonalBundle A hA lam0) B evaluationB M evaluation square hA =
      η[(dualAbelianSchemeFromEvaluation A hA geometryA preservation MA evaluationA
        stability composition unitCoherence associativity comparison symmetry).X] :=
    mumfordSchemeMap_unit A preservation _ M evaluation stability square hA
  have hstar := @comp_mumfordSchemeMap_poincareDiagonal preservation S A hA geometryA MA
    evaluationA stability composition unitCoherence associativity comparison symmetry lam0 _
    B evaluationB M evaluation square
  obtain ⟨g, hg⟩ : ∃ g : A.X ⟶ (dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
      evaluationA stability composition unitCoherence associativity comparison symmetry).X,
      g = mumfordSchemeMapOfLineBundle preservation A (poincareDiagonalBundle A hA lam0) B
        evaluationB M evaluation square hA := ⟨_, rfl⟩
  rw [← hg] at hunit hstar ⊢
  refine (div_eq_one (a := g) (b := lam0 * lam0)).mp (eq_one_of_forall_point A (dualAbelianSchemeFromEvaluation A hA geometryA
    preservation MA evaluationA stability composition unitCoherence associativity comparison
    symmetry) (g / (lam0 * lam0)) ?_ ?_)
  · have h1g : (1 : Over.mk (𝟙 S) ⟶ A.X) ≫ g = 1 :=
      (Category.assoc (SemiCartesianMonoidalCategory.toUnit (Over.mk (𝟙 S))) η[A.X] g).trans
        (congrArg (SemiCartesianMonoidalCategory.toUnit (Over.mk (𝟙 S)) ≫ ·) hunit)
    rw [GrpObj.comp_div, MonObj.comp_mul, MonObj.one_comp lam0, h1g, mul_one, div_one]
  · intro x
    obtain ⟨T, hT, t, z, hz, hsym⟩ := hpts x
    refine ⟨T, t, z, hz, ?_⟩
    rw [GrpObj.comp_div, MonObj.comp_mul]
    exact (div_eq_one (a := t ≫ g)).mpr (hstar t hsym)

end Diagonal

/-- GIT Proposition 6.10: for a relative polarization `λ`, the diagonal Poincaré pullback
`(1, λ)^* P` admits unit-section normalization data, and its Mumford map is `2 λ`. -/
theorem polarizationDiagonalMumford : PolarizationDiagonalMumfordStatement.{u} := by
  intro preservation square universality composition unitCoherence associativity comparison
    symmetry stability S _ A hA geometryA MA evaluationA lam h
  obtain ⟨B, ⟨evaluationB⟩⟩ := LineBundle.exists_tensorObj_iso_structureSheaf
    ((LineBundle.pullback (unitSection A)).obj
      (poincareDiagonalBundle A hA (groupHom lam).hom.hom))
  obtain ⟨M, ⟨evaluation⟩⟩ := LineBundle.exists_tensorObj_iso_structureSheaf
    ((RigidifiedLineBundle.forget _).obj (LineBundle.normalize preservation A.X.hom
      (unitSection A) (unitSection_comp A) (poincareDiagonalBundle A hA (groupHom lam).hom.hom)
      B evaluationB))
  refine ⟨B, evaluationB, M, evaluation, ?_⟩
  have hlam : (groupHom (2 • lam)).hom.hom =
      (groupHom lam).hom.hom * (groupHom lam).hom.hom := by
    rw [two_nsmul]
    rfl
  rw [hlam]
  exact mumfordSchemeMap_poincareDiagonal_eq_mul preservation square A hA geometryA MA
    evaluationA stability composition unitCoherence associativity comparison symmetry
    (groupHom lam).hom.hom B evaluationB M evaluation
    (fun x ↦ h.exists_poincareSliceSymmetric preservation square universality A hA geometryA
      MA evaluationA stability composition unitCoherence associativity comparison symmetry x)

end Langlands.AbelianScheme
