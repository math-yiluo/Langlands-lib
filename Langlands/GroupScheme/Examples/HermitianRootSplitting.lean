import Langlands.GroupScheme.Examples.HermitianRootExchangeSplitting
import Langlands.GroupScheme.Examples.HermitianRootGroupScheme
import Langlands.GroupScheme.Examples.QuasiSplitUnitarySplitting

/-! # Splitting the actual weighted Hermitian group scheme -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.HermitianRoot.SchemeModel

open SU3Root Langlands.Shimura.AlgebraInvolution.SchemeModel

attribute [local instance] sectionsSAlgebra sectionsScalarTower
  Algebra.TensorProduct.rightAlgebra

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [Algebra.IsQuadraticExtension k L] [Algebra.IsSeparable k L]
  {Middle : Type} [Fintype Middle] [DecidableEq Middle]
  (H : DiagonalForm (fieldInvolution k L) Middle)

/-- The original middle weights included into the sections of an `L`-test. -/
def splittingWeights (T : Over (Spec (CommRingCat.of L))) :
    Middle → restrictedSections k L T :=
  fun i => algebraMap L (restrictedSections k L T) (H.weight i)

/-- The original weight units included into the sections of an `L`-test. -/
def splittingUnits (w : Middle → Lˣ) (T : Over (Spec (CommRingCat.of L))) :
    Middle → (restrictedSections k L T)ˣ :=
  fun i => Units.map (algebraMap L (restrictedSections k L T)).toMonoidHom (w i)

omit [Fintype Middle] [DecidableEq Middle] in
theorem splittingUnits_val {w : Middle → Lˣ}
    (hw : ∀ i, (w i : L) = H.weight i)
    (T : Over (Spec (CommRingCat.of L))) (i : Middle) :
    (splittingUnits k L w T i : restrictedSections k L T) =
      splittingWeights k L H T i :=
  congrArg (algebraMap L (restrictedSections k L T)) (hw i)

/-- The actual tensor coefficient ring splits over every `L`-test scheme. -/
def coefficientSplit (T : Over (Spec (CommRingCat.of L))) :
    SpecialLinear.WeilRoot.tensorAlgebra k L ((Over.map (scalarBaseMap k L)).obj T) ≃+*
      (restrictedSections k L T × restrictedSections k L T) :=
  (QuasiSplitUnitary.tensorSplit (restrictedSections k L T)
    (conjugation k L) (conjugation_ne_one k L)).toRingEquiv

/-- The original scalar conjugation becomes factor exchange. -/
theorem coefficientSplit_bar (T : Over (Spec (CommRingCat.of L)))
    (x : SpecialLinear.WeilRoot.tensorAlgebra k L
      ((Over.map (scalarBaseMap k L)).obj T)) :
    coefficientSplit k L T
        ((SU3Root.SchemeModel.coefficientInvolution k L
          ((Over.map (scalarBaseMap k L)).obj T)).bar x) =
      (Exchange.involution (restrictedSections k L T)).bar (coefficientSplit k L T x) :=
  QuasiSplitUnitary.tensorSplit_scalarConjugation (restrictedSections k L T)
    (conjugation k L) (conjugation_ne_one k L) x

omit [Fintype Middle] [DecidableEq Middle] in
/-- Every Hermitian middle weight has the same image in the two split factors. -/
theorem coefficientSplit_weight (T : Over (Spec (CommRingCat.of L))) (i : Middle) :
    coefficientSplit k L T
        ((tensorForm k L H ((Over.map (scalarBaseMap k L)).obj T)).weight i) =
      (Exchange.form (splittingWeights k L H T)).weight i := by
  change QuasiSplitUnitary.tensorSplit (restrictedSections k L T)
      (conjugation k L) (conjugation_ne_one k L) (H.weight i ⊗ₜ[k] 1) =
    (algebraMap L (restrictedSections k L T) (H.weight i),
      algebraMap L (restrictedSections k L T) (H.weight i))
  rw [QuasiSplitUnitary.tensorSplit_tmul, one_mul, one_mul]
  exact Prod.ext rfl (congrArg (algebraMap L (restrictedSections k L T)) (H.bar_weight i))

variable (w : Middle → Lˣ) (hw : ∀ i, (w i : L) = H.weight i)

/-- Splitting of the actual determinant-one Hermitian tensor matrices. -/
def pointsSplitting (T : Over (Spec (CommRingCat.of L))) :
    specialUnitarySubgroup (tensorForm k L H ((Over.map (scalarBaseMap k L)).obj T)) ≃*
      Matrix.SpecialLinearGroup (Index Middle) (restrictedSections k L T) :=
  (specialUnitaryRingEquiv (coefficientSplit k L T)
    (coefficientSplit_bar k L T) (coefficientSplit_weight k L H T)).trans
      (Exchange.specialUnitaryEquiv (splittingWeights k L H T)
        (splittingUnits k L w T) (splittingUnits_val k L H hw T))

/-- The splitting takes the first split coefficient of the original matrix entrywise. -/
theorem pointsSplitting_val (T : Over (Spec (CommRingCat.of L)))
    (g : specialUnitarySubgroup
      (tensorForm k L H ((Over.map (scalarBaseMap k L)).obj T))) :
    (pointsSplitting k L H w hw T g :
        Matrix (Index Middle) (Index Middle) (restrictedSections k L T)) =
      (g.1 : Matrix (Index Middle) (Index Middle) _).map
        (fun a => (coefficientSplit k L T a).1) := rfl

/-- The inverse splitting recovers the tensor entry from a weighted inverse-transpose pair. -/
theorem pointsSplitting_symm_val (T : Over (Spec (CommRingCat.of L)))
    (g : Matrix.SpecialLinearGroup (Index Middle) (restrictedSections k L T))
    (i j : Index Middle) :
    (((pointsSplitting k L H w hw T).symm g).1 :
        Matrix (Index Middle) (Index Middle) _) i j =
      (coefficientSplit k L T).symm
        (g i j, unitaryTwist (Exchange.baseForm (splittingWeights k L H T))
          (splittingUnits k L w T) (splittingUnits_val k L H hw T) g i j) := rfl

/-- Scalar extension of the actual weighted Hermitian group scheme to `L`. -/
abbrev baseChangeGroupScheme : GroupScheme (Spec (CommRingCat.of L)) :=
  (GroupScheme.baseChange (scalarBaseMap k L)).obj (groupScheme k L H w hw)

/-- All points of the actual scalar extension are the full special-linear matrices. -/
def basePointsEquiv (T : Over (Spec (CommRingCat.of L))) :
    (T ⟶ (baseChangeGroupScheme k L H w hw).X) ≃*
      Matrix.SpecialLinearGroup (Index Middle) Γ(T.left, ⊤) :=
  (GroupScheme.baseChangePointsEquiv (scalarBaseMap k L) (groupScheme k L H w hw) T).trans
    ((pointsEquiv k L H w hw ((Over.map (scalarBaseMap k L)).obj T)).trans
      (pointsSplitting k L H w hw T))

/-- Formula on each entry of every actual base-changed test point. -/
theorem basePointsEquiv_apply (T : Over (Spec (CommRingCat.of L)))
    (x : T ⟶ (baseChangeGroupScheme k L H w hw).X) (i j : Index Middle) :
    (basePointsEquiv k L H w hw T x :
        Matrix (Index Middle) (Index Middle) Γ(T.left, ⊤)) i j =
      (coefficientSplit k L T
        (((pointsEquiv k L H w hw ((Over.map (scalarBaseMap k L)).obj T)
          (GroupScheme.baseChangePointsEquiv (scalarBaseMap k L)
            (groupScheme k L H w hw) T x)).1 :
              Matrix (Index Middle) (Index Middle) _) i j)).1 := rfl

/-- The splitting is natural for every morphism of `L`-test schemes. -/
theorem basePointsEquiv_naturality
    {T T' : Over (Spec (CommRingCat.of L))} (a : T' ⟶ T)
    (x : T ⟶ (baseChangeGroupScheme k L H w hw).X) :
    basePointsEquiv k L H w hw T' (a ≫ x) =
      Matrix.SpecialLinearGroup.map a.left.appTop.hom (basePointsEquiv k L H w hw T x) := by
  apply Subtype.ext
  ext i j
  rw [basePointsEquiv_apply]
  change _ = a.left.appTop
    ((basePointsEquiv k L H w hw T x : Matrix (Index Middle) (Index Middle) _) i j)
  rw [basePointsEquiv_apply, GroupScheme.baseChangePointsEquiv_naturality,
    pointsEquiv_naturality, Matrix.map_apply]
  have key := QuasiSplitUnitary.tensorSplit_coefficientMap_fst
    (R := restrictedSections k L T) (S := restrictedSections k L T')
    (conjugation k L) (conjugation_ne_one k L)
    ((algΓ (CommRingCat.of k)).map ((Over.map (scalarBaseMap k L)).map a)).unop.hom
    (fun e => ((algΓ (CommRingCat.of L)).map a).unop.hom.commutes e)
  exact key _

/-- The actual scalar-extended Hermitian group scheme is the full special-linear group. -/
def splittingIso :
    baseChangeGroupScheme k L H w hw ≅
      SpecialLinear.groupScheme (Index Middle) (CommRingCat.of L) :=
  isoOfPointModels (fun T => Matrix.SpecialLinearGroup (Index Middle) Γ(T.left, ⊤))
    (fun a => Matrix.SpecialLinearGroup.map a.left.appTop.hom)
    (basePointsEquiv k L H w hw)
    (SpecialLinear.pointsEquiv (Index Middle) (CommRingCat.of L))
    (basePointsEquiv_naturality k L H w hw)
    (fun {_ _} a y => SpecialLinear.pointsEquiv_naturality a y)

/-- The actual scheme isomorphism induces the constructed first-coordinate splitting. -/
theorem splittingIso_hom_points (T : Over (Spec (CommRingCat.of L)))
    (x : T ⟶ (baseChangeGroupScheme k L H w hw).X) :
    SpecialLinear.pointsEquiv (Index Middle) (CommRingCat.of L) T
        (x ≫ (splittingIso k L H w hw).hom.hom.hom) =
      basePointsEquiv k L H w hw T x :=
  isoOfPointModels_hom _ _ _ _ (basePointsEquiv_naturality k L H w hw)
    (fun {_ _} a y => SpecialLinear.pointsEquiv_naturality a y) T x

/-- The inverse scheme isomorphism induces the inverse point splitting. -/
theorem splittingIso_inv_points (T : Over (Spec (CommRingCat.of L)))
    (y : T ⟶ (SpecialLinear.groupScheme (Index Middle) (CommRingCat.of L)).X) :
    basePointsEquiv k L H w hw T (y ≫ (splittingIso k L H w hw).inv.hom.hom) =
      SpecialLinear.pointsEquiv (Index Middle) (CommRingCat.of L) T y :=
  isoOfPointModels_inv _ _ _ _ (basePointsEquiv_naturality k L H w hw)
    (fun {_ _} a y => SpecialLinear.pointsEquiv_naturality a y) T y

end Langlands.GroupScheme.HermitianRoot.SchemeModel
