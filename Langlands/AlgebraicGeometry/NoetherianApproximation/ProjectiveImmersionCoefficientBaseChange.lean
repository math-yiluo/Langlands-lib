import Langlands.AlgebraicGeometry.NoetherianApproximation.ProjectiveImmersionSubalgebraModel
import Langlands.AlgebraicGeometry.PointTopology.AffineFiberProducts

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.NoetherianApproximation

/-- An actual model over a specified coefficient ring retaining the original
projective immersion and original-field Cartesian square. -/
structure ProjectiveImmersionRingModelData
    (R F : Type u) [CommRing R] [Field F] [Algebra R F]
    (X : Scheme.{u}) (n : ℕ) (j : X ⟶ ProjectiveSpace F n) where
  model : Scheme.{u}
  immersion : model ⟶ ProjectiveSpace R n
  isImmersion : IsImmersion immersion
  locallyOfFinitePresentation : LocallyOfFinitePresentation
    (immersion ≫ projectiveSpaceToSpec R n)
  quasiCompact : QuasiCompact (immersion ≫ projectiveSpaceToSpec R n)
  comparison : X ⟶ model
  cartesian : IsPullback comparison (j ≫ projectiveSpaceToSpec F n)
    (immersion ≫ projectiveSpaceToSpec R n) (Spec.algebraMap R F)
  originalImmersion : comparison ≫ immersion = j ≫ ProjSpace.map R F n

set_option backward.isDefEq.respectTransparency.types false in
open P2MW.S_AlgebraicGeometry_ProjSpace_exists_fg_subalgebra_isClosedImmersion_flat_isPullback_comp_map_of_isClosedImmersion_of_flat_of_locallyOfFinitePresentation.ProjFlatDescent25 in
/-- Base change an actual finite coefficient model to a specified intermediate
ring, retaining its original-field square and specified projective map. -/
def projectiveImmersionCoefficientBaseChange
    {F : Type u} [Field F] {X : Scheme.{u}} {n : ℕ}
    {j : X ⟶ ProjectiveSpace F n}
    (D : ProjectiveImmersionSubalgebraModelData F X n j)
    (R : Type u) [CommRing R] [Algebra R F]
    [Algebra D.coefficients R] [IsScalarTower D.coefficients R F] :
    ProjectiveImmersionRingModelData R F X n j := by
  let A := D.coefficients
  let f := D.immersion ≫ projectiveSpaceToSpec A n
  have hbase : Spec.algebraMap R F ≫ Spec.algebraMap A R =
      Spec.algebraMap A F := PointTopology.specAlgebraMap_tower A R F
  let p : X ⟶ pullback f (Spec.algebraMap A R) :=
    pullback.lift D.comparison
      ((j ≫ projectiveSpaceToSpec F n) ≫ Spec.algebraMap R F) (by
        rw [Category.assoc, hbase]
        exact D.cartesian.w)
  have hpfirst : p ≫ pullback.fst f (Spec.algebraMap A R) = D.comparison :=
    pullback.lift_fst _ _ _
  have hpsecond : p ≫ pullback.snd f (Spec.algebraMap A R) =
      (j ≫ projectiveSpaceToSpec F n) ≫ Spec.algebraMap R F :=
    pullback.lift_snd _ _ _
  have hp : IsPullback p (j ≫ projectiveSpaceToSpec F n)
      (pullback.snd f (Spec.algebraMap A R)) (Spec.algebraMap R F) := by
    apply IsPullback.of_right (h₁₂ := pullback.fst f (Spec.algebraMap A R))
      (h₂₂ := Spec.algebraMap A R) (v₁₃ := f) _ hpsecond
      (IsPullback.of_hasPullback f (Spec.algebraMap A R))
    rw [hpfirst, hbase]
    exact D.cartesian
  let aR : ProjectiveSpace R n ⟶ ProjectiveSpace A n := ProjSpace.map A R n
  let rF : ProjectiveSpace F n ⟶ ProjectiveSpace R n := ProjSpace.map R F n
  let aF : ProjectiveSpace F n ⟶ ProjectiveSpace A n := ProjSpace.map A F n
  have hcomp : rF ≫ aR = aF := map_comp_map A R F n
  have hproj : IsPullback aR (projectiveSpaceToSpec R n)
      (projectiveSpaceToSpec A n) (Spec.algebraMap A R) :=
    ProjSpace.isPullback_map A R n
  let m : pullback f (Spec.algebraMap A R) ⟶ ProjectiveSpace R n :=
    hproj.lift (pullback.fst f (Spec.algebraMap A R) ≫ D.immersion)
      (pullback.snd f (Spec.algebraMap A R))
      ((Category.assoc _ _ _).trans
        (pullback.condition (f := f) (g := Spec.algebraMap A R)))
  have hmfirst : m ≫ aR =
      pullback.fst f (Spec.algebraMap A R) ≫ D.immersion :=
    hproj.lift_fst _ _ _
  have hmsecond : m ≫ projectiveSpaceToSpec R n =
      pullback.snd f (Spec.algebraMap A R) := hproj.lift_snd _ _ _
  have hmpb : IsPullback (pullback.fst f (Spec.algebraMap A R)) m
      D.immersion aR := by
    apply IsPullback.of_bot (v₂₁ := projectiveSpaceToSpec R n)
      (v₂₂ := projectiveSpaceToSpec A n) _ hmfirst.symm hproj
    rw [hmsecond]
    exact IsPullback.of_hasPullback f (Spec.algebraMap A R)
  have himm : IsImmersion m := MorphismProperty.of_isPullback hmpb D.isImmersion
  let : LocallyOfFinitePresentation f := D.locallyOfFinitePresentation
  let : QuasiCompact f := D.quasiCompact
  have hloc : LocallyOfFinitePresentation (m ≫ projectiveSpaceToSpec R n) := by
    rw [hmsecond]
    infer_instance
  have hqc : QuasiCompact (m ≫ projectiveSpaceToSpec R n) := by
    rw [hmsecond]
    infer_instance
  have hrF : rF ≫ projectiveSpaceToSpec R n =
      projectiveSpaceToSpec F n ≫ Spec.algebraMap R F :=
    (ProjSpace.isPullback_map R F n).w
  have horiginal : p ≫ m = j ≫ rF := by
    apply hproj.hom_ext
    · calc
        (p ≫ m) ≫ aR =
            (p ≫ pullback.fst f (Spec.algebraMap A R)) ≫ D.immersion := by
          simp only [Category.assoc, hmfirst]
        _ = D.comparison ≫ D.immersion := by rw [hpfirst]
        _ = j ≫ aF := D.originalImmersion
        _ = (j ≫ rF) ≫ aR := by rw [Category.assoc, hcomp]
    · calc
        (p ≫ m) ≫ projectiveSpaceToSpec R n =
            p ≫ pullback.snd f (Spec.algebraMap A R) := by
          rw [Category.assoc, hmsecond]
        _ = (j ≫ projectiveSpaceToSpec F n) ≫ Spec.algebraMap R F := hpsecond
        _ = (j ≫ rF) ≫ projectiveSpaceToSpec R n := by
          simp only [Category.assoc, hrF]
  exact {
    model := pullback f (Spec.algebraMap A R)
    immersion := m
    isImmersion := himm
    locallyOfFinitePresentation := hloc
    quasiCompact := hqc
    comparison := p
    cartesian := by rw [hmsecond]; exact hp
    originalImmersion := horiginal }

end Langlands.AlgebraicGeometry.NoetherianApproximation
