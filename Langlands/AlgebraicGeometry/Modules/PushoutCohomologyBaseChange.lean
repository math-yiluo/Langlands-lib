import Langlands.AlgebraicGeometry.Modules.CohomologyBaseChangeZero
import Langlands.AlgebraicGeometry.Modules.PushoutAffineSectionsBaseChange
import Langlands.AlgebraicGeometry.Modules.AffinePullbackQuasicoherent
import Langlands.AlgebraicGeometry.Modules.AffineQuasicoherentCohomologyVanishingProof

/-! # Canonical cohomology base change over an algebra pushout -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct ChangeOfRings

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

variable (R S A B : CommRingCat.{u})
  [Algebra R S] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra S B]
  [IsScalarTower R A B] [IsScalarTower R S B]

/-- The spectra of a compatible square of algebra structures form a
commutative square. -/
lemma affineAlgebraSquare_comm :
    Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap S B)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact congrArg CommRingCat.ofHom
    ((IsScalarTower.algebraMap_eq R A B).symm.trans
      (IsScalarTower.algebraMap_eq R S B))

/-- The ordinary sections construction on this square is the explicit
affine sections map induced by the pullback unit. -/
lemma sectionsBaseChangeMap_affineAlgebraSquare (M : (Spec A).Modules) :
    sectionsBaseChangeMap (CommRingCat.ofHom (algebraMap R S))
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap S B)))
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (affineAlgebraSquare_comm R S A B) M =
        Langlands.Scheme.Modules.pushoutAffineSectionsPullbackMap R S A B M := by
  ext x
  rfl

/-- The scalar adjunct is the already constructed explicit affine sections map. -/
lemma scalarSectionsBaseChangeMap_affineAlgebraSquare (M : (Spec A).Modules) :
    scalarSectionsBaseChangeMap (CommRingCat.ofHom (algebraMap R S))
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap S B)))
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (affineAlgebraSquare_comm R S A B) M =
        Langlands.Scheme.Modules.pushoutAffineScalarSectionsMap R S A B M := by
  rw [scalarSectionsBaseChangeMap, sectionsBaseChangeMap_affineAlgebraSquare]
  rfl

variable [Algebra.IsPushout R S A B]

/-- For a quasi-coherent module on the affine source of an algebra pushout
square, the actual scalar-linear degree-zero cohomology base-change map is invertible. -/
instance isIso_scalarBaseChangeMap_zero_affinePushout
    (M : (Spec A).Modules) [M.IsQuasicoherent] :
    IsIso (scalarBaseChangeMap (CommRingCat.ofHom (algebraMap R S))
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap S B)))
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (affineAlgebraSquare_comm R S A B) M
      (isZero_higherDirectImage_affinePullback
        (CommRingCat.ofHom (algebraMap A B)) M) 0) := by
  rw [scalarBaseChangeMap_zero, scalarSectionsBaseChangeMap_affineAlgebraSquare]
  infer_instance

/-- For a quasi-coherent module on the affine source of an algebra pushout
square, the actual scalar-linear cohomology base-change map is invertible
in every nonnegative degree. -/
instance isIso_scalarBaseChangeMap_affinePushout
    (M : (Spec A).Modules) [M.IsQuasicoherent] (n : ℕ) :
    IsIso (scalarBaseChangeMap (CommRingCat.ofHom (algebraMap R S))
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap S B)))
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (affineAlgebraSquare_comm R S A B) M
      (isZero_higherDirectImage_affinePullback
        (CommRingCat.ofHom (algebraMap A B)) M) n) := by
  cases n with
  | zero => exact isIso_scalarBaseChangeMap_zero_affinePushout R S A B M
  | succ q =>
    apply IsZero.isIso
    · apply (ModuleCat.extendScalars (algebraMap R S)).map_isZero
      exact (affineQuasicoherentCohomologyVanishing
        (Spec A) inferInstance M inferInstance q).2 R
          (Spec.map (CommRingCat.ofHom (algebraMap R A)))
    · exact (affineQuasicoherentCohomologyVanishing (Spec B) inferInstance
        ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj M)
          inferInstance q).2 S (Spec.map (CommRingCat.ofHom (algebraMap S B)))

/-- Canonical scalar-linear cohomology base change for a quasi-coherent module
on the affine source of an algebra pushout square. -/
def scalarBaseChangeAffinePushoutIso
    (M : (Spec A).Modules) [M.IsQuasicoherent] (n : ℕ) :
    (ModuleCat.extendScalars (algebraMap R S)).obj
        ((relativeCohomology (Spec.map (CommRingCat.ofHom (algebraMap R A))) n).obj M) ≅
      (relativeCohomology (Spec.map (CommRingCat.ofHom (algebraMap S B))) n).obj
        ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj M) :=
  asIso (scalarBaseChangeMap (CommRingCat.ofHom (algebraMap R S))
    (Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (Spec.map (CommRingCat.ofHom (algebraMap S B)))
    (Spec.map (CommRingCat.ofHom (algebraMap A B)))
    (affineAlgebraSquare_comm R S A B) M
    (isZero_higherDirectImage_affinePullback
      (CommRingCat.ofHom (algebraMap A B)) M) n)

@[simp]
lemma scalarBaseChangeAffinePushoutIso_hom
    (M : (Spec A).Modules) [M.IsQuasicoherent] (n : ℕ) :
    (scalarBaseChangeAffinePushoutIso R S A B M n).hom =
      scalarBaseChangeMap (CommRingCat.ofHom (algebraMap R S))
        (Spec.map (CommRingCat.ofHom (algebraMap R A)))
        (Spec.map (CommRingCat.ofHom (algebraMap S B)))
        (Spec.map (CommRingCat.ofHom (algebraMap A B)))
        (affineAlgebraSquare_comm R S A B) M
        (isZero_higherDirectImage_affinePullback
          (CommRingCat.ofHom (algebraMap A B)) M) n := rfl

end Langlands.AlgebraicGeometry.Modules.DerivedSections
