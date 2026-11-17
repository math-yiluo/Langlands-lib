import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeLocality
import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Langlands.GroupScheme.Torus.DiagonalizableGeometry
import Langlands.GroupScheme.Torus.FppfRelativeTorusDescent
import Langlands.AlgebraicGeometry.SchemeFlatPropertyDescent
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Geometry and fppf locality of relative groups of multiplicative type -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.RelativeMultiplicativeType

variable {S : Scheme.{u}} {H : GroupScheme S}

/-- The integral split model is of finite presentation, including for torsion
character groups. Its base is Noetherian and its character group is finitely generated. -/
theorem locallyOfFinitePresentation_integralModel
    (Λ : Type u) [AddCommGroup Λ] [AddGroup.FG Λ] :
    LocallyOfFinitePresentation
      (Diagonalizable.groupScheme (CommRingCat.of (ULift.{u} ℤ)) Λ).X.hom := by
  infer_instance

/-- The split model over any scheme is affine over its base. -/
theorem isAffineHom_diagonalizable (S : Scheme.{u}) (Λ : Type u) [AddCommGroup Λ] :
    IsAffineHom (diagonalizable S Λ).X.hom := by
  change IsAffineHom (pullback.snd _ _)
  exact MorphismProperty.pullback_snd _ _
    (Diagonalizable.isAffineHom (CommRingCat.of (ULift.{u} ℤ)) Λ)

/-- The split model over any scheme is flat over its base. -/
theorem flat_diagonalizable (S : Scheme.{u}) (Λ : Type u) [AddCommGroup Λ] :
    Flat (diagonalizable S Λ).X.hom := by
  have : Flat (Diagonalizable.groupScheme (CommRingCat.of (ULift.{u} ℤ)) Λ).X.hom := by
    change Flat (Spec.map (CommRingCat.ofHom
      (algebraMap (ULift.{u} ℤ) (AddMonoidAlgebra (ULift.{u} ℤ) Λ))))
    apply Flat.SpecMap_iff.mpr
    change (algebraMap (ULift.{u} ℤ) (AddMonoidAlgebra (ULift.{u} ℤ) Λ)).Flat
    rw [RingHom.flat_algebraMap_iff]
    infer_instance
  change Flat (pullback.snd _ _)
  infer_instance

/-- Finite generation of the full character group makes the split model locally
of finite presentation, including when its characters have torsion. -/
theorem locallyOfFinitePresentation_diagonalizable
    (S : Scheme.{u}) (Λ : Type u) [AddCommGroup Λ] [AddGroup.FG Λ] :
    LocallyOfFinitePresentation (diagonalizable S Λ).X.hom := by
  have : LocallyOfFinitePresentation
      (Diagonalizable.groupScheme (CommRingCat.of (ULift.{u} ℤ)) Λ).X.hom := by
    change LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom
      (algebraMap (ULift.{u} ℤ) (AddMonoidAlgebra (ULift.{u} ℤ) Λ))))
    apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mpr
    change (algebraMap (ULift.{u} ℤ) (AddMonoidAlgebra (ULift.{u} ℤ) Λ)).FinitePresentation
    rw [RingHom.finitePresentation_algebraMap]
    exact Algebra.FinitePresentation.of_finiteType.mp inferInstance
  change LocallyOfFinitePresentation (pullback.snd _ _)
  infer_instance

/-- The split model is commutative over its actual base scheme. -/
theorem isCommMonObj_diagonalizable (S : Scheme.{u}) (Λ : Type u) [AddCommGroup Λ] :
    IsCommMonObj (diagonalizable S Λ).X := by
  infer_instance

/-- A diagonalizable group is affine over its base. -/
theorem IsDiagonalizable.isAffineHom (hH : IsDiagonalizable H) :
    IsAffineHom H.X.hom := by
  obtain ⟨Λ, _, _, ⟨e⟩⟩ := hH
  have := isAffineHom_diagonalizable S Λ
  rw [← Over.w e.hom.hom.hom]
  infer_instance

/-- A diagonalizable group is flat over its base. -/
theorem IsDiagonalizable.flat (hH : IsDiagonalizable H) : Flat H.X.hom := by
  obtain ⟨Λ, _, _, ⟨e⟩⟩ := hH
  have := flat_diagonalizable S Λ
  rw [← Over.w e.hom.hom.hom]
  infer_instance

/-- A diagonalizable group is locally of finite presentation over its base. -/
theorem IsDiagonalizable.locallyOfFinitePresentation (hH : IsDiagonalizable H) :
    LocallyOfFinitePresentation H.X.hom := by
  obtain ⟨Λ, _, _, ⟨e⟩⟩ := hH
  have := locallyOfFinitePresentation_diagonalizable S Λ
  rw [← Over.w e.hom.hom.hom]
  infer_instance

/-- A group of multiplicative type is affine over its base. -/
theorem IsMultiplicativeType.isAffineHom (hH : IsMultiplicativeType H) :
    IsAffineHom H.X.hom := by
  obtain ⟨𝒰, h𝒰⟩ := hH
  have : MorphismProperty.IsLocalAtTarget (@IsAffineHom : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
    Langlands.AlgebraicGeometry.FppfLocal.isLocalAtTarget_fppfPrecoverage _
  let 𝒱 : Scheme.Cover Scheme.fppfPrecoverage S := 𝒰
  exact MorphismProperty.IsLocalAtTarget.of_zeroHypercover 𝒱 fun i => (h𝒰 i).isAffineHom

/-- A group of multiplicative type is flat over its base. -/
theorem IsMultiplicativeType.flat (hH : IsMultiplicativeType H) : Flat H.X.hom := by
  obtain ⟨𝒰, h𝒰⟩ := hH
  have : MorphismProperty.IsLocalAtTarget (@Flat : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
    Langlands.AlgebraicGeometry.FppfLocal.isLocalAtTarget_fppfPrecoverage _
  let 𝒱 : Scheme.Cover Scheme.fppfPrecoverage S := 𝒰
  exact MorphismProperty.IsLocalAtTarget.of_zeroHypercover 𝒱 fun i => (h𝒰 i).flat

/-- A group of multiplicative type is locally of finite presentation over its base. -/
theorem IsMultiplicativeType.locallyOfFinitePresentation (hH : IsMultiplicativeType H) :
    LocallyOfFinitePresentation H.X.hom := by
  obtain ⟨𝒰, h𝒰⟩ := hH
  have : MorphismProperty.IsLocalAtTarget
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
    Langlands.AlgebraicGeometry.FppfLocal.isLocalAtTarget_fppfPrecoverage _
  let 𝒱 : Scheme.Cover Scheme.fppfPrecoverage S := 𝒰
  exact MorphismProperty.IsLocalAtTarget.of_zeroHypercover 𝒱
    fun i => (h𝒰 i).locallyOfFinitePresentation

/-- Relative multiplicative-type groups are separated over the base. -/
theorem IsMultiplicativeType.isSeparated (hH : IsMultiplicativeType H) :
    IsSeparated H.X.hom := by
  let := hH.isAffineHom
  infer_instance

/-- Relative multiplicative-type groups are quasi-compact over the base. -/
theorem IsMultiplicativeType.quasiCompact (hH : IsMultiplicativeType H) :
    QuasiCompact H.X.hom := by
  let := hH.isAffineHom
  infer_instance

end Langlands.GroupScheme.RelativeMultiplicativeType
