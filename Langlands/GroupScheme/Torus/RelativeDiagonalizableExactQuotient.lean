import Langlands.GroupScheme.Torus.DiagonalizableExactQuotient
import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Langlands.GroupScheme.FppfQuotientComparison
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Exact diagonalizable quotients over an arbitrary scheme -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.RelativeMultiplicativeType

variable (S : Scheme.{u}) {Λ Γ : Type u} [AddCommGroup Λ] [AddCommGroup Γ]
    (p : Λ →+ Γ)

/-- Restriction of characters over an arbitrary base scheme. -/
def diagonalizableMap : diagonalizable S Γ ⟶ diagonalizable S Λ :=
  (GroupScheme.baseChange (Gm.toSpecZ S)).map
    (Diagonalizable.restrictMap (CommRingCat.of (ULift.{u} ℤ)) p)

/-- The exact quotient associated with a character surjection. -/
def diagonalizableExactQuotientMap :
    diagonalizable S Λ ⟶ diagonalizable S p.ker :=
  (GroupScheme.baseChange (Gm.toSpecZ S)).map
    (Diagonalizable.exactQuotientMap (CommRingCat.of (ULift.{u} ℤ)) p)

/-- A subgroup of a finitely generated abelian character group is finitely generated. -/
theorem exactQuotientCharacters_fg [AddGroup.FG Λ] : AddGroup.FG p.ker := by
  have : Module.Finite ℤ Λ := Module.Finite.iff_addGroup_fg.mpr inferInstance
  have : Module.Finite ℤ p.ker :=
    Module.Finite.of_injective p.ker.subtype.toIntLinearMap Subtype.val_injective
  exact Module.Finite.iff_addGroup_fg.mp inferInstance

/-- A character surjection gives a closed inclusion over every scheme. -/
theorem isClosedSubgroup_diagonalizableMap (hp : Function.Surjective p) :
    IsClosedSubgroup (diagonalizableMap S p) := by
  have h : IsClosedSubgroup
      (Diagonalizable.restrictMap (CommRingCat.of (ULift.{u} ℤ)) p) :=
    Diagonalizable.isClosedImmersion_restrictMap _ p hp
  exact h.baseChange (Gm.toSpecZ S)

/-- The exact quotient is affine, without any hypothesis on the base. -/
theorem isAffineHom_diagonalizableExactQuotientMap :
    IsAffineHom (diagonalizableExactQuotientMap S p).hom.hom.left := by
  have h : IsAffineHom
      (Diagonalizable.exactQuotientMap (CommRingCat.of (ULift.{u} ℤ)) p).hom.hom.left := by
    change IsAffineHom
      (Diagonalizable.restrictMap (CommRingCat.of (ULift.{u} ℤ)) p.ker.subtype).hom.hom.left
    rw [Diagonalizable.restrictMap_left]
    exact isAffineHom_of_isAffine
      (X := Spec (CommRingCat.of (AddMonoidAlgebra (ULift.{u} ℤ) Λ)))
      (Y := Spec (CommRingCat.of (AddMonoidAlgebra (ULift.{u} ℤ) p.ker))) _
  exact MorphismProperty.overPullbackMap (P := @IsAffineHom) (Gm.toSpecZ S)
    (Diagonalizable.exactQuotientMap (CommRingCat.of (ULift.{u} ℤ)) p).hom.hom
    h

/-- The full quotient of `D_S(Λ)` by the included `D_S(Γ)` is `D_S(ker p)`. -/
theorem isFppfQuotient_diagonalizableExactQuotientMap [AddGroup.FG Λ]
    (hp : Function.Surjective p) :
    RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (diagonalizableMap S p))
      (diagonalizableExactQuotientMap S p) := by
  have : IsNoetherianRing (ULift.{u} ℤ) :=
    isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  have h := Diagonalizable.isFppfQuotient_exactQuotientMap
    (CommRingCat.of (ULift.{u} ℤ)) p hp
  change RelativeRoot.IsFppfQuotient
    (SubgroupFunctor.range ((GroupScheme.baseChange (Gm.toSpecZ S)).map
      (Diagonalizable.restrictMap (CommRingCat.of (ULift.{u} ℤ)) p)))
    ((GroupScheme.baseChange (Gm.toSpecZ S)).map
      (Diagonalizable.exactQuotientMap (CommRingCat.of (ULift.{u} ℤ)) p))
  rw [SubgroupFunctor.range_baseChangeHom]
  exact h.baseChange (Gm.toSpecZ S)

/-- The quotient has finitely generated characters and hence multiplicative type. -/
theorem isMultiplicativeType_diagonalizableExactQuotient [AddGroup.FG Λ] :
    IsMultiplicativeType (diagonalizable S p.ker) := by
  have := exactQuotientCharacters_fg p
  exact IsMultiplicativeType.of_isDiagonalizable
    ⟨p.ker, inferInstance, inferInstance, ⟨Iso.refl _⟩⟩

end Langlands.GroupScheme.RelativeMultiplicativeType
