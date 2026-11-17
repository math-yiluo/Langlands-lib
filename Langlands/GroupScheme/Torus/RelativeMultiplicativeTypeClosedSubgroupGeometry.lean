import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Langlands.GroupScheme.Torus.FppfRelativeTorusDescent
import Langlands.AlgebraicGeometry.Morphisms.FppfLocalAtTarget

/-! # Geometry of closed subgroups of relative groups of multiplicative type -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.RelativeMultiplicativeType

variable {S : Scheme.{u}} {H K : GroupScheme S}

/-- The split diagonalizable model is affine over every base scheme. -/
private theorem split_affine (S : Scheme.{u}) (Λ : Type u) [AddCommGroup Λ] :
    IsAffineHom (diagonalizable S Λ).X.hom := by
  change IsAffineHom (pullback.snd _ _)
  exact MorphismProperty.pullback_snd
    (Diagonalizable.groupScheme (CommRingCat.of (ULift.{u} ℤ)) Λ).X.hom
    (Gm.toSpecZ S) (by
      change IsAffineHom (Spec.map _)
      infer_instance)

/-- The split diagonalizable model is commutative over every base scheme. -/
private theorem split_commutative (S : Scheme.{u}) (Λ : Type u) [AddCommGroup Λ] :
    IsCommMonObj (diagonalizable S Λ).X :=
  Functor.isCommMonObj_obj (F := Over.pullback (Gm.toSpecZ S))
    (M := (Diagonalizable.groupScheme (CommRingCat.of (ULift.{u} ℤ)) Λ).X)

/-- An actual diagonalizable presentation gives an affine structure morphism. -/
private theorem diagonalizable_affine (hH : IsDiagonalizable H) :
    IsAffineHom H.X.hom := by
  obtain ⟨Λ, _, _, ⟨e⟩⟩ := hH
  exact isAffineHom_of_over_iso ((Grp.forget _).mapIso e)
    (split_affine S Λ)

/-- An actual diagonalizable presentation gives commutativity. -/
private theorem diagonalizable_commutative (hH : IsDiagonalizable H) :
    IsCommMonObj H.X := by
  obtain ⟨Λ, _, _, ⟨e⟩⟩ := hH
  let : IsCommMonObj (diagonalizable S Λ).X := split_commutative S Λ
  apply (isCommMonObj_iff_isMulCommutative _).2
  intro T
  refine ⟨⟨fun x y => ?_⟩⟩
  apply (isoPointsEquiv e T).injective
  rw [map_mul, map_mul, mul_comm]

/-- Affineness of a group of multiplicative type descends from its fppf split cover. -/
private theorem multiplicativeType_affine (hH : IsMultiplicativeType H) :
    IsAffineHom H.X.hom := by
  obtain ⟨𝒰, h𝒰⟩ := hH
  have : MorphismProperty.IsLocalAtTarget (@IsAffineHom : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
    Langlands.AlgebraicGeometry.FppfLocal.isLocalAtTarget_fppfPrecoverage _
  let 𝒱 : Scheme.Cover Scheme.fppfPrecoverage S := 𝒰
  exact MorphismProperty.IsLocalAtTarget.of_zeroHypercover 𝒱 fun i => diagonalizable_affine (h𝒰 i)

/-- Commutativity of a group of multiplicative type descends from its fppf split cover. -/
private theorem multiplicativeType_commutative (hH : IsMultiplicativeType H) :
    IsCommMonObj H.X := by
  obtain ⟨𝒰, h𝒰⟩ := hH
  exact isCommMonObj_of_fppfCover 𝒰 fun i => diagonalizable_commutative (h𝒰 i)

/-- A closed subgroup of a group of multiplicative type is affine over the base. -/
theorem IsMultiplicativeType.closedSubgroup_isAffineHom
    (hH : IsMultiplicativeType H) (k : K ⟶ H)
    (hk : IsClosedImmersion k.hom.hom.left) : IsAffineHom K.X.hom := by
  let : IsAffineHom H.X.hom := multiplicativeType_affine hH
  let : IsClosedImmersion k.hom.hom.left := hk
  rw [← Over.w k.hom.hom]
  infer_instance

/-- A closed subgroup of a group of multiplicative type is commutative. -/
theorem IsMultiplicativeType.closedSubgroup_isCommMonObj
    (hH : IsMultiplicativeType H) (k : K ⟶ H)
    (hk : IsClosedImmersion k.hom.hom.left) : IsCommMonObj K.X := by
  let : IsCommMonObj H.X := multiplicativeType_commutative hH
  let : IsClosedImmersion k.hom.hom.left := hk
  let : Mono k.hom.hom := Over.mono_of_mono_left _
  apply (isCommMonObj_iff_isMulCommutative _).2
  intro T
  refine ⟨⟨fun x y => ?_⟩⟩
  apply (cancel_mono k.hom.hom).1
  rw [MonObj.mul_comp, MonObj.mul_comp, mul_comm]

/-- The given closed subgroup of a group of multiplicative type, with its
proved commutativity added to the unchanged underlying group scheme. -/
def IsMultiplicativeType.closedSubgroupCommGroupScheme
    (hH : IsMultiplicativeType H) (k : K ⟶ H)
    (hk : IsClosedImmersion k.hom.hom.left) : CommGroupScheme S :=
  { K with comm := hH.closedSubgroup_isCommMonObj k hk }

end Langlands.GroupScheme.RelativeMultiplicativeType
