import Langlands.GroupScheme.SimplyConnected.CenterCharacterQuotient
import Langlands.GroupScheme.Adjoint.Quotient
import Langlands.GroupScheme.Reductive.GroundFieldRadical
import Langlands.GroupScheme.BaseChangeReflection

/-! # Trivial centre from trivial geometric centre characters -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

/-- Every point of a diagonalizable group scheme with trivial character group is the
identity. -/
theorem Diagonalizable.points_eq_one_of_subsingleton (R : CommRingCat.{u}) (Λ : Type u)
    [AddCommGroup Λ] [Subsingleton Λ] (T : Over (Spec R))
    (x : T ⟶ (Diagonalizable.groupScheme R Λ).X) : x = 1 := by
  let P := Corepresented.pointsEquiv (Diagonalizable.functor R Λ)
    (Diagonalizable.grpCorepresentation R Λ) T
  have hs : Subsingleton (Multiplicative Λ →* (((algΓ R).obj T).unop)ˣ) :=
    ⟨fun a b => MonoidHom.ext fun m => by rw [Subsingleton.elim m 1, map_one, map_one]⟩
  exact P.injective (hs.elim (P x) (P 1))

namespace TitsIndexData

variable {K : Type u} [Field K] {G : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G)

local notation "Ω" => SeparableClosure K
local notation "BC" => CommGroupScheme.baseChange (algebraBaseMap K Ω)

/-- If the full centre has no nontrivial character over the separable closure, then
its base change to the separable closure has only the identity as a point. -/
theorem toralCenter_baseChange_points_eq_one
    (h : Subsingleton (characterLattice ((BC).obj d.toralCenter.group)))
    (T : Over (Spec (CommRingCat.of Ω))) (x : T ⟶ ((BC).obj d.toralCenter.group).X) :
    x = 1 := by
  obtain ⟨Λ, _, _, ⟨eZ⟩⟩ := exists_diagonalizableIso_of_isClosedSubgroup_splitTorus
    d.pinning.isSplitTorus (CommGroupScheme.groupHom ((BC).map d.toralCenter.torusMap))
    (d.toralCenter_isClosedSubgroup.baseChange (algebraBaseMap K Ω))
  let jZ := CommGroupScheme.isoOfGroupIso eZ
  let ΦZ := (DiagonalizableCharacter.evalCharacterEquiv Ω Λ).trans
    (characterLattice.congr jZ).symm
  have hΛ : Subsingleton Λ := ΦZ.injective.subsingleton
  have hy := Diagonalizable.points_eq_one_of_subsingleton (CommRingCat.of Ω) Λ T
    (x ≫ eZ.hom.hom.hom)
  have hinv : eZ.hom.hom.hom ≫ eZ.inv.hom.hom = 𝟙 _ := by
    rw [← Grp.comp_hom_hom, Iso.hom_inv_id, Grp.id_hom_hom]
  calc x = (x ≫ eZ.hom.hom.hom) ≫ eZ.inv.hom.hom := by
        rw [Category.assoc, hinv, Category.comp_id]
    _ = 1 := by rw [hy, MonObj.one_comp]

/-- If the full centre has no nontrivial character over the separable closure, then
every point of the toral centre over the ground field is the identity. -/
theorem toralCenter_points_eq_one
    (h : Subsingleton (characterLattice ((BC).obj d.toralCenter.group)))
    (T : Over (Spec (CommRingCat.of K))) (x : T ⟶ d.toralCenter.group.X) : x = 1 := by
  obtain ⟨hs, hf, hq⟩ := fieldExtension_fpqc K Ω
  let b := algebraBaseMap K Ω
  have hF : (⊤ : SubgroupFunctor d.toralCenter.group.toGrp).baseChange b = ⊥ := by
    rw [SubgroupFunctor.top_baseChange]
    apply SubgroupFunctor.ext
    intro T'
    apply le_antisymm ?_ bot_le
    intro y _
    exact d.toralCenter_baseChange_points_eq_one h T' y
  have hbot := SubgroupFunctor.eq_bot_of_baseChange_eq_bot b hF
  have hx : x ∈ (⊤ : SubgroupFunctor d.toralCenter.group.toGrp).carrier T :=
    Subgroup.mem_top x
  rw [hbot] at hx
  exact hx

/-- If the full centre has no nontrivial character over the separable closure, then
every central point of the group is the identity. -/
theorem center_points_eq_one
    (h : Subsingleton (characterLattice ((BC).obj d.toralCenter.group)))
    (T : Over (Spec (CommRingCat.of K))) (x : T ⟶ G.X) (hx : x ∈ (center G).carrier T) :
    x = 1 := by
  rw [← d.toralCenter.isCenter.2, SubgroupFunctor.mem_range] at hx
  obtain ⟨y, rfl⟩ := hx
  rw [d.toralCenter_points_eq_one h T y, MonObj.one_comp]

/-- If the full centre has no nontrivial character over the separable closure, then
the identity homomorphism kills the centre. -/
theorem killsCenter_id
    (h : Subsingleton (characterLattice ((BC).obj d.toralCenter.group))) :
    KillsCenter (𝟙 G) := by
  intro T x hx
  rw [Grp.id_hom_hom, Category.comp_id]
  exact d.center_points_eq_one h T x hx

end TitsIndexData

namespace IsAdjointQuotient

variable {k : Type u} [Field k] {G A : GroupScheme (Spec (CommRingCat.of k))}

/-- An adjoint quotient of a group whose identity homomorphism kills the centre is an
isomorphism. -/
theorem isIso_of_killsCenter_id {q : G ⟶ A} (hq : IsAdjointQuotient q)
    (h : KillsCenter (𝟙 G)) : IsIso q := by
  refine ⟨hq.desc (𝟙 G) h, hq.comp_desc _ _, hq.hom_ext ?_⟩
  rw [← Category.assoc, hq.comp_desc, Category.id_comp, Category.comp_id]

end IsAdjointQuotient

end Langlands.GroupScheme
