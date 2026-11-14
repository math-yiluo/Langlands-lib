import Langlands.GroupScheme.Rational.UnitriangularCongruence
import Langlands.GroupScheme.IntegralModel.CongruenceProP
import Langlands.GroupTheory.ProPCompactSubgroups

/-! # Compact subgroups of local unipotent rational points are pro-p -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory AlgebraicGeometry Topology
open Langlands.AlgebraicGeometry.PointTopology Langlands.Cohomology
open scoped CategoryTheory.MonObj Matrix ValuativeRel

namespace Langlands.GroupScheme

namespace GeneralLinear

variable {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalRing F]

local instance (n : ℕ) :
    IsAffine (groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  isAffine_groupScheme (Fin n) (CommRingCat.of F)

/-- The original rational matrix equivalence preserves the canonical topology. -/
def rationalPointsMatrixHomeomorph (n : ℕ) :
    letI : TopologicalSpace (rationalPoints (groupScheme (Fin n) (CommRingCat.of F))) :=
      rationalPointTopology F (groupScheme (Fin n) (CommRingCat.of F)).X
    rationalPoints (groupScheme (Fin n) (CommRingCat.of F)) ≃ₜ* GL (Fin n) F := by
  let P := groupScheme (Fin n) (CommRingCat.of F)
  let : IsAffine P.X.left := isAffine_groupScheme (Fin n) (CommRingCat.of F)
  let : TopologicalSpace (rationalPoints P) := rationalPointTopology F P.X
  let : TopologicalSpace (P.affinePoints (CommAlgCat.of (CommRingCat.of F) F)) :=
    P.affinePointsTopologicalSpace _
  let e := (rationalPointsAffineHomeomorph P).trans
    (affinePointsHomeomorph (Fin n) (CommRingCat.of F)
      (CommAlgCat.of (CommRingCat.of F) F)).toHomeomorph
  have he (g : rationalPoints P) : rationalPointsEquiv n (CommRingCat.of F) g = e g := by
    apply Units.ext
    ext i j
    rw [rationalPointsEquiv_apply_apply]
    change _ = (affinePointsHomeomorph (Fin n) (CommRingCat.of F)
      (CommAlgCat.of (CommRingCat.of F) F) (rationalPointsAffineHomeomorph P g)) i j
    rw [affinePointsHomeomorph_apply, affinePointsEquiv_entry_evaluation]
    change _ = (Scheme.ΓSpecIso (CommRingCat.of F)).hom
      ((rationalPointsAffineHomeomorph P g).left.appTop _)
    rw [rationalPointsAffineHomeomorph_left]
    rfl
  let h := (rationalPointsEquiv n (CommRingCat.of F)).toEquiv.toHomeomorphOfIsInducing
    (show IsInducing (rationalPointsEquiv n (CommRingCat.of F)) from by
      convert e.isInducing using 1
      funext g
      exact he g)
  exact
    { toMulEquiv := rationalPointsEquiv n (CommRingCat.of F)
      continuous_toFun := h.continuous
      continuous_invFun := h.symm.continuous }

end GeneralLinear

section Unitriangular

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {Γ : Type v} [Group Γ] [TopologicalSpace Γ] {n : ℕ}

/-- Every compact subgroup topologically embedded as upper unitriangular matrices
is pro-p for the actual residue characteristic and its original topology. -/
theorem isProPSubgroup_of_isCompact_unitriangular
    (φ : Γ →* GL (Fin n) F) (hφ : IsEmbedding φ)
    (hdiag : ∀ x i, (φ x : Matrix (Fin n) (Fin n) F) i i = 1)
    (hlow : ∀ x i j, j < i → (φ x : Matrix (Fin n) (Fin n) F) i j = 0)
    (K : Subgroup Γ) (hK : IsCompact (K : Set Γ)) :
    IsProPSubgroup (ringChar 𝓀[F]) K := by
  let P := GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)
  let : IsAffine P.X.left := GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)
  let : TopologicalSpace (rationalPoints P) := rationalPointTopology F P.X
  let e := GeneralLinear.rationalPointsMatrixHomeomorph (F := F) n
  let : IsTopologicalGroup (rationalPoints P) :=
    e.isInducing.isTopologicalGroup e.toMonoidHom
  obtain ⟨t, ht⟩ := UnitriangularCongruence.exists_rescale_mem_standardCongruence
    φ hφ.continuous hdiag hlow K hK
  let M := GeneralLinear.standardIntegralModel ↥𝒪[F] F (Fin n)
  let Q := M.congruenceSubgroupAt 1
  let f : Γ →* rationalPoints P :=
    e.symm.toMonoidHom.comp ((UnitriangularCongruence.rescale t).toMonoidHom.comp φ)
  let fK : K →* Q := (f.comp K.subtype).codRestrict Q fun x => by
    change (GeneralLinear.rationalPointsEquiv n (CommRingCat.of F)).symm
      (UnitriangularCongruence.rescale t (φ x)) ∈ _
    exact ht x x.property
  have hf : IsEmbedding f :=
    e.symm.isEmbedding.comp ((UnitriangularCongruence.rescaleContinuous t).isEmbedding.comp hφ)
  have hfK : IsEmbedding fK :=
    (hf.comp IsEmbedding.subtypeVal).codRestrict (Q : Set (rationalPoints P)) _
  exact (M.localField_isProP_congruenceSubgroupAt 1).of_isEmbedding fK hfK hK

end Unitriangular

section Unipotent

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- Every compact subgroup of the actual local rational points of a unipotent
affine group of finite type is pro-p in its canonical subspace topology. -/
theorem isProPSubgroup_of_isCompact_isUnipotent
    (U : GroupScheme (Spec (CommRingCat.of F))) [IsAffine U.X.left]
    [LocallyOfFiniteType U.X.hom] (hU : IsUnipotent U) :
    letI : TopologicalSpace (rationalPoints U) := rationalPointTopology F U.X
    ∀ K : Subgroup (rationalPoints U), IsCompact (K : Set (rationalPoints U)) →
      IsProPSubgroup (ringChar 𝓀[F]) K := by
  let : TopologicalSpace (rationalPoints U) := rationalPointTopology F U.X
  let : T2Space F := Langlands.BruhatTits.localField_t2Space F
  obtain ⟨n, ρ, hρ, hdiag, hlow⟩ := exists_unitriangular_closedRepresentation U hU
  exact isProPSubgroup_of_isCompact_unitriangular ρ.rationalMatrix
    (ρ.isClosedEmbedding_rationalMatrix hρ).isEmbedding hdiag hlow

end Unipotent

end Langlands.GroupScheme
