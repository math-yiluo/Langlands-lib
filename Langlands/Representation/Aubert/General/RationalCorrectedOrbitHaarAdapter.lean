import Langlands.Representation.Aubert.General.RationalCorrectedOrbitRealization
import Langlands.Representation.Aubert.General.CommonCentralizerHaarBalance
import Langlands.Representation.Aubert.General.Conjugation

/-! # Actual Haar values for corrected-orbit cocharacters -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme

private theorem closedNormalizerCharacter_congr
    {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] {U V : Subgroup H}
    (hUV : U = V) (hU : IsClosed (U : Set H)) (hV : IsClosed (V : Set H))
    (x : Subgroup.normalizer (U : Set H)) (y : Subgroup.normalizer (V : Set H))
    (hxy : (x : H) = y) :
    HaarModulus.closedNormalizerCharacter U hU x =
      HaarModulus.closedNormalizerCharacter V hV y := by
  subst V
  congr 1
  exact Subtype.ext hxy

namespace CorrectedOrbitCocharacterRealization

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}
    {I K : Finset (SimpleRoot i ν)} {m : rationalPoints G}
    (r : CorrectedOrbitCocharacterRealization i ν I K m)

local instance correctedOrbitHaarAdapterAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

/-- The actual affine group scheme representing the common full centralizer. -/
abbrev actingScheme :=
  Dynamic.Affine.centralizerScheme (CommGroupScheme.groupHom r.zeta ≫ i)

/-- Its original inclusion into the ambient group scheme. -/
def actingHom : r.actingScheme ⟶ G :=
  Dynamic.Affine.centralizerHom (CommGroupScheme.groupHom r.zeta ≫ i)

theorem acting_range_left :
    SubgroupFunctor.range r.actingHom ≤
      Dynamic.centralizer (CommGroupScheme.groupHom r.zeta ≫ i) :=
  (Dynamic.Affine.isRepresentedBy_centralizerHom
    (CommGroupScheme.groupHom r.zeta ≫ i)).2.le

theorem acting_range_right :
    SubgroupFunctor.range r.actingHom ≤
      Dynamic.centralizer (CommGroupScheme.groupHom r.eta ≫ i) := by
  rw [← r.centralizer_eq]
  exact r.acting_range_left

theorem levi_left_points :
    (Dynamic.centralizer (CommGroupScheme.groupHom r.zeta ≫ i)).rationalPoints =
      levi i ν I := by
  rw [← r.levi_left]

/-- Actual points of the represented common centralizer identify with the
original standard Levi by their original ambient values. -/
def leviPointEquiv : rationalPoints r.actingScheme ≃* levi i ν I :=
  ((Dynamic.Affine.isRepresentedBy_centralizerHom
    (CommGroupScheme.groupHom r.zeta ≫ i)).pointsEquiv (Over.mk (𝟙 _))).trans
      (MulEquiv.subgroupCongr r.levi_left_points)

@[simp] theorem leviPointEquiv_coe (z : rationalPoints r.actingScheme) :
    (r.leviPointEquiv z : rationalPoints G) = rationalPoints.map r.actingHom z :=
  rfl

@[simp] theorem leviPointEquiv_symm_map (l : levi i ν I) :
    rationalPoints.map r.actingHom (r.leviPointEquiv.symm l) = l := by
  rw [← r.leviPointEquiv_coe, MulEquiv.apply_symm_apply]

section Haar

variable [TopologicalSpace k]

local instance correctedOrbitHaarAdapterTopology :
    TopologicalSpace (Langlands.AlgebraicGeometry.PointTopology.RationalPoint k G.X) :=
  pointTopology

variable (hUI : IsClosed (unipotent i ν I : Set (rationalPoints G)))
    (hUK : IsClosed (unipotent i ν K : Set (rationalPoints G)))

include hUI in
theorem isClosed_left :
    IsClosed ((Dynamic.unipotent (CommGroupScheme.groupHom r.zeta ≫ i)).rationalPoints :
      Set (rationalPoints G)) := by
  rw [r.unipotent_left_points]
  exact hUI

variable [NonarchimedeanGroup
  (Langlands.AlgebraicGeometry.PointTopology.RationalPoint k G.X)]

include hUK in
theorem isClosed_right :
    IsClosed ((Dynamic.unipotent (CommGroupScheme.groupHom r.eta ≫ i)).rationalPoints :
      Set (rationalPoints G)) := by
  rw [r.unipotent_right_points]
  change IsClosed ((fun x : rationalPoints G => m⁻¹ * x * (m⁻¹)⁻¹) ⁻¹'
    (unipotent i ν K : Set (rationalPoints G)))
  exact hUK.preimage ((continuous_const.mul continuous_id).mul continuous_const)

include hUI hUK in
theorem isClosed_intersection :
    IsClosed ((Dynamic.unipotent (CommGroupScheme.groupHom r.zeta ≫ i) ⊓
      Dynamic.unipotent (CommGroupScheme.groupHom r.eta ≫ i)).rationalPoints :
        Set (rationalPoints G)) := by
  rw [r.intersection_points]
  exact CorrectedFiltration.isClosed_orbitUnipotentIntersection hUI hUK m

variable [LocallyCompactSpace
    (Langlands.AlgebraicGeometry.PointTopology.RationalPoint k G.X)]
    (hdI : IsSemidirectDecomposition (parabolic i ν I) (levi i ν I) (unipotent i ν I))
    (hdK : IsSemidirectDecomposition (parabolic i ν K) (levi i ν K) (unipotent i ν K))
    (hK : ∀ x : rationalPoints G, x ∈ levi i ν I ↔ m⁻¹ * x * m ∈ levi i ν K)

/-- The first centralizing Haar character is the exact target's first
restricted character, at the original Levi point. -/
theorem haar_left (z : rationalPoints r.actingScheme) :
    centralizingUnipotentHaarCharacter
        (CommGroupScheme.groupHom r.zeta ≫ i) r.actingHom r.acting_range_left
        (r.isClosed_left hUI) z =
      HaarModulus.closedRestrictCharacter (unipotent i ν I) hUI (levi i ν I)
        hdI.levi_le_normalizer (r.leviPointEquiv z) := by
  apply closedNormalizerCharacter_congr r.unipotent_left_points
    (r.isClosed_left hUI) hUI
    (Dynamic.centralizingUnipotentNormalizerHom
      (CommGroupScheme.groupHom r.zeta ≫ i) r.actingHom r.acting_range_left z)
    (Subgroup.inclusion hdI.levi_le_normalizer (r.leviPointEquiv z))
  rfl

/-- The second centralizing Haar character is the exact original second
radical character at `conjugationEquiv m hK` of that Levi point. -/
theorem haar_right (z : rationalPoints r.actingScheme) :
    centralizingUnipotentHaarCharacter
        (CommGroupScheme.groupHom r.eta ≫ i) r.actingHom r.acting_range_right
        (r.isClosed_right hUK) z =
      HaarModulus.closedRestrictCharacter (unipotent i ν K) hUK (levi i ν K)
        hdK.levi_le_normalizer (conjugationEquiv m hK (r.leviPointEquiv z)) := by
  have hV (x : rationalPoints G) :
      x ∈ (Dynamic.unipotent (CommGroupScheme.groupHom r.eta ≫ i)).rationalPoints ↔
        m⁻¹ * x * m ∈ unipotent i ν K := by
    rw [r.unipotent_right_points]
    simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hx :
      m⁻¹ * (Dynamic.centralizingUnipotentNormalizerHom
        (CommGroupScheme.groupHom r.eta ≫ i) r.actingHom r.acting_range_right z :
          rationalPoints G) * m ∈
        Subgroup.normalizer (unipotent i ν K : Set (rationalPoints G)) := by
    apply hdK.levi_le_normalizer
    apply (hK _).mp
    exact (r.leviPointEquiv z).property
  exact closedNormalizerCharacter_conj m hV hUK (r.isClosed_right hUK)
    (Dynamic.centralizingUnipotentNormalizerHom
      (CommGroupScheme.groupHom r.eta ≫ i) r.actingHom r.acting_range_right z) hx

/-- The centralizing intersection character is the restricted character of
the literal orbit intersection with the target's published normalizer proof. -/
theorem haar_intersection (z : rationalPoints r.actingScheme) :
    centralizingUnipotentIntersectionHaarCharacter
        (CommGroupScheme.groupHom r.zeta ≫ i) (CommGroupScheme.groupHom r.eta ≫ i)
        r.actingHom r.acting_range_left r.acting_range_right
        (r.isClosed_intersection hUI hUK) z =
      HaarModulus.closedRestrictCharacter
        (CorrectedFiltration.orbitUnipotentIntersection (unipotent i ν I) (unipotent i ν K) m)
        (CorrectedFiltration.isClosed_orbitUnipotentIntersection hUI hUK m) (levi i ν I)
        (CorrectedFiltration.levi_le_normalizer_orbitUnipotentIntersection hdI hdK m hK)
        (r.leviPointEquiv z) := by
  apply closedNormalizerCharacter_congr r.intersection_points
    (r.isClosed_intersection hUI hUK)
    (CorrectedFiltration.isClosed_orbitUnipotentIntersection hUI hUK m)
    (Dynamic.centralizingUnipotentIntersectionNormalizerHom
      (CommGroupScheme.groupHom r.zeta ≫ i) (CommGroupScheme.groupHom r.eta ≫ i)
      r.actingHom r.acting_range_left r.acting_range_right z)
    (Subgroup.inclusion
      (CorrectedFiltration.levi_le_normalizer_orbitUnipotentIntersection hdI hdK m hK)
      (r.leviPointEquiv z))
  rfl

/-- A full common-centralizer Haar balance yields the exact three target
values for every original Levi point. The balance remains an explicit
internal hypothesis here. -/
theorem squared_modulus_of_dynamic_balance
    (hBalance : ∀ z : rationalPoints r.actingScheme,
      (centralizingUnipotentHaarCharacter
        (CommGroupScheme.groupHom r.zeta ≫ i) r.actingHom r.acting_range_left
        (r.isClosed_left hUI) z : ℝ≥0) *
      (centralizingUnipotentHaarCharacter
        (CommGroupScheme.groupHom r.eta ≫ i) r.actingHom r.acting_range_right
        (r.isClosed_right hUK) z : ℝ≥0) =
      (centralizingUnipotentIntersectionHaarCharacter
        (CommGroupScheme.groupHom r.zeta ≫ i) (CommGroupScheme.groupHom r.eta ≫ i)
        r.actingHom r.acting_range_left r.acting_range_right
        (r.isClosed_intersection hUI hUK) z : ℝ≥0) ^ 2)
    (l : levi i ν I) :
    (HaarModulus.closedRestrictCharacter (unipotent i ν I) hUI (levi i ν I)
        hdI.levi_le_normalizer l : ℝ≥0) *
      (HaarModulus.closedRestrictCharacter (unipotent i ν K) hUK (levi i ν K)
        hdK.levi_le_normalizer (conjugationEquiv m hK l) : ℝ≥0) =
      (HaarModulus.closedRestrictCharacter
        (CorrectedFiltration.orbitUnipotentIntersection (unipotent i ν I) (unipotent i ν K) m)
        (CorrectedFiltration.isClosed_orbitUnipotentIntersection hUI hUK m) (levi i ν I)
        (CorrectedFiltration.levi_le_normalizer_orbitUnipotentIntersection hdI hdK m hK)
        l : ℝ≥0) ^ 2 := by
  have h := hBalance (r.leviPointEquiv.symm l)
  rw [r.haar_left hUI hdI, r.haar_right hUK hdK hK,
    r.haar_intersection hUI hUK hdI hdK hK, MulEquiv.apply_symm_apply] at h
  exact h

end Haar

end CorrectedOrbitCocharacterRealization

end Langlands.Aubert.General.RationalPointFamily
