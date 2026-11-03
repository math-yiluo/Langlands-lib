import Langlands.GroupScheme.IntegralModel
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.Algebra.Group.Subgroup.Basic

/-! # Residue fibres, reduction and connectedness for actual integral models -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G H : GroupScheme (Spec (CommRingCat.of K))}
  (M : IntegralModel R K G)

/-- Every actual scheme-theoretic fibre is connected in its Zariski topology. -/
def HasConnectedFibres : Prop :=
  ∀ x : Spec (CommRingCat.of R), ConnectedSpace (M.group.X.hom.fiber x)

/-- Every fibre is geometrically connected over the residue field of its base point. -/
def HasGeometricallyConnectedFibres : Prop :=
  GeometricallyConnected M.group.X.hom

theorem hasGeometricallyConnectedFibres_iff :
    M.HasGeometricallyConnectedFibres ↔
      ∀ x : Spec (CommRingCat.of R),
        GeometricallyConnected (M.group.X.hom.fiberToSpecResidueField x) :=
  GeometricallyConnected.iff_geometricallyConnected_fiber M.group.X.hom

theorem hasConnectedFibres_of_geometricallyConnected
    (h : M.HasGeometricallyConnectedFibres) : M.HasConnectedFibres := by
  let : GeometricallyConnected M.group.X.hom := h
  intro x
  infer_instance

section Residue

variable [IsLocalRing R]

/-- The actual scheme map induced by the residue quotient homomorphism. -/
def residueBaseMap (R : Type u) [CommRing R] [IsLocalRing R] :
    Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))

/-- The full special fibre as a group scheme over the actual residue field. -/
abbrev specialFibre :
    GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R))) :=
  (baseChange (residueBaseMap R)).obj M.group

/-- Reduction of integral sections by the actual residue quotient map. -/
def reduction : M.integralSections →* rationalPoints M.specialFibre :=
  baseChangeSectionHom (residueBaseMap R) M.group

/-- Reduction is the pullback lift of the residue restriction and the identity. -/
theorem reduction_left (x : M.integralSections) :
    (M.reduction x).left =
      pullback.lift (residueBaseMap R ≫ x.left) (𝟙 _)
        (by simp [Category.assoc, x.w]) :=
  baseChangeSectionHom_left (residueBaseMap R) M.group x

/-- The congruence kernel in the group of integral sections. -/
def congruenceKernel : Subgroup M.integralSections := M.reduction.ker

theorem mem_congruenceKernel (x : M.integralSections) :
    x ∈ M.congruenceKernel ↔ M.reduction x = 1 :=
  Iff.rfl

instance congruenceKernel_normal : M.congruenceKernel.Normal := by
  change M.reduction.ker.Normal
  infer_instance

variable {M} {N : IntegralModel R K H} {f : G ⟶ H}

/-- A compatible integral-model map induces the actual special-fibre map. -/
def Hom.specialFibreMap (φ : M.Hom N f) : M.specialFibre ⟶ N.specialFibre :=
  (baseChange (residueBaseMap R)).map φ.hom

/-- Reduction commutes with a compatible integral-model morphism. -/
theorem Hom.reduction_naturality (φ : M.Hom N f) (x : M.integralSections) :
    N.reduction (rationalPoints.map φ.hom x) =
      rationalPoints.map φ.specialFibreMap (M.reduction x) := by
  exact baseChangeSectionHom_naturality (residueBaseMap R) φ.hom x

theorem Hom.map_mem_congruenceKernel (φ : M.Hom N f) {x : M.integralSections}
    (hx : x ∈ M.congruenceKernel) :
    rationalPoints.map φ.hom x ∈ N.congruenceKernel := by
  rw [mem_congruenceKernel] at hx ⊢
  rw [φ.reduction_naturality, hx, map_one]

variable (M)

/-- The congruence kernel represented in the given generic rational-point group. -/
def congruenceSubgroup : Subgroup (rationalPoints G) :=
  M.congruenceKernel.map M.integralPointMap

theorem mem_congruenceSubgroup (g : rationalPoints G) :
    g ∈ M.congruenceSubgroup ↔
      ∃ x : M.integralSections, M.reduction x = 1 ∧ M.integralPointMap x = g :=
  Iff.rfl

theorem congruenceSubgroup_le_integralPoints :
    M.congruenceSubgroup ≤ M.integralPoints := by
  rintro g ⟨x, _, rfl⟩
  exact ⟨x, rfl⟩

/-- The congruence image with the integral-point image as its ambient group. -/
def congruenceInIntegralPoints : Subgroup M.integralPoints :=
  M.congruenceKernel.map M.integralPointMap.rangeRestrict

instance congruenceInIntegralPoints_normal : M.congruenceInIntegralPoints.Normal :=
  Subgroup.Normal.map (inferInstance : M.congruenceKernel.Normal)
    M.integralPointMap.rangeRestrict M.integralPointMap.rangeRestrict_surjective

theorem congruenceInIntegralPoints_eq_subgroupOf :
    M.congruenceInIntegralPoints =
      M.congruenceSubgroup.subgroupOf M.integralPoints := by
  ext g
  constructor
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hx, congrArg Subtype.val h⟩
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hx, Subtype.ext h⟩

/-- Normality is in the integral-point image, with this ambient group explicit. -/
instance congruenceSubgroup_normal_in_integralPoints :
    (M.congruenceSubgroup.subgroupOf M.integralPoints).Normal := by
  rw [← M.congruenceInIntegralPoints_eq_subgroupOf]
  infer_instance

/-- Connectedness of the Zariski space of the actual residue special fibre. -/
def HasConnectedSpecialFibre : Prop := ConnectedSpace M.specialFibre.X.left

/-- Geometric connectedness of the actual special fibre over the residue field. -/
def HasGeometricallyConnectedSpecialFibre : Prop :=
  GeometricallyConnected M.specialFibre.X.hom

theorem hasGeometricallyConnectedSpecialFibre_of_geometricallyConnected
    (h : M.HasGeometricallyConnectedFibres) :
    M.HasGeometricallyConnectedSpecialFibre := by
  let : GeometricallyConnected M.group.X.hom := h
  change GeometricallyConnected (pullback.snd M.group.X.hom (residueBaseMap R))
  infer_instance

theorem hasConnectedSpecialFibre_of_geometricallyConnected
    (h : M.HasGeometricallyConnectedSpecialFibre) :
    M.HasConnectedSpecialFibre := by
  let : GeometricallyConnected M.specialFibre.X.hom := h
  exact GeometricallyConnected.connectedSpace_of_subsingleton M.specialFibre.X.hom

end Residue
end Langlands.GroupScheme.IntegralModel
