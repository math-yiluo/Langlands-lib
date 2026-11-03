import Langlands.GroupScheme.Rational.ActionLieRigidity
import Langlands.GroupScheme.Rational.SemigroupIntersectionGeometry
import Langlands.GroupScheme.Lie.TorusCentralizer
import Langlands.GroupScheme.Torus.SolvableFixedContainmentConnectedStatement

/-! # The solvable alternative of semigroup intersection comparison -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

namespace AutomorphicAction

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {H : GroupScheme (Spec (CommRingCat.of k))}
    (c : AutomorphicAction S.toGrp H)

/-- The whole-torus fixed subgroup is invariant under the same action. -/
theorem fixedSubgroup_isStable : c.IsStable c.fixedSubgroup := by
  intro T s x hx V a t
  rw [c.naturality, ← c.act_mul_left, mul_comm, c.act_mul_left, hx V a t]

variable [IsAffineHom H.X.hom]

/-- The intrinsic zero weight is exactly the all-algebra invariant submodule. -/
theorem actionWeightSpace_zero_eq_lieInvariants :
    RelativeRoot.actionWeightSpace c 0 = c.lieInvariants := by
  ext X
  rw [RelativeRoot.actionWeightSpace_eq_lieWeightSpace, mem_lieWeightSpace]
  simp only [Grp.id_hom_hom, Category.comp_id, Lie.characterValue_zero,
    Units.val_one, one_smul, lieInvariants, Submodule.mem_mk]
  rfl

/-- The all-test fixed subgroup has exactly the intrinsic zero tangent weight. -/
theorem tangentSubmodule_fixedSubgroup_eq_actionWeightSpace_zero :
    RelativeRoot.tangentSubmodule c.fixedSubgroup =
      RelativeRoot.actionWeightSpace c 0 := by
  rw [c.tangentSubmodule_fixedSubgroup, c.actionWeightSpace_zero_eq_lieInvariants]

/-- Split-torus fixed subgroups of smooth affine groups have smooth closed
representatives, without a connectedness assertion. -/
theorem fixedSubgroup_isSmoothClosed [Smooth H.X.hom]
    (hS : IsSplitTorus S.toGrp) : RelativeRoot.IsSmoothClosed c.fixedSubgroup := by
  classical
  have : IsAffineHom S.X.hom := hS.isAffineHom
  obtain ⟨C, q, hq, hqc⟩ := fieldFixedSubgroupRepresentability k S.toGrp H inferInstance c
  obtain ⟨I, hI, ⟨e⟩⟩ := hS
  let : Fintype I := Fintype.ofFinite I
  let eD : S.toGrp ≅ (Diagonalizable.groupScheme (CommRingCat.of k) (I → ℤ)).toGrp :=
    e ≪≫ (Diagonalizable.splitIso (CommRingCat.of k) (AddEquiv.refl (I → ℤ))).symm
  exact ⟨C, q, hq, hqc,
    Diagonalizable.fixedSubgroup_smooth_of_actingIso
      Diagonalizable.FixedSmooth.fixedSubgroupSmooth c eD inferInstance inferInstance q hq hqc⟩

/-- A chosen smooth closed representative of the full split-torus fixed
subgroup. -/
def fixedSubgroupSmoothRepresentative [Smooth H.X.hom]
    (hS : IsSplitTorus S.toGrp) : GroupScheme (Spec (CommRingCat.of k)) :=
  (c.fixedSubgroup_isSmoothClosed hS).choose

/-- The actual inclusion of the chosen smooth fixed-subgroup representative. -/
def fixedSubgroupSmoothInclusion [Smooth H.X.hom]
    (hS : IsSplitTorus S.toGrp) : c.fixedSubgroupSmoothRepresentative hS ⟶ H :=
  (c.fixedSubgroup_isSmoothClosed hS).choose_spec.choose

/-- The chosen inclusion represents the all-test fixed subgroup and is smooth
over the field and closed in the ambient group. -/
theorem fixedSubgroupSmoothInclusion_properties [Smooth H.X.hom]
    (hS : IsSplitTorus S.toGrp) :
    c.fixedSubgroup.IsRepresentedBy (c.fixedSubgroupSmoothInclusion hS) ∧
      IsClosedSubgroup (c.fixedSubgroupSmoothInclusion hS) ∧
      Smooth (c.fixedSubgroupSmoothRepresentative hS).X.hom :=
  (c.fixedSubgroup_isSmoothClosed hS).choose_spec.choose_spec

end AutomorphicAction

namespace RelativeRoot

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom]
    (c : AutomorphicAction S.toGrp H) (hS : IsSplitTorus S.toGrp)

/-- When zero belongs to the semigroup, every fixed tangent lies in its full
weight span. -/
theorem tangentSubmodule_fixedSubgroup_le_semigroupWeightSpan
    (A : AddSubsemigroup (characterLattice S)) (h0 : 0 ∈ A) :
    tangentSubmodule c.fixedSubgroup ≤ semigroupWeightSpan c A := by
  rw [c.tangentSubmodule_fixedSubgroup_eq_actionWeightSpace_zero]
  exact le_iSup (fun χ : A => actionWeightSpace c χ.val) ⟨0, h0⟩

variable [Smooth H.X.hom] [ConnectedSpace H.X.left]
    (hConn : Torus.SolvableFixedContainmentConnectedStatement.{u})
    (hsolv : IsSolvableScheme H)

include hConn hsolv hS

/-- The general solvable connectedness criterion makes the whole-torus fixed
subgroup a smooth connected closed subgroup functor. -/
theorem fixedSubgroup_isSmoothConnectedClosed_of_solvable :
    IsSmoothConnectedClosed c.fixedSubgroup := by
  obtain ⟨C, q, hq, hqc, hqs⟩ := c.fixedSubgroup_isSmoothClosed hS
  exact ⟨C, q, hq, hqc, hqs,
    hConn k H inferInstance inferInstance inferInstance hsolv S hS c c.fixedSubgroup
      c.fixedSubgroup_isStable le_rfl C q hq hqc hqs⟩

/-- The full fixed subgroup of a connected solvable group is an actual
semigroup generator whenever the semigroup contains zero. -/
theorem fixedSubgroup_isSemigroupGenerator_of_solvable
    (A : AddSubsemigroup (characterLattice S)) (h0 : 0 ∈ A) :
    IsSemigroupGenerator c A c.fixedSubgroup := by
  exact ⟨fixedSubgroup_isSmoothConnectedClosed_of_solvable c hS hConn hsolv,
    c.fixedSubgroup_isStable,
    actionWeightSupport_subset_of_tangentSubmodule_le c hS A c.fixedSubgroup
      (tangentSubmodule_fixedSubgroup_le_semigroupWeightSpan c A h0)⟩

/-- Zero-containing semigroups contain the full torus fixed subgroup in a
smooth connected solvable ambient group. -/
theorem fixedSubgroup_le_semigroupSubgroup_of_solvable
    (A : AddSubsemigroup (characterLattice S)) (h0 : 0 ∈ A) :
    c.fixedSubgroup ≤ semigroupSubgroup c A :=
  generator_le_semigroupSubgroup c A c.fixedSubgroup
    (fixedSubgroup_isSemigroupGenerator_of_solvable c hS hConn hsolv A h0)

variable {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (b : AutomorphicAction S.toGrp G) (j : H ⟶ G)
    (heq : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (x : T ⟶ H.X),
      c.act s x ≫ j.hom.hom = b.act s (x ≫ j.hom.hom))
    (hReal : SemigroupRealizationStatement.{u}) (hjc : IsClosedSubgroup j)

include heq hReal hjc

/-- The solvable alternative with zero present, reduced only to semigroup
realization and the independent general solvable connectedness criterion. -/
theorem semigroup_comap_eq_of_solvable_of_zero_mem
    (A : AddSubsemigroup (characterLattice S)) (h0 : 0 ∈ A) :
    (semigroupSubgroup b A).comap j = semigroupSubgroup c A := by
  obtain ⟨K, p, hp, hpc, hps⟩ :=
    isSmoothClosed_semigroup_comap b c j heq hReal hS hjc A
  have hfixed : c.fixedSubgroup ≤ (semigroupSubgroup b A).comap j :=
    (fixedSubgroup_le_semigroupSubgroup_of_solvable c hS hConn hsolv A h0).trans
      (SubgroupFunctor.map_le_iff_le_comap.mp
        (semigroupSubgroup_map_le j hjc c b heq A))
  have hstable : c.IsStable ((semigroupSubgroup b A).comap j) :=
    isStable_comap_of_equivariant b c j heq
      (hReal k G inferInstance inferInstance S hS b A).2.1
  have hconnected : ConnectedSpace K.X.left :=
    hConn k H inferInstance inferInstance inferInstance hsolv S hS c
      ((semigroupSubgroup b A).comap j) hstable hfixed K p hp hpc hps
  exact semigroup_comap_eq_of_connected b c j heq hReal hS hjc A p hp hpc hconnected

end RelativeRoot
end Langlands.GroupScheme
