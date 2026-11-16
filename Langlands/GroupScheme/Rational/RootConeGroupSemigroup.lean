import Langlands.GroupScheme.Rational.RootSubsetGroupGeometry
import Langlands.GroupScheme.Rational.CyclicRootFunctorComparisonProof
import Langlands.GroupScheme.Rational.RootParabolicProper
import Langlands.GroupScheme.Rational.SemigroupRealizationGeometry
import Langlands.GroupScheme.Lie.TorusCentralizer

/-! # Cone slices and generated character-semigroup groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}

/-- The actual integral characters whose real images belong to the cone. -/
def rootConeSemigroup (C : PointedCone ℝ (RealTorusSpace.Vstar T)) :
    AddSubsemigroup (characterLattice T) where
  carrier := {a | (1 : ℝ) ⊗ₜ[ℤ] a ∈ C}
  add_mem' := by
    intro a b ha hb
    change (1 : ℝ) ⊗ₜ[ℤ] (a + b) ∈ C
    simpa only [TensorProduct.tmul_add] using C.add_mem ha hb

@[simp] theorem mem_rootConeSemigroup
    (C : PointedCone ℝ (RealTorusSpace.Vstar T)) (a : characterLattice T) :
    a ∈ rootConeSemigroup C ↔ (1 : ℝ) ⊗ₜ[ℤ] a ∈ C := Iff.rfl

/-- Zero is retained, so the semigroup group also contains the torus centralizer. -/
theorem zero_mem_rootConeSemigroup (C : PointedCone ℝ (RealTorusSpace.Vstar T)) :
    (0 : characterLattice T) ∈ rootConeSemigroup C := by
  change (1 : ℝ) ⊗ₜ[ℤ] (0 : characterLattice T) ∈ C
  simpa only [TensorProduct.tmul_zero] using C.zero_mem

/-- Intersecting cones intersects their integral-character semigroups. -/
@[simp] theorem rootConeSemigroup_inf
    (C D : PointedCone ℝ (RealTorusSpace.Vstar T)) :
    rootConeSemigroup (C ⊓ D) = rootConeSemigroup C ⊓ rootConeSemigroup D := rfl

namespace RelativeRoot

variable [IsAffineHom G.X.hom] [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (i : T.toGrp ⟶ G) (hi : IsSplitSubtorus i)
    (C : PointedCone ℝ (RealTorusSpace.Vstar T))

include hi

/-- All-test containment of the whole-torus centralizer in the cone semigroup group. -/
theorem torusCentralizer_le_rootConeSemigroupGroup :
    torusCentralizer i ≤ semigroupSubgroup (AutomorphicAction.conjugation i)
      (rootConeSemigroup C) := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨Z, z, hzc, hzs, hz⟩ :=
    torusCentralizer_hasSmoothClosedRepresentative i hi inferInstance
  have hconn : ConnectedSpace Z.X.left := hi.1.connectedSpace_centralizer i hz
  have hstable : (AutomorphicAction.conjugation i).IsStable (torusCentralizer i) := by
    intro V s g hg
    have he : (AutomorphicAction.conjugation i).act s g = g := by
      rw [AutomorphicAction.conjugation_act]
      have hc := hg V (𝟙 V) s
      simp only [Category.id_comp] at hc
      rw [hc.symm.eq, mul_inv_cancel_right]
    rwa [he]
  apply le_semigroupSubgroup_of_tangentSubmodule_le
    (AutomorphicAction.conjugation i) hi.1 (rootConeSemigroup C)
    ⟨Z, z, hz, hzc, hzs, hconn⟩ hstable
  intro X hX
  have hzero : X ∈ actionWeightSpace (AutomorphicAction.conjugation i) 0 := by
    rw [actionWeightSpace_conjugation]
    exact Lie.mem_weightSpace_zero_of_mem_torusCentralizer i X.toMul hX
  exact (le_iSup (fun a : rootConeSemigroup C =>
    actionWeightSpace (AutomorphicAction.conjugation i) a.val)
    ⟨0, zero_mem_rootConeSemigroup C⟩) hzero

omit [ConnectedSpace G.X.left] in
/-- A selected root's whole positive cyclic tail remains inside the cone. -/
theorem subgroup_le_rootConeSemigroupGroup {a : characterLattice T}
    (ha : a ≠ 0) (hC : (1 : ℝ) ⊗ₜ[ℤ] a ∈ C) :
    subgroup i a ≤ semigroupSubgroup (AutomorphicAction.conjugation i)
      (rootConeSemigroup C) := by
  rw [← weightFiltration_one_eq_subgroup hi.1 i a ha]
  apply semigroupSubgroup_mono
  rintro b ⟨n, _, _, rfl⟩
  change (1 : ℝ) ⊗ₜ[ℤ] (n • a) ∈ C
  rw [show (1 : ℝ) ⊗ₜ[ℤ] (n • a) = n • ((1 : ℝ) ⊗ₜ[ℤ] a) from
    map_nsmul (TensorProduct.mk ℤ ℝ (characterLattice T) (1 : ℝ)) n a]
  exact C.toAddSubmonoid.nsmul_mem hC n

end RelativeRoot

variable [IsAffineHom G.X.hom]
    (i : T.toGrp ⟶ G) (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (C : PointedCone ℝ (RealTorusSpace.Vstar T))
    {H : GroupScheme (Spec (CommRingCat.of k))} {h : H ⟶ G}

include hG hi

/-- A supplied root-cone-slice group is exactly the intrinsic character-semigroup group. -/
theorem IsRootSubsetGroup.range_eq_rootConeSemigroupGroup
    (hh : IsRootSubsetGroup i {a | a ∈ relativeRoots i ∧ (1 : ℝ) ⊗ₜ[ℤ] a ∈ C} h) :
    SubgroupFunctor.range h =
      RelativeRoot.semigroupSubgroup (AutomorphicAction.conjugation i) (rootConeSemigroup C) := by
  let : Smooth G.X.hom := hG.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  let : IsAffineHom T.X.hom := hi.1.1.isAffineHom
  let b := AutomorphicAction.conjugation i
  let A := rootConeSemigroup C
  obtain ⟨K, q, hq, hqc, hqs, hqconn⟩ :=
    RelativeRoot.isSmoothConnectedClosed_semigroupSubgroup b hi.1.1 A
  have hle : SubgroupFunctor.range h ≤ RelativeRoot.semigroupSubgroup b A := by
    rw [← hq.2]
    apply hh.2.2.2 K q hqc
    · rw [hq.2]
      exact RelativeRoot.torusCentralizer_le_rootConeSemigroupGroup i hi.1 C
    · intro a ha
      rw [hq.2]
      exact RelativeRoot.subgroup_le_rootConeSemigroupGroup i hi.1 C ha.1.1 ha.2
  have hLieA := RelativeRoot.hasLieImage_semigroupSubgroup b hi.1.1 A
  have hLie : RelativeRoot.HasLieImage (SubgroupFunctor.range h)
      (RelativeRoot.semigroupWeightSpan b A) := by
    apply (RelativeRoot.hasLieImage_iff_tangentSubmodule_eq _ _).mpr
    apply le_antisymm
    · rw [← (RelativeRoot.hasLieImage_iff_tangentSubmodule_eq _ _).mp hLieA]
      exact RelativeRoot.tangentSubmodule_mono hle
    · apply iSup_le
      intro a
      rw [RelativeRoot.actionWeightSpace_conjugation]
      by_cases ha0 : a.val = 0
      · rw [ha0]
        intro X hX
        exact hh.2.1 _ (Lie.mem_torusCentralizer_of_mem_weightSpace_zero i X.toMul hX)
      · by_cases haw : weightSpace i a.val = ⊥
        · rw [haw]
          exact bot_le
        · exact (RelativeRoot.weightSpace_le_tangentSubmodule_subgroup i hi.1.1 ha0).trans
            (RelativeRoot.tangentSubmodule_mono (hh.2.2.1 a.val ⟨⟨ha0, haw⟩, a.property⟩))
  obtain ⟨hHs, _, hHconn⟩ :=
    IsRootSubsetGroup.smooth_affine_connected i _ hG hi (fun _ ha => ha.1) hh
  have hrep : (SubgroupFunctor.range h).IsRepresentedBy h := by
    let : IsClosedImmersion h.hom.hom.left := hh.1
    exact ⟨Over.mono_of_mono_left _, rfl⟩
  exact RelativeRoot.IsSmoothConnectedClosed.eq_of_le_of_hasLieImage
    ⟨H, h, hrep, hh.1, hHs, hHconn⟩ ⟨K, q, hq, hqc, hqs, hqconn⟩ hle hLie hLieA

end Langlands.GroupScheme
