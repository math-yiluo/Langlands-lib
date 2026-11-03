import Langlands.GroupScheme.Rational.KernelCentralizerTangent
import Langlands.GroupScheme.Rational.KernelCentralizerClosed
import Langlands.GroupScheme.Rational.KernelCentralizerSmooth
import Langlands.GroupScheme.Rational.SemigroupWeightSupport
import Langlands.GroupScheme.FieldFixedSubgroupRepresentabilityProof
import Langlands.GroupScheme.Torus.KernelDiagonalizable
import Langlands.GroupScheme.Torus.DiagonalizableFixedSmoothProof
import Langlands.GroupScheme.Lie.SubgroupEqualityProof
import Langlands.GroupScheme.Dynamic.ActionAffineRepresentability
import Langlands.GroupScheme.Dynamic.ActionLieCriterion
import Langlands.GroupScheme.Dynamic.LieProof

/-! # Geometric rigidity of integral and positive action weights -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

namespace RelativeRoot

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- All integral multiples of one character for an arbitrary torus action. -/
def integralActionWeightSpan {S : CommGroupScheme (Spec (CommRingCat.of k))}
    (b : AutomorphicAction S.toGrp G) (a : characterLattice S) :
    Submodule k (Additive (lieKernel G k)) :=
  ⨆ n : ℤ, actionWeightSpace b (n • a)

/-- A smooth closed representative with the full tangent image equals the
connected smooth ambient group on every test scheme. -/
theorem eq_top_of_smooth_closed_of_tangentSubmodule_eq_top
    [Smooth G.X.hom] [ConnectedSpace G.X.left]
    {F : SubgroupFunctor G} {H : GroupScheme (Spec (CommRingCat.of k))}
    (j : H ⟶ G) (hj : F.IsRepresentedBy j) (hc : IsClosedSubgroup j)
    (hs : Smooth H.X.hom) (hLie : tangentSubmodule F = ⊤) : F = ⊤ := by
  let : Smooth H.X.hom := hs
  let : IsClosedImmersion j.hom.hom.left := hc
  let : IsAffineHom H.X.hom := by
    rw [← j.hom.hom.w]
    infer_instance
  let : Mono j.hom.hom := hj.1
  have hRange : LinearMap.range (Lie.targetMapLinear j k) = ⊤ := by
    rw [← tangentSubmodule_range j, hj.2, hLie]
  have hfull : ∀ X : lieKernel G k,
      ∃ Y : lieKernel H k, Y.val ≫ j.hom.hom = X.val := by
    intro X
    obtain ⟨Y, hY⟩ := (show Additive.ofMul X ∈
      LinearMap.range (Lie.targetMapLinear j k) by rw [hRange]; trivial)
    exact ⟨Y.toMul, congrArg (fun Z : Additive (lieKernel G k) => Z.toMul.val) hY⟩
  exact hj.2.symm.trans (lieSubgroupEquality k G H j hc hfull)

end RelativeRoot

namespace AutomorphicAction

open RelativeRoot

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- All-refinement fixed tangents are precisely the differential invariants. -/
theorem tangentSubmodule_fixedSubgroup {H : GroupScheme (Spec (CommRingCat.of k))}
    (b : AutomorphicAction H G) :
    tangentSubmodule b.fixedSubgroup = b.lieInvariants := by
  ext X
  exact b.isFixed_iff_mem_lieInvariants X

/-- A diagonalizable action with trivial differential on a smooth connected
ambient group is trivial on all tests. Torsion in its character group is allowed. -/
theorem fixedSubgroup_eq_top_of_diagonalizable_lieInvariants_eq_top
    [Smooth G.X.hom] [ConnectedSpace G.X.left]
    {H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom]
    {Λ : Type u} [AddCommGroup Λ] [AddGroup.FG Λ]
    (b : AutomorphicAction H G)
    (e : H ≅ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp)
    (hLie : b.lieInvariants = ⊤) : b.fixedSubgroup = ⊤ := by
  obtain ⟨C, j, hj, hc⟩ := fieldFixedSubgroupRepresentability k H G inferInstance b
  have hs : Smooth C.X.hom :=
    Diagonalizable.fixedSubgroup_smooth_of_actingIso
      Diagonalizable.FixedSmooth.fixedSubgroupSmooth b e inferInstance inferInstance j hj hc
  apply eq_top_of_smooth_closed_of_tangentSubmodule_eq_top j hj hc hs
  rw [tangentSubmodule_fixedSubgroup, hLie]

variable {S : CommGroupScheme (Spec (CommRingCat.of k))}
    (b : AutomorphicAction S.toGrp G) (a : characterLattice S)

/-- Integral character multiples are fixed by the actual character kernel,
including its possible infinitesimal part. -/
theorem integralActionWeightSpan_le_kernel_lieInvariants :
    integralActionWeightSpan b a ≤ (b.restrict (characterKernelι a)).lieInvariants := by
  refine iSup_le fun n => ?_
  intro X hX A _ _ c
  rw [actionWeightSpace_eq_lieWeightSpace] at hX
  have h := hX A (c ≫ (characterKernelι a).hom.hom)
  simp only [Grp.id_hom_hom, Category.comp_id] at h
  rw [characterValue_zsmul_kernel, Units.val_one, one_smul] at h
  simpa only [differential_restrict] using h

/-- If all tangent weights are integral multiples of a character, its actual
kernel acts trivially on a smooth connected group. -/
theorem kernelActsTrivially_of_integralActionWeightSpan_eq_top
    [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (hS : IsSplitTorus S.toGrp) (hLie : integralActionWeightSpan b a = ⊤) :
    b.KernelActsTrivially (CommGroupScheme.groupHom a) := by
  let : IsAffineHom S.X.hom := hS.isAffineHom
  let : IsAffineHom (characterKernel a).X.hom := characterKernel_isAffineHom a
  let : AddGroup.FG (Diagonalizable.quotientLattice a) :=
    Diagonalizable.quotientLattice_fg S hS a
  have hInv : (b.restrict (characterKernelι a)).lieInvariants = ⊤ := by
    apply top_unique
    rw [← hLie]
    exact b.integralActionWeightSpan_le_kernel_lieInvariants a
  have hfixed := fixedSubgroup_eq_top_of_diagonalizable_lieInvariants_eq_top
    (b.restrict (characterKernelι a)) (Diagonalizable.kernelDiagonalizableIso S hS a) hInv
  intro T c g
  have hg : g ∈ (b.restrict (characterKernelι a)).fixedSubgroup.carrier T := by
    rw [hfixed]
    trivial
  simpa only [Category.id_comp] using hg T (𝟙 T) c

/-- A smooth connected affine group with entirely positive Gm weights is
contracted to the identity on every test scheme. -/
theorem unipotent_eq_top_of_positiveWeightSpan_eq_top
    [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (d : AutomorphicAction (Gm (Spec (CommRingCat.of k))).toGrp G)
    (hLie : d.positiveWeightSpan = ⊤) : d.unipotent = ⊤ := by
  apply eq_top_of_smooth_closed_of_tangentSubmodule_eq_top
    (Affine.unipotentHom d) (Affine.isRepresentedBy_unipotentHom d)
    (Affine.isClosedSubgroup_unipotentHom d) (Affine.smooth_unipotentScheme d)
  rw [d.tangentSubmodule_unipotent dynamicLie, hLie]

end AutomorphicAction

end Langlands.GroupScheme
