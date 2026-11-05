import Langlands.GroupScheme.Lie.SubgroupCellDimension
import Langlands.GroupScheme.HomogeneousQuotientDimension
import Langlands.GroupScheme.Rational.RootSubgroupRealizationProof
import Langlands.GroupScheme.Rational.RootSubgroupNontrivial
import Langlands.GroupScheme.Torus.MaximalSplitComparison
import Langlands.GroupScheme.Unipotent.OneDimensional.Proof
import Langlands.GroupScheme.Absolute.RootVectorLineStatement

/-! # Vector lines from a bound on the actual root tangent -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
    {G U : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom U.X.hom]

/-- The actual Lie module of a monomorphic representative is canonically
identified with any specified exact intrinsic Lie image. -/
def representedLieImageEquiv (F : SubgroupFunctor G) (j : U ⟶ G)
    (hj : F.IsRepresentedBy j)
    (W : Submodule k (Additive (lieKernel G k))) (hW : HasLieImage F W) :
    Additive (lieKernel U k) ≃ₗ[k] W :=
  (representedTangentLinearEquiv F j hj).trans
    (LinearEquiv.ofEq _ _ ((hasLieImage_iff_tangentSubmodule_eq F W).mp hW))

/-- A smooth connected affine representative with nonzero intrinsic tangent
of dimension at most one has constant smooth relative dimension one. -/
theorem smoothOfRelativeDimension_one_of_tangent_le_one
    [Smooth U.X.hom] [ConnectedSpace U.X.left]
    (F : SubgroupFunctor G) (j : U ⟶ G) (hj : F.IsRepresentedBy j)
    (hne : tangentSubmodule F ≠ ⊥)
    (hdim : Module.finrank k (tangentSubmodule F) ≤ 1) :
    SmoothOfRelativeDimension 1 U.X.hom := by
  have : FiniteDimensional k (tangentSubmodule F) :=
    (representedTangentLinearEquiv F j hj).finiteDimensional
  have : Nontrivial (tangentSubmodule F) :=
    Submodule.nontrivial_iff_ne_bot.mpr hne
  have hpos : 0 < Module.finrank k (tangentSubmodule F) :=
    Module.finrank_pos
  have hdim1 : Module.finrank k (tangentSubmodule F) = 1 := by omega
  have hUdim : Lie.dimension U = 1 := by
    rw [Lie.dimension, ← finrank_tangentSubmodule_eq_of_isRepresentedBy F j hj]
    exact hdim1
  obtain ⟨d, hd⟩ := Langlands.AlgebraicGeometry.smoothConnectedRelativeDimension
    U.X.left _ U.X.hom inferInstance inferInstance
  have hd1 : d = 1 := (Lie.dimension_eq_of_smoothOfRelativeDimension U hd).symm.trans hUdim
  simpa only [hd1] using hd

/-- The perfect-field classification applies to a smooth connected affine
unipotent representative once its nonzero intrinsic tangent has dimension
at most one. The resulting coordinates are natural on every scheme test. -/
theorem isVectorGroupOfDimension_one_of_tangent_le_one
    [PerfectField k] [Smooth U.X.hom] [ConnectedSpace U.X.left]
    (F : SubgroupFunctor G) (j : U ⟶ G) (hj : F.IsRepresentedBy j)
    (hU : IsUnipotent U) (hne : tangentSubmodule F ≠ ⊥)
    (hdim : Module.finrank k (tangentSubmodule F) ≤ 1) :
    IsVectorGroupOfDimension U 1 := by
  let : SmoothOfRelativeDimension 1 U.X.hom :=
    smoothOfRelativeDimension_one_of_tangent_le_one F j hj hne hdim
  exact perfectFieldOneDimensionalUnipotent k U inferInstance hU

end Langlands.GroupScheme.RelativeRoot

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] [PerfectField k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Closed root realization and the perfect-field classification turn a bound
on the full positive intrinsic root tangent into an actual vector line.
The tangent bound is an explicit remaining input. -/
theorem exists_rootVectorLine_of_tangent_le_one
    (hG : IsConnectedReductive G) (t : T.toGrp ⟶ G)
    (ht : IsMaximalSplitTorus t) (α : characterLattice T)
    (hα : haveI := hG.isAffineHom
      α ∈ relativeRoots t)
    (hdim : haveI := hG.isAffineHom
      Module.finrank k (RelativeRoot.tangentSubmodule
        (RelativeRoot.subgroup t α)) ≤ 1) :
    ∃ (U : GroupScheme (Spec (CommRingCat.of k))) (j : U ⟶ G),
      (RelativeRoot.subgroup t α).IsRepresentedBy j ∧ IsClosedSubgroup j ∧
        RelativeRoot.IsVectorGroupOfDimension U 1 := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  obtain ⟨U, j, hj, hclosed, hsmooth, hconn, hU, _, _, hLie⟩ :=
    RelativeRoot.rootSubgroupRealization k G hG T t ht α hα
  have : IsAffineHom U.X.hom := hclosed.isAffineHom
  have : Smooth U.X.hom := hsmooth
  have : ConnectedSpace U.X.left := hconn
  have hne : RelativeRoot.tangentSubmodule (RelativeRoot.subgroup t α) ≠ ⊥ := by
    rw [(RelativeRoot.hasLieImage_iff_tangentSubmodule_eq _ _).mp hLie]
    exact RelativeRoot.positiveWeightSpan_ne_bot t hα
  exact ⟨U, j, hj, hclosed,
    RelativeRoot.isVectorGroupOfDimension_one_of_tangent_le_one
      (RelativeRoot.subgroup t α) j hj hU hne hdim⟩

/-- Reduction of the exact absolute vector-line target to the full intrinsic
root tangent bound. This conditional helper does not supply that bound. -/
theorem absoluteRootVectorLine_of_tangentBound
    (hbound : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
      letI := hG.isAffineHom
      ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (t : T.toGrp ⟶ G),
        IsSplitSubtorus t → IsMaximalTorus t →
        ∀ α ∈ relativeRoots t,
          Module.finrank k (RelativeRoot.tangentSubmodule
            (RelativeRoot.subgroup t α)) ≤ 1) :
    AbsoluteRootVectorLineStatement.{u} := by
  intro k _ _ G hG T t hsplit hmax α hα
  exact exists_rootVectorLine_of_tangent_le_one hG t
    (hmax.isMaximalSplitTorus hsplit.1) α hα
    (hbound k G hG T t hsplit hmax α hα)

end Langlands.GroupScheme
