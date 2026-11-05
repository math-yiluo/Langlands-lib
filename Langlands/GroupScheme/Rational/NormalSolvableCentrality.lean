import Langlands.GroupScheme.Absolute.NormalSolvableCentrality
import Langlands.GroupScheme.Absolute.AlgebraicClosureBaseChange
import Langlands.GroupScheme.Rational.SolvableSchemeComparison
import Langlands.GroupScheme.CentralIsogeny.FpqcReflectionHelpers

/-! # Normal solvable subgroups of connected reductive groups over any field -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Over every field, a smooth connected affine solvable normal closed subgroup
of a connected reductive group is central on every relative test scheme. -/
def NormalSolvableCentralityStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G H : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left],
    IsSolvableGroupScheme H → IsConnectedReductive G →
    ∀ (i : H ⟶ G), IsClosedSubgroup i →
      (SubgroupFunctor.range i).IsNormal → IsCentral i

/-- A smooth connected solvable normal closed subgroup of a connected reductive
group is central on every test scheme, over an arbitrary field. -/
theorem IsSolvableGroupScheme.isCentral_of_normal_of_isConnectedReductive_field
    {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
    (hH : IsSolvableGroupScheme H) (hG : IsConnectedReductive G)
    (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (hin : (SubgroupFunctor.range i).IsNormal) : IsCentral i := by
  let b := toAlgebraicClosure k
  have : Smooth ((GroupScheme.baseChange b).obj H).X.hom :=
    inferInstanceAs (Smooth (pullback.snd H.X.hom b))
  have : IsAffineHom ((GroupScheme.baseChange b).obj H).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd H.X.hom b))
  have : ConnectedSpace ((GroupScheme.baseChange b).obj H).X.left :=
    H.connectedSpace_baseChange_of_smooth_affine b
  have hHs : IsSolvableGroupScheme ((GroupScheme.baseChange b).obj H) :=
    (((RelativeRoot.isSolvableScheme_iff_isSolvableGroupScheme
      (inferInstanceAs (Smooth H.X.hom))).mpr hH).baseChange b).isSolvableGroupScheme
  have hin' : (SubgroupFunctor.range ((GroupScheme.baseChange b).map i)).IsNormal := by
    rw [SubgroupFunctor.range_baseChangeHom]
    exact hin.baseChange b
  obtain ⟨hsurj, hflat, -⟩ := fieldExtension_fpqc k (AlgebraicClosure k)
  let : Surjective b := hsurj
  let : Flat b := hflat
  apply IsCentral.of_baseChange b
  exact hHs.isCentral_of_normal_of_isConnectedReductive hG.baseChange_toAlgebraicClosure
    ((GroupScheme.baseChange b).map i) (hi.baseChange b) hin'

/-- The arbitrary-field centrality statement follows from fpqc reflection of
the published algebraically closed centrality theorem. -/
theorem normalSolvableCentrality : NormalSolvableCentralityStatement.{u} := by
  intro k _ G H _ _ _ hH hG i hi hin
  exact hH.isCentral_of_normal_of_isConnectedReductive_field hG i hi hin

end Langlands.GroupScheme
