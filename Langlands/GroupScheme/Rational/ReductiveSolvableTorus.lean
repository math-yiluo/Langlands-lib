import Langlands.GroupScheme.Rational.AlgClosedNormalSolvableTorusProof
import Langlands.GroupScheme.Rational.SolvableSchemeComparison
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.Torus.BaseChange
import Langlands.GroupScheme.Torus.Geometry

/-! # Solvable connected reductive groups are tori -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- A solvable connected reductive group over any field is a torus. -/
theorem IsConnectedReductive.isTorus_of_isSolvableGroupScheme
    (hG : IsConnectedReductive G) (hsol : IsSolvableGroupScheme G) :
    IsTorus G := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : ConnectedSpace G.X.left := hG.connectedSpace
  let b := toAlgebraicClosure k
  let Gc := (GroupScheme.baseChange b).obj G
  have hGc : IsPseudoReductive Gc :=
    { smooth := inferInstanceAs (Smooth (pullback.snd G.X.hom b))
      isAffineHom := inferInstanceAs (IsAffineHom (pullback.snd G.X.hom b))
      connectedSpace := G.connectedSpace_baseChange_of_smooth_affine b
      hasTrivialUnipotentRadical := hG.hasTrivialGeometricUnipotentRadical }
  have hsolc : IsSolvableGroupScheme Gc :=
    (((RelativeRoot.isSolvableScheme_iff_isSolvableGroupScheme hG.smooth).mpr hsol).baseChange
      b).isSolvableGroupScheme
  have hcl : IsClosedSubgroup (𝟙 Gc) :=
    inferInstanceAs (IsClosedImmersion (𝟙 Gc.X.left))
  have hnormal : (SubgroupFunctor.range (𝟙 Gc)).IsNormal := by
    intro T g x _ _
    exact SubgroupFunctor.mem_range.mpr ⟨g * x * g⁻¹, Category.comp_id _⟩
  have htorusc : IsTorus Gc :=
    (algClosedReductiveNormalSolvableTorus (AlgebraicClosure k) Gc hGc
      Gc (𝟙 Gc) hcl hGc.smooth hGc.connectedSpace hsolc hnormal).1
  exact IsTorus.of_baseChange (K := AlgebraicClosure k) htorusc

/-- Regard the original solvable connected reductive group as a commutative
group scheme, using its torus structure. -/
def IsConnectedReductive.torusOfIsSolvable
    (hG : IsConnectedReductive G) (hsol : IsSolvableGroupScheme G) :
    CommGroupScheme (Spec (CommRingCat.of k)) :=
  { toGrp := G
    comm := (hG.isTorus_of_isSolvableGroupScheme hsol).isCommMonObj }

/-- The construction keeps the original underlying group scheme. -/
@[simp]
theorem IsConnectedReductive.torusOfIsSolvable_toGrp
    (hG : IsConnectedReductive G) (hsol : IsSolvableGroupScheme G) :
    (hG.torusOfIsSolvable hsol).toGrp = G := rfl

/-- The commutative presentation is a torus over the original ground field. -/
theorem IsConnectedReductive.isTorus_torusOfIsSolvable
    (hG : IsConnectedReductive G) (hsol : IsSolvableGroupScheme G) :
    IsTorus (hG.torusOfIsSolvable hsol).toGrp :=
  hG.isTorus_of_isSolvableGroupScheme hsol

end Langlands.GroupScheme
