import Langlands.GroupScheme.Reductive.CentralQuotientReductiveStatement
import Langlands.GroupScheme.Reductive.CentralQuotientCore
import Langlands.GroupScheme.Adjoint.CenterQuotientReduction
import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent

/-! # Quotients of connected reductive groups by central subgroups are connected reductive -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A subgroup functor contained in the centre stays in the centre after base change. -/
theorem SubgroupFunctor.baseChange_le_center {S S' : Scheme.{u}} (b : S' ⟶ S)
    {G : GroupScheme S} {N : SubgroupFunctor G} (hN : N ≤ center G) :
    N.baseChange b ≤ center ((GroupScheme.baseChange b).obj G) := by
  rw [center_baseChange]
  exact SubgroupFunctor.baseChange_mono b hN

/-- **Central quotients are reductive.** Over every field `k`, the target of an fppf quotient
of a connected reductive group by a subgroup functor contained in its centre, with affine
target locally of finite type, is connected reductive. -/
theorem centralQuotientReductive : CentralQuotientReductiveStatement.{u} := by
  intro k _ G Q q N hG hQa hQf hN hq
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : ConnectedSpace G.X.left := hG.connectedSpace
  let b := toAlgebraicClosure k
  have hGa : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
    change IsAffineHom (Limits.pullback.snd G.X.hom b)
    infer_instance
  have hGs : Smooth ((GroupScheme.baseChange b).obj G).X.hom := by
    change Smooth (Limits.pullback.snd G.X.hom b)
    infer_instance
  have hQa' : IsAffineHom ((GroupScheme.baseChange b).obj Q).X.hom := by
    change IsAffineHom (Limits.pullback.snd Q.X.hom b)
    infer_instance
  have hQf' : LocallyOfFiniteType ((GroupScheme.baseChange b).obj Q).X.hom := by
    change LocallyOfFiniteType (Limits.pullback.snd Q.X.hom b)
    infer_instance
  exact
    { smooth := hq.smooth_target
      isAffineHom := hQa
      connectedSpace := hq.connectedSpace
      hasTrivialGeometricUnipotentRadical :=
        CentralQuotient.hasTrivialUnipotentRadical_of_isFppfQuotient
          ((GroupScheme.baseChange b).map q) hGs hGa hG.connectedSpace_toAlgebraicClosure
          hG.hasTrivialGeometricUnipotentRadical hQa' hQf'
          (SubgroupFunctor.baseChange_le_center b hN) (hq.baseChange b) }

end Langlands.GroupScheme
