import Langlands.GroupScheme.Torus.MaximalModuliOpen
import Langlands.GroupScheme.Torus.EtaleLocalMaximalExistenceProof
import Langlands.GroupScheme.Torus.MaximalTorusModuliQuasiAffineProof

/-! # Representability of the scheme of maximal tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

namespace TorusSubgroupModuli

/-- Local maximal-torus existence makes any universal maximal-torus parameter
scheme surjective over the original base. -/
theorem IsUniversalMaximal.surjective_of_cover
    {S : Scheme.{u}} {G : GroupScheme S} {M : Over S}
    {K : CommGroupScheme M.left} {j : K.toGrp ⟶ (baseChange M.hom).obj G}
    (huni : IsUniversalMaximal j)
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    (h𝒰 : ∀ z : 𝒰.I₀, ∃ (H : CommGroupScheme (𝒰.X z))
      (i : H.toGrp ⟶ (baseChange (𝒰.f z)).obj G),
      RelativeTorus.IsTorus H.toGrp ∧ IsClosedSubgroup i ∧ IsFibrewiseMaximalTorus i) :
    Surjective M.hom := by
  constructor
  intro s
  obtain ⟨z, x, hx⟩ := 𝒰.exists_eq s
  obtain ⟨H, i, hH, hi, hm⟩ := h𝒰 z
  obtain ⟨a, ha, hua⟩ := huni (Over.mk (𝒰.f z)) H i hH hi hm
  refine ⟨a.left x, ?_⟩
  have he := congrArg (fun f : 𝒰.X z ⟶ S => f x) (Over.w a)
  exact he.trans hx

end TorusSubgroupModuli

/-- The complete representability assertion follows from the separate
quasi-affineness theorem. -/
theorem maximalTorusScheme_of
    (hqa : MaximalTorusModuliQuasiAffineStatement.{u}) :
    MaximalTorusSchemeStatement.{u} := by
  intro S G hG
  obtain ⟨M, K, j, hK, hj, hm, huni, hs⟩ :=
    TorusSubgroupModuli.exists_smooth_isUniversalMaximal S G hG
  obtain ⟨𝒰, h𝒰⟩ := etaleLocalMaximalTorusExistence S G hG
  exact ⟨M, K, j, hK, hj, hm, huni, hs,
    huni.surjective_of_cover 𝒰 h𝒰, hqa S G hG M K j hK hj hm huni⟩

/-- The scheme of maximal tori of a reductive group scheme is smooth,
surjective and relatively quasi-affine over its arbitrary base. -/
theorem maximalTorusScheme : MaximalTorusSchemeStatement.{u} :=
  maximalTorusScheme_of maximalTorusModuliQuasiAffine

end Langlands.GroupScheme
