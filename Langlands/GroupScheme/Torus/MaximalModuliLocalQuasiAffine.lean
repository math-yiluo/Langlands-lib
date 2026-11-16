import Langlands.GroupScheme.Torus.MaximalModuliBaseChange
import Langlands.GroupScheme.Torus.MaximalModuliQuotientComparison
import Langlands.GroupScheme.Torus.RelativeTorusMultiplicativeType
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeQuotientStatement
import Langlands.GroupScheme.Torus.EtaleLocalMaximalExistenceProof
import Langlands.GroupScheme.Torus.MaximalTorusModuliQuasiAffineStatement
import Langlands.AlgebraicGeometry.QuasiAffineEtaleDescent

/-! # Local quasi-affine models from the multiplicative-type quotient statement -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.TorusSubgroupModuli

variable {S : Scheme.{u}} {G : GroupScheme S}
  {M : Over S} {K : CommGroupScheme M.left} {H : CommGroupScheme S}

/-- The general multiplicative-type quotient theorem supplies relative
quasi-affineness when a fixed maximal torus exists over the base. -/
theorem quasiAffineOver_of_fixedMaximalTorus
    (hq : RelativeMultiplicativeTypeQuotientStatement.{u})
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (j : K.toGrp ⟶ (baseChange M.hom).obj G) (huni : IsUniversalMaximal j)
    (hK : RelativeTorus.IsTorus K.toGrp) (hj : IsClosedSubgroup j)
    (hm : IsFibrewiseMaximalTorus j)
    (i : H.toGrp ⟶ G) (hH : RelativeTorus.IsTorus H.toGrp)
    (hi : IsClosedSubgroup i) (hmax : IsFibrewiseMaximalTorus i) :
    ∀ V : S.affineOpens, (M.hom ⁻¹ᵁ (V : S.Opens)).toScheme.IsQuasiAffine := by
  obtain ⟨⟨N, n, _, hn⟩, _, hN⟩ := hq S G H i hH.isMultiplicativeType hi
  obtain ⟨⟨Q, _, hQ⟩, _⟩ := hN N n hn
  exact quasiAffineOver_of_normalizerQuotient j huni hK hj hm i hH hi hmax n hn Q hQ

/-- An actual etale cover on which supplied universal maximal-torus moduli
are relatively quasi-affine, conditional on the general quotient theorem. -/
def quasiAffineLocalCoverOfQuotient
    (hq : RelativeMultiplicativeTypeQuotientStatement.{u}) (hG : IsReductive G)
    (j : K.toGrp ⟶ (baseChange M.hom).obj G) (huni : IsUniversalMaximal j)
    (hK : RelativeTorus.IsTorus K.toGrp) (hj : IsClosedSubgroup j)
    (hm : IsFibrewiseMaximalTorus j) :
    {𝒰 : S.Cover.{u} (Scheme.precoverage @Etale) // ∀ k, ∀ V : (𝒰.X k).affineOpens,
      (((Over.pullback (𝒰.f k)).obj M).hom ⁻¹ᵁ (V : (𝒰.X k).Opens)).toScheme.IsQuasiAffine} := by
  apply Classical.choice
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  obtain ⟨𝒰, h𝒰⟩ := etaleLocalMaximalTorusExistence S G hG
  refine ⟨⟨𝒰, fun k => ?_⟩⟩
  obtain ⟨H, i, hH, hi, hmax⟩ := h𝒰 k
  let f := 𝒰.f k
  let : Smooth ((baseChange f).obj G).X.hom :=
    inferInstanceAs (Smooth (pullback.snd G.X.hom f))
  let : IsAffineHom ((baseChange f).obj G).X.hom :=
    MorphismProperty.pullback_snd _ _ ‹IsAffineHom G.X.hom›
  exact quasiAffineOver_of_fixedMaximalTorus
    (S := 𝒰.X k) (G := (baseChange f).obj G) (M := (Over.pullback f).obj M)
    (K := (CommGroupScheme.baseChange (pullParameter f M).left).obj K)
    (H := H) hq (pullFamily f j) (huni.pullFamily f)
    (hK.baseChange (pullParameter f M).left) (isClosedSubgroup_pullFamily f j hj)
    (isFibrewiseMaximalTorus_pullFamily f j hm) i hH hi hmax

end Langlands.GroupScheme.TorusSubgroupModuli

namespace Langlands.GroupScheme

/-- The general multiplicative-type quotient theorem implies the unchanged
quasi-affineness target for every supplied universal maximal-torus family. -/
theorem maximalTorusModuliQuasiAffine_of_quotient
    (hq : RelativeMultiplicativeTypeQuotientStatement.{u}) :
    MaximalTorusModuliQuasiAffineStatement.{u} := by
  intro S G hG M K j hK hj hm huni
  let c := TorusSubgroupModuli.quasiAffineLocalCoverOfQuotient hq hG j huni hK hj hm
  exact Langlands.AlgebraicGeometry.QuasiAffineEtaleDescent.quasiAffineOver_of_etaleCover
    M.hom c.val c.property

end Langlands.GroupScheme
