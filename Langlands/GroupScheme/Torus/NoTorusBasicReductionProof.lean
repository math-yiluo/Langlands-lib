import Langlands.GroupScheme.Torus.NoTorusBasicReductionStatement
import Langlands.GroupScheme.Rational.RootSubgroupVectorTransport
import Langlands.GroupScheme.Rational.SplitUnipotentTransport
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.Unipotent.FieldReflectionProof

/-! # Conditional nilpotent and finite-field no-torus reductions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The two basic no-torus cases follow from their explicit structural inputs. -/
theorem noTorusBasicReduction : NoTorusBasicReductionStatement.{u} := by
  constructor
  · intro hstructure k _ G _ _ _ hnil hnotorus
    obtain ⟨T, i, Q, q, hmax, _, _, hQ, hq⟩ := hstructure k G hnil
    have hbot : RelativeRoot.IsFppfQuotient ⊥ q := by
      simpa only [hnotorus T hmax.1 i] using hq
    exact IsUnipotent.of_iso hbot.isoOfBot hQ
  · intro hfinite halgclosed k _ _ G _ _ _ hnotorus
    obtain ⟨T, i, hmax, hgeom⟩ := hfinite k G
    have hconn := G.connectedSpace_baseChange_of_smooth_affine (toAlgebraicClosure k)
    have : Smooth ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).X.hom := by
      change Smooth (pullback.snd G.X.hom (toAlgebraicClosure k))
      infer_instance
    have : IsAffineHom ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).X.hom := by
      change IsAffineHom (pullback.snd G.X.hom (toAlgebraicClosure k))
      infer_instance
    have hbot : SubgroupFunctor.range
        ((GroupScheme.baseChange (toAlgebraicClosure k)).map i) = ⊥ := by
      rw [SubgroupFunctor.range_baseChangeHom, hnotorus T hmax.1 i,
        SubgroupFunctor.bot_baseChange]
    exact IsUnipotent.of_baseChange
      (halgclosed (AlgebraicClosure k) _
        ((CommGroupScheme.baseChange (toAlgebraicClosure k)).obj T) _ hgeom hbot)

end Langlands.GroupScheme
