import Langlands.AlgebraicGeometry.AlgebraicSpace.UnipotentOrbitQuotientStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.UnipotentOrbitStabilizerSmoothReduction
import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothStabilizerActionQuotientProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.OrbitStratumActionRestrictionProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.ActionQuotientFinitenessProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.LocallySeparatedRationalPointsProof
import Langlands.GroupScheme.AffineCartierSmoothProof
import Langlands.GroupScheme.Unipotent.CharZeroConnectedProof
import Langlands.GroupScheme.ReducedBaseSmoothProof

/-!
# Rational points of the quotient of an orbit-dimension stratum: proof

Clause 3 of Conrad's Example 5.5. Given a locally separated fppf quotient `X` of the
stratum `Z`, the quotient map is smooth and surjective and `X` is locally of finite type
(the stabilizer is smooth by SGA 3, Exposé VI_B, Corollaire 4.4 over a reduced base, and
`G` is smooth by Cartier's theorem). Since `Z` is of finite type, `X` is quasi-separated.
A quasi-separated, locally separated algebraic space locally of finite type over a
henselian valued field has locally Hausdorff rational points, with the stated local
compactness and total disconnectedness.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open _root_.AlgebraicGeometry
open Langlands (GroupScheme)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Conrad's Example 5.5, clause 3, for locally separated quotients: every locally
separated fppf quotient of an orbit-dimension stratum `Z` by a restricted action of a
unipotent algebraic group has locally Hausdorff rational points, locally compact when `K`
is locally compact and locally totally disconnected when `K` is non-archimedean. -/
theorem unipotentOrbitQuotientPointTopology :
    UnipotentOrbitQuotientPointTopologyStatement.{u} := by
  have hB : UnipotentOrbitStabilizerSmoothStatement.{u} :=
    unipotentOrbitStabilizerSmooth_of_reducedBase_of_charZeroConnected
      GroupScheme.reducedBaseConnectedFibreSmooth GroupScheme.charZeroUnipotentConnected
  intro K _ hK hchar G hG V hV a d Z i hi hZ hrange b hb X π hq hls
  have := hchar
  -- Cartier: `G` is smooth.
  have hGs : Smooth G.X.hom := GroupScheme.affineCartierSmooth K G hG.1 hG.2.1
  -- `Z` is locally of finite type and quasi-compact over `K`, as it is immersed in `V`.
  have hVl : LocallyOfFiniteType V.hom := hV.2.1
  have hZl : LocallyOfFiniteType Z.hom := by
    rw [← Over.w i]
    infer_instance
  have hZq : QuasiCompact Z.hom := by
    have : IsLocallyNoetherian V.left := LocallyOfFiniteType.isLocallyNoetherian V.hom
    have : QuasiCompact V.hom := hV.2.2
    have : CompactSpace V.left := QuasiCompact.compactSpace_of_compactSpace V.hom
    have : IsNoetherian V.left := ⟨⟩
    have : TopologicalSpace.NoetherianSpace Z.left :=
      (Scheme.Hom.isEmbedding i.left).isInducing.noetherianSpace
    infer_instance
  -- Every action on `Z` making `i` equivariant has constant orbit dimension `d`.
  obtain ⟨-, hdim⟩ := orbitStratumActionRestriction K G hGs V hVl a d Z i hi hZ hrange
  -- The stabilizer of `b` is smooth over `Z`.
  have hstab := hB K G hG.1 hG.2.1 hG.2.2 Z hZ hZl b d (hdim b hb)
  -- The given quotient map is smooth and surjective, and `X` is locally of finite type.
  obtain ⟨-, hall⟩ := smoothStabilizerActionQuotient _ G Z b hGs hZl hstab
  obtain ⟨hsm, hsurj, hlft⟩ := hall X π hq
  have hGq : QuasiCompact G.X.hom := by
    have := hG.1
    infer_instance
  -- `X` is quasi-separated.
  obtain ⟨hqs, -⟩ := actionQuotientFiniteness K G Z b hGq hZl hZq X π hq hsm hsurj hlft
  exact locallySeparatedRationalPoints K hK X ⟨⟨hqs, hlft⟩, hls⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace
