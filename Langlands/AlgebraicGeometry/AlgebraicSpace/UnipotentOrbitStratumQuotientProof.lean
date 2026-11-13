import Langlands.AlgebraicGeometry.AlgebraicSpace.UnipotentOrbitQuotientStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.UnipotentOrbitStabilizerSmoothReduction
import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothStabilizerActionQuotientProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.OrbitStratumActionRestrictionProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.ActionQuotientFinitenessProof
import Langlands.GroupScheme.AffineCartierSmoothProof
import Langlands.GroupScheme.Unipotent.CharZeroConnectedProof
import Langlands.GroupScheme.ReducedBaseSmoothProof

/-!
# The quotient of an orbit-dimension stratum: proof

Clause 2 of Conrad's Example 5.5. Cartier's theorem makes `G` smooth. The action restricts
to the stratum `Z` with constant orbit dimension `d`. The stabilizer of the restricted
action is smooth over `Z` (SGA 3, Exposé VI_B, Corollaire 4.4 over a reduced base, with
unipotent groups in characteristic zero connected). The fppf quotient of `Z` by a smooth
group with smooth stabilizer is an algebraic space receiving a smooth surjective map from
`Z`, and it is quasi-separated and of finite presentation because `Z` is of finite type.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open _root_.AlgebraicGeometry
open Langlands (GroupScheme)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Conrad's Example 5.5, clause 2: the action of a unipotent algebraic group restricts to
an orbit-dimension stratum `Z`, with flat stabilizer, and the fppf quotient of `Z` is a
quasi-separated algebraic space of finite presentation receiving a flat surjective map
from `Z`. -/
theorem unipotentOrbitStratumQuotient : UnipotentOrbitStratumQuotientStatement.{u} := by
  have hB : UnipotentOrbitStabilizerSmoothStatement.{u} :=
    unipotentOrbitStabilizerSmooth_of_reducedBase_of_charZeroConnected
      GroupScheme.reducedBaseConnectedFibreSmooth GroupScheme.charZeroUnipotentConnected
  intro K _ _ hchar G hG V hV a d Z i hi hZ hrange
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
  -- The restricted action on `Z` and constant orbit dimension `d` on `Z`.
  obtain ⟨⟨b, hb⟩, hdim⟩ := orbitStratumActionRestriction K G hGs V hVl a d Z i hi hZ hrange
  -- The stabilizer of `b` is smooth over `Z`.
  have hstab := hB K G hG.1 hG.2.1 hG.2.2 Z hZ hZl b d (hdim b hb)
  -- The quotient algebraic space and its smooth surjective quotient map.
  obtain ⟨⟨X, π, hq⟩, hall⟩ := smoothStabilizerActionQuotient _ G Z b hGs hZl hstab
  obtain ⟨hsm, hsurj, hlft⟩ := hall X π hq
  have hGq : QuasiCompact G.X.hom := by
    have := hG.1
    infer_instance
  -- Quasi-separatedness and finite presentation of the quotient.
  obtain ⟨hqs, hfp⟩ := actionQuotientFiniteness K G Z b hGq hZl hZq X π hq hsm hsurj hlft
  -- A smooth representable map of presheaves is flat.
  have hflat : IsFlat π.hom := by
    refine MorphismProperty.relative_monotone ?_ π.hom hsm
    intro T T' g hg
    have : Smooth ((Over.forget _).map g) := hg
    exact (inferInstance : Flat ((Over.forget _).map g))
  refine ⟨b, hb, ?_, X, π, hq, hqs, hfp, hflat, hsurj⟩
  change Flat _
  infer_instance

end Langlands.AlgebraicGeometry.AlgebraicSpace
