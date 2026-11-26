import Langlands.GroupScheme.DvrFiniteSmoothCoverStatement
import Langlands.GroupScheme.DvrSmoothGenericReduction
import Langlands.GroupScheme.DvrCoverAssembly
import Langlands.AlgebraicGeometry.DvrPotentialGenericReductionProof
import Langlands.AlgebraicGeometry.DvrStableNormalizationProof

/-! # Proof of the finite smooth cover after a DVR extension

The reduced generic subgroup closure (`DvrSmoothGenericReduction.reduction`, fed by the proof
of potential geometric reducedness) gives a finite surjective group map from a flat group with
smooth affine generic fibre. Stable normalization of that group
(`DvrCoverAssembly.smoothGenericCover`, fed by the proof of stable normalization) gives a
finite smooth cover of it, and `DvrCoverAssembly.Cover.comp` composes the two.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

/-- After a faithfully flat DVR extension, a flat separated finite-type group scheme over a DVR
with affine generic fibre admits a finite surjective homomorphism from a smooth, quasi-compact,
separated group scheme with affine generic fibre. -/
theorem dvrFiniteSmoothCover : DvrFiniteSmoothCoverStatement.{u} := by
  intro R _ _ _ K _ _ _ G hflat hlft hqc hsep hgen
  have := hflat
  have := hlft
  have := hqc
  have := hsep
  have := hgen
  let P := DvrSmoothGenericReduction.reduction R K G
    Langlands.AlgebraicGeometry.dvrPotentialGenericReduction
  have := P.flat
  have := P.surjective
  have := P.group_flat
  have := P.locallyOfFiniteType
  have := P.quasiCompact
  have := P.separated
  have := P.smoothGeneric
  have := P.affineGeneric
  let D := DvrCoverAssembly.smoothGenericCover P.group
    Langlands.AlgebraicGeometry.dvrStableNormalization
  let C := DvrCoverAssembly.Cover.comp P.base P.map P.finite P.map_surjective D
  exact ⟨C.ring, C.comm, C.domain, C.dvr, C.base, C.flat, C.surjective,
    C.group, C.map, C.smooth, C.quasiCompact, C.separated, C.affineGeneric,
    C.finite, C.map_surjective⟩

end Langlands.GroupScheme
