import Langlands.GroupScheme.AntiAffineSmoothConnectedStatement
import Langlands.GroupScheme.AntiAffineSmoothCore
import Langlands.GroupScheme.ReducedCosetAffine
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-! # Smoothness and connectedness of anti-affine algebraic field groups -/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace IsAntiAffine

variable {k : Type u} [Field k]
  {N : GroupScheme (Spec (CommRingCat.of k))}

/-- Over a perfect field the actual reduced-subgroup quotient is affine,
so its smooth surjective projection forces an anti-affine group to be smooth. -/
theorem smooth_of_perfect_field [PerfectField k] [LocallyOfFiniteType N.X.hom]
    (hN : IsAntiAffine N) : Smooth N.X.hom := by
  let M := ReducedCosetAffine.model N
  have : IsAffine M.space.left := M.affine
  have : Smooth M.projection.left := M.smooth
  have : Surjective M.projection.left := M.surjective
  exact hN.smooth_of_affine_smooth_surjection M.space M.projection

/-- Smoothness of an anti-affine algebraic group over an arbitrary field. -/
theorem smooth [LocallyOfFiniteType N.X.hom] [QuasiCompact N.X.hom]
    (hN : IsAntiAffine N) : Smooth N.X.hom := by
  have : IsSeparated N.X.hom := fieldSeparated k N
  have : CompactSpace N.X.left := QuasiCompact.compactSpace_of_compactSpace N.X.hom
  have : QuasiSeparatedSpace N.X.left := quasiSeparatedSpace_of_quasiSeparated N.X.hom
  let b := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  let H := (GroupScheme.baseChange b).obj N
  have : LocallyOfFiniteType H.X.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd N.X.hom b))
  have hH : IsAntiAffine H := hN.baseChange (algebraMap k (AlgebraicClosure k))
  have hs : Smooth H.X.hom := hH.smooth_of_perfect_field
  obtain ⟨hf, hsurj⟩ := (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))).mpr
    (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  have : QuasiCompact b := inferInstanceAs (QuasiCompact
    (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))
  exact MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    ⟨⟨hsurj, hf⟩, inferInstance⟩ hs

end IsAntiAffine

/-- Anti-affine algebraic field groups are smooth and connected, without
perfectness or affine ambient hypotheses. -/
theorem antiAffineSmoothConnected : AntiAffineSmoothConnectedStatement.{u} := by
  intro k _ N hft hqc hN
  have : LocallyOfFiniteType N.X.hom := hft
  have : QuasiCompact N.X.hom := hqc
  exact ⟨hN.smooth, hN.connectedSpace⟩

end Langlands.GroupScheme
