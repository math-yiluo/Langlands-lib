import Langlands.AlgebraicGeometry.Modules.FaithfullyFlatPullbackDescent
import Langlands.AlgebraicGeometry.Modules.CoherentClosure
import Langlands.AlgebraicGeometry.Modules.PullbackQuasicoherent

/-! # Quasi-coherence detected by affine faithfully flat pullback -/

noncomputable section

universe u

open CategoryTheory Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.AlgebraicGeometry.Modules

variable {X Y : Scheme.{u}} (p : X ⟶ Y)

/-- Quasi-coherence descends along an affine flat surjection, for ordinary modules. -/
lemma isQuasicoherent_of_pullback_of_affine_flat_surjective
    [IsAffineHom p] [Flat p] [Surjective p] (M : Y.Modules)
    [((Scheme.Modules.pullback p).obj M).IsQuasicoherent] : M.IsQuasicoherent := by
  let L := Scheme.Modules.pullback p
  let R := Scheme.Modules.pushforward p
  let adj := Scheme.Modules.pullbackPushforwardAdjunction p
  have := pullback_reflectsIsomorphisms_of_flat_surjective p
  have := flatPullbackExact X Y p inferInstance
  have : ReflectsLimitsOfShape WalkingParallelPair L :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  let f : R.obj (L.obj M) ⟶ R.obj (L.obj (R.obj (L.obj M))) :=
    R.map (L.map (adj.unit.app M))
  let g : R.obj (L.obj M) ⟶ R.obj (L.obj (R.obj (L.obj M))) :=
    adj.unit.app (R.obj (L.obj M))
  have : (R.obj (L.obj M)).IsQuasicoherent :=
    QuasicoherentLocal.isQuasicoherent_pushforward p _
  have : (R.obj (L.obj (R.obj (L.obj M)))).IsQuasicoherent :=
    QuasicoherentLocal.isQuasicoherent_pushforward p _
  have hQ := QuasicoherentLocal.isQuasicoherent_kernel (f - g)
  let h := Comonad.ComonadicityInternal.unitEqualizerOfCoreflectsEqualizer adj M
  let e : M ≅ kernel (f - g) :=
    (Preadditive.isLimitKernelForkOfFork h).conePointUniqueUpToIso (limit.isLimit _)
  exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso e.symm hQ

/-- Affine flat surjective pullback detects and preserves quasi-coherence. -/
lemma isQuasicoherent_iff_pullback_of_affine_flat_surjective
    [IsAffineHom p] [Flat p] [Surjective p] (M : Y.Modules) :
    M.IsQuasicoherent ↔ ((Scheme.Modules.pullback p).obj M).IsQuasicoherent := by
  constructor
  · intro hM
    exact Langlands.Scheme.Modules.isQuasicoherent_pullback p M
  · intro hM
    exact isQuasicoherent_of_pullback_of_affine_flat_surjective p M

end Langlands.AlgebraicGeometry.Modules
