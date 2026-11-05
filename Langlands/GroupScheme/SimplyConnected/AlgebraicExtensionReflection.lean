import Langlands.GroupScheme.SimplyConnected.AlgebraicExtensionReflectionStatement
import Langlands.GroupScheme.Reductive.AlgebraicExtensionReflectionProof
import Langlands.GroupScheme.Reductive.AlgebraicExtensionAscent
import Langlands.GroupScheme.CentralIsogeny.BaseChange
import Langlands.GroupScheme.BaseChangeReflection

/-! # Simple connectedness reflected by algebraic field extensions -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Simple connectedness reflects along every algebraic extension of fields. -/
theorem IsSimplyConnected.of_algebraicExtension
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    [Algebra.IsAlgebraic k K]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsSimplyConnected
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G)) :
    IsSimplyConnected G := by
  refine ⟨semisimpleAlgebraicExtensionReflection k K G hG.isSemisimple, ?_⟩
  intro H f hH hf
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have : IsIso ((GroupScheme.baseChange b).map f) :=
    hG.central_isogeny_isIso _ _ hH.baseChange_of_algebraicExtension (hf.baseChange b)
  obtain ⟨hsurj, hflat, hqc⟩ := fieldExtension_fpqc k K
  let : Surjective b := hsurj
  let : Flat b := hflat
  let : QuasiCompact b := hqc
  exact isIso_of_baseChange b f

/-- The exact published algebraic-extension reflection proposition. -/
theorem simplyConnectedAlgebraicExtensionReflection :
    SimplyConnectedAlgebraicExtensionReflectionStatement.{u} :=
  fun _ _ _ _ _ _ _ hG => IsSimplyConnected.of_algebraicExtension hG

end Langlands.GroupScheme
