import Langlands.AlgebraicGeometry.Picard.AmpleTensorStatement
import Langlands.AlgebraicGeometry.Picard.AmpleIsoProof
import Langlands.AlgebraicGeometry.Picard.TensorRankOneProof
import Langlands.AlgebraicGeometry.Picard.AffineGenerationLocusIntersectionProof
import Langlands.AlgebraicGeometry.Modules.TensorPowerIsomorphisms
import Langlands.AlgebraicGeometry.Modules.TensorPowerDistributivity
import Langlands.AlgebraicGeometry.Modules.PositiveSectionPowerGenerationLocusProof

/-! # Ampleness of tensor products of actual line bundles -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.SchemeModule Langlands.Scheme.Modules

/-- A line bundle representing the actual tensor product of two ample line bundles is ample. -/
theorem ampleTensor : AmpleTensorStatement.{u} := by
  intro X L M N ⟨e⟩ hL hM
  refine ⟨hL.1, fun x ↦ ?_⟩
  obtain ⟨n, hn, s, hxs, hs⟩ := hL.2 x
  obtain ⟨m, hm, t, hxt, _⟩ := hM.2 x
  let Ln : LineBundle X := ⟨tensorPow L.obj n, tensorPow_isLocallyFreeRankOne X L n⟩
  let Mm : LineBundle X := ⟨tensorPow M.obj m, tensorPow_isLocallyFreeRankOne X M m⟩
  let Lnm : LineBundle X := ⟨tensorPow Ln.obj m, tensorPow_isLocallyFreeRankOne X Ln m⟩
  let Mmn : LineBundle X := ⟨tensorPow Mm.obj n, tensorPow_isLocallyFreeRankOne X Mm n⟩
  let sm : GlobalSections Lnm.obj := sectionPow Ln.obj s m
  let tn : GlobalSections Mmn.obj := sectionPow Mm.obj t n
  let q : GlobalSections (tensorObj Lnm.obj Mmn.obj) :=
    tensorSection Lnm.obj Mmn.obj sm tn
  let E : tensorObj Lnm.obj Mmn.obj ≅ tensorPow N.obj (n * m) :=
    (tensorFunctor X).mapIso
        ((tensorPowMulIso L.obj n m).prod
          (tensorPowMulIso M.obj m n ≪≫
            eqToIso (congrArg (tensorPow M.obj) (Nat.mul_comm m n)))) ≪≫
      (tensorPowTensorIso L.obj M.obj (n * m)).symm ≪≫ tensorPowIso e (n * m)
  let r : N.powSections (n * m) := E.hom.app ⊤ q
  have hsm : trivializationOpen Lnm.obj sm = L.sectionOpen s :=
    trivializationOpen_sectionPow Ln s hm
  have htn : trivializationOpen Mmn.obj tn = M.sectionOpen t :=
    trivializationOpen_sectionPow Mm t hn
  have hopen : N.sectionOpen r = L.sectionOpen s ⊓ M.sectionOpen t := by
    change trivializationOpen (tensorPow N.obj (n * m)) (E.hom.app ⊤ q) = _
    rw [trivializationOpen_mapIso E q]
    change trivializationOpen (tensorObj Lnm.obj Mmn.obj)
      (tensorSection Lnm.obj Mmn.obj sm tn) = _
    rw [tensorSectionGenerationLocus X Lnm Mmn sm tn, hsm, htn]
  refine ⟨n * m, by simpa using Nat.mul_le_mul hn hm, r, ?_, ?_⟩
  · rw [hopen]
    exact ⟨hxs, hxt⟩
  · rw [hopen]
    exact affineGenerationLocusIntersection X Mm t (L.sectionOpen s) hs

end Langlands.AlgebraicGeometry.Picard
