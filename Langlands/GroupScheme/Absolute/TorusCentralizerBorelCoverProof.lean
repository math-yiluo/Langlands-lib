import Langlands.GroupScheme.Absolute.TorusCentralizerBorelCoverStatement
import Langlands.GroupScheme.Absolute.TorusCentralizerBorelProof
import Langlands.GroupScheme.Absolute.BorelPointContainmentProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport
import Langlands.GroupScheme.Torus.CentralizerConnected
import Langlands.GroupScheme.Torus.CentralizerSmooth
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.SplitReflection

/-! # Points of a torus centralizer lie in Borel subgroups containing the torus -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every rational point of the centralizer of a closed torus in a smooth connected affine
group over an algebraically closed field lies in a Borel subgroup containing the torus
(Milne, Lemma 17.37). -/
theorem torusCentralizerBorelCover : TorusCentralizerBorelCoverStatement.{u} := by
  intro k _ _ G hGsmooth _ _ S s hS hs g hg
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hsplit := hS.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting
  obtain ⟨C, c, hc, hCsmooth, hrep⟩ :=
    torusCentralizer_hasSmoothClosedRepresentative s ⟨hsplit, hs⟩ hGsmooth
  let : Smooth C.X.hom := hCsmooth
  let : IsAffineHom C.X.hom := hc.isAffineHom
  let : ConnectedSpace C.X.left := hS.connectedSpace_centralizer s hrep
  rw [← hrep.2] at hg
  obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.mp hg
  obtain ⟨D, d, y, hd, hy⟩ := borelPointContainment k C x
  obtain ⟨B, i, hi, hSB, hr⟩ :=
    (torusCentralizerBorel k G S s hS hs C c hrep hc).2 inferInstance D d hd
  have hx : x ≫ c.hom.hom ∈ (SubgroupFunctor.range (d ≫ c)).carrier _ := by
    refine SubgroupFunctor.mem_range.mpr ⟨y, ?_⟩
    rw [Grp.comp_hom_hom, ← Category.assoc, hy]
  rw [hr] at hx
  obtain ⟨b, hb⟩ := SubgroupFunctor.mem_range.mp hx.2
  exact ⟨B, i, b, hi, hSB, hb⟩

end Langlands.GroupScheme
