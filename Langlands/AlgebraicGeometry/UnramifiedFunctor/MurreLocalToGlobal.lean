import Langlands.AlgebraicGeometry.UnramifiedFunctor.EtaleLocusAssembly
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreGenericNoLargerLiftProof
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreEtaleLocusClosedProof
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCharts
import Langlands.AlgebraicGeometry.UnramifiedFunctor.ChartGluingRepr
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreLocalToGlobalReduction

/-! # Murre's Proposition 2: representability is local on the base

Proof of `MurreLocalToGlobalStatement` (Murre, Bourbaki exp. 294, Proposition 2) by
assembling its published steps:

* Lemma 3 (gluing of formally unramified charts): `ChartGluing.murreChartGluing`;
* Lemma 2 (openness of the étale locus): its closed-subscheme case
  `EtaleLocus.closedEtaleLocusOpen_of_generic`, fed with the generic-point case
  `EtaleLocus.genericNoLargerLift`, and then reduced to the general case by
  `EtaleLocus.murreEtaleLocusOpen_of_closed`;
* the inductive chart-construction step of Proposition 2, using Lemma 2:
  `Charts.murreChartsFromEtaleLocus`;
* the reduction of Proposition 2 to chart existence and Lemma 3: `murreLocalToGlobal_of_steps`. -/

universe u v

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

/-- Murre's Proposition 2 (Bourbaki exp. 294): over a locally noetherian base `S`, a
presheaf `F` on `Over S` satisfying Murre's conditions whose base change to
`Spec 𝒪_{S,s}` is representable by a separated, locally of finite type, formally
unramified scheme for every point `s` is itself so representable. -/
theorem murreLocalToGlobal : MurreLocalToGlobalStatement.{u, v} :=
  murreLocalToGlobal_of_steps ⟨ChartGluing.murreChartGluing,
    Charts.murreChartsFromEtaleLocus (EtaleLocus.murreEtaleLocusOpen_of_closed
      (EtaleLocus.closedEtaleLocusOpen_of_generic EtaleLocus.genericNoLargerLift))⟩

end Langlands.AlgebraicGeometry.UnramifiedFunctor
