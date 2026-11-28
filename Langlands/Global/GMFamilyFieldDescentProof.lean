import Langlands.Global.GMFamilyFieldDescentAssembly
import Langlands.GroupScheme.Rational.FieldLeviSplitComponentProof
import Langlands.GroupScheme.Rational.LeviSplitComponentRootDatumProof
import Langlands.GroupScheme.Lie.LeviWeightFibreDeterminantProof

/-!
# Field-extension descent for (G,M)-families

Proof of `FieldExtensionDescentStatement` (J. Arthur, *An introduction to the trace formula*
(2005), Lemma 17.5 and (17.13)): the conditional theorem `fieldExtensionDescent_of_inputs`
applied to the proofs of its three group-theoretic inputs.
-/

universe u

namespace Langlands.GMFamily

open Langlands.GroupScheme

/-- Field-extension descent for the (G,M)-families of nested rational Levi subgroups
(Arthur 2005, Lemma 17.5 and (17.13)). -/
theorem fieldExtensionDescent : FieldExtensionDescentStatement.{u} :=
  fieldExtensionDescent_of_inputs fieldLeviSplitComponentInclusion leviWeightFibreDeterminant
    leviSplitComponentRootDatum

end Langlands.GMFamily
