import Langlands.GroupScheme.SimplyConnected.FieldExtensionProof

/-! # The field-extension package for semisimplicity, simple connectedness and covers -/

universe u

namespace Langlands.GroupScheme

/-- **Field-extension package** (CGP, Corollary A.4.11(1); Milne, Propositions 19.10 and
19.13). Semisimplicity, algebraic simple connectedness and supplied simply connected covers
are all preserved by base change along an arbitrary field extension `K/k`. -/
theorem simplyConnected_fieldExtension : SimplyConnectedFieldExtensionStatement.{u} :=
  ⟨isSemisimpleFieldExtension, isSimplyConnectedFieldExtension,
    isSimplyConnectedCover_fieldExtension⟩

end Langlands.GroupScheme
