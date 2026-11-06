import Langlands.GroupScheme.Reductive.SplitSemisimpleRootSpanSufficiency
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof

/-! # The split semisimplicity criterion

Milne Proposition 21.48 with Definition C.34, and its dual coroot form (proof of Milne
Proposition 21.49(a)): for a connected reductive group over a field with a split maximal torus
and a root datum, the group is semisimple exactly when the roots span a subgroup of finite index
of the character lattice, and exactly when the coroots span a subgroup of finite index of the
cocharacter lattice. -/

universe u

namespace Langlands.GroupScheme

/-- **Semisimplicity from the root datum** (Milne Proposition 21.48 with Definition C.34, and the
dual form used in the proof of Milne Proposition 21.49(a)). -/
theorem splitSemisimpleRootDatum : SplitSemisimpleRootDatumStatement.{u} :=
  splitSemisimpleRootDatum_of_maximalTorusCentralizer maximalTorusCentralizer

end Langlands.GroupScheme
