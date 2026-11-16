import Langlands.LinearAlgebra.ArthurCombinatoricsSigmaSupport
import Langlands.LinearAlgebra.ArthurCombinatoricsLanglandsLemma

/-!
# Arthur's combinatorial lemmas

The conjunction `ArthurCombinatoricsStatement`, assembled from its six conjuncts, each proved as
its own named theorem:

* `alternatingSumStatement` (Arthur 1978, Proposition 1.1);
* `tauTauHatVanishingStatement` (the remark after Arthur 1978, Corollary 6.2);
* `sigmaCharacterizationStatement` (Arthur 1978, Lemma 6.1);
* `langlandsCombinatorialLemmaStatement` (Arthur 1978, Lemma 6.3);
* `tauTauHatSigmaExpansionStatement` (Arthur 2005, (8.2));
* `sigmaSupportStatement` (Arthur 2005, Lemma 8.3).
-/

universe u

namespace Langlands.ArthurCombinatorics

/-- **Arthur's combinatorial lemmas** for standard parabolic subgroups. -/
theorem arthurCombinatoricsStatement : ArthurCombinatoricsStatement.{u} :=
  ⟨alternatingSumStatement, tauTauHatVanishingStatement, sigmaCharacterizationStatement,
    langlandsCombinatorialLemmaStatement, tauTauHatSigmaExpansionStatement,
    sigmaSupportStatement⟩

end Langlands.ArthurCombinatorics
