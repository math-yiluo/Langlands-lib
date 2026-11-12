import Langlands.GroupScheme.Reductive.SteinbergBigCellReduction
import Langlands.GroupScheme.Reductive.SteinbergBigCellRootCorootAssembly
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.SimplyConnected.SplitNecessity

/-! # The simply connected positive-characteristic conjugation map -/

universe u

namespace Langlands.GroupScheme

/-- **The positive-characteristic endomorphism-map input to Haboush's theorem**
(Mumford–Fogarty–Kirwan, *Geometric Invariant Theory*, 3rd ed., Appendix 1.A, p.192).
For a simply connected semisimple group over an algebraically closed field of prime
characteristic, a nonzero vector fixed on all test schemes maps to a nonzero scalar
identity under an actual conjugation-equivariant linear map. The Steinberg big-cell data
come from root-datum existence and integral coroot generation, then covariant exhaustion
and Steinberg tensor embeddings give the map. -/
theorem simplyConnectedPositiveCharConjugationMap :
    SimplyConnectedPositiveCharConjugationMapStatement.{u} :=
  simplyConnectedPositiveCharConjugationMap_of_bigCell
    (steinbergBigCell_of_rootAndCoroot rootDatumExistence splitSimplyConnectedCorootSpan)

end Langlands.GroupScheme
