import Langlands.GroupScheme.Torus.EndomorphismDichotomy

/-! # Proof of the actual torus endomorphism dichotomy

The mathematical proof is Worker 1369's published `torusEndomorphismDichotomy`.
This module checks it at the exact existing proposition without adding a public alias.
-/

namespace Langlands.GroupScheme

universe u

-- Check the published theorem at the exact target and universe.
example : TorusEndomorphismDichotomyStatement.{u} :=
  torusEndomorphismDichotomy.{u}

end Langlands.GroupScheme
