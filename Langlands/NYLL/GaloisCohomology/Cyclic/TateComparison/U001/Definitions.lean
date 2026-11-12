/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.Cohomology.Tate.ZeroDefinitions

/-!
# Degree-zero Tate boundary homology

Adapted from NYLL's `TateCohomology.isoZeroBoundary` by reusing the published
short-complex comparison `Langlands.Tate.zeroShortComplexIso`.
-/

noncomputable section

open CategoryTheory

namespace Langlands.NYLL.TateCohomology

universe u

/-- Degree-zero Tate cohomology is the homology of the standard boundary
short complex `A --N--> A --d₀₁--> C¹(G, A)` for every finite group. -/
def isoZeroBoundary {R G : Type u} [CommRing R] [Group G] [Fintype G]
    (A : Rep R G) :
    tateCohomology A 0 ≅
      (ShortComplex.mk A.norm.toModuleCatHom (groupCohomology.d₀₁ A)
        (Rep.norm_comp_d_eq_zero A)).homology :=
  ShortComplex.homologyMapIso (Langlands.Tate.zeroShortComplexIso A)

end Langlands.NYLL.TateCohomology
