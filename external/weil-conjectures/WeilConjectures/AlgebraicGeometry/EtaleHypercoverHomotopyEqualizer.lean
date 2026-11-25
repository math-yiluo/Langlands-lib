/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSplitEtaleHypercover
public import WeilConjectures.AlgebraicGeometry.EtaleHypercover
import WeilConjectures.AlgebraicGeometry.EtaleOrdinalPathHypercover

/-! Intermediate construction for finite split hypercover refinement. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FiniteSplitEtaleHypercover

set_option linter.unusedVariables false in
/-- Source: Stacks Project, Hypercoverings, Tags 0DAV, 094K, 01GS.

Proof: Use the ordered join of two copies of [n], namely [2n+1], as an explicit
simplicial path object for V. The cut maps give its elementary endpoint homotopy.
Pull the two endpoint maps back along (a,b). To check its matching covers, first
pull back U's matching cover. The resulting endpoint and lower doubled-face data
glue on a finite subcomplex of the standard (2n+1)-simplex. Finite-simplex lifting
in V extends this family locally. The endpoint pullback universal property gives
local lifts of the matching datum, proving the required surjectivity. The projection
to U and the explicit cut homotopy then give the asserted witnesses.
(auxiliary; not a blueprint node) -/
theorem exists_etale_hypercover_homotopy_equalizer
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (U V : FiniteSplitEtaleHypercover X) (a b : U.Refinement V) :
    ∃ (K : SimplicialObject X.Etale) (hK : IsEtaleHypercover K)
      (c : K ⟶ U.simplicial), Nonempty (SimplicialObject.Homotopy (c ≫ a) (c ≫ b)) := by
  refine ⟨SimplicialObject.ordinalPathPullback a b, ?_,
    SimplicialObject.ordinalPathPullbackFst a b,
    ⟨SimplicialObject.ordinalPathPullbackHomotopy a b⟩⟩
  apply EtaleSimplicialMatching.isEtaleHypercover_ordinalPathPullback a b
  · intro n
    exact ⟨U.matching n, U.projection n, U.matchingMap n, U.projection_naturality n,
      U.matching_universal n, U.matchingMap_projection n, U.matching_cover n⟩
  · intro n
    exact ⟨V.matching n, V.projection n, V.matchingMap n, V.projection_naturality n,
      V.matching_universal n, V.matchingMap_projection n, V.matching_cover n⟩

end AlgebraicGeometry.FiniteSplitEtaleHypercover
