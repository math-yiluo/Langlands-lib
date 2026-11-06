import Langlands.Global.AdelicGroupPointTopology

/-! # Compact open identity neighborhoods on actual finite adelic points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField Filter
open scoped CategoryTheory.MonObj Topology

namespace Langlands.Global

/-- The original finite adelic point topology is totally disconnected.
Finite type gives a neighborhood basis of actual compact open subgroups. -/
def FiniteAdelicGroupCompactOpenBasisStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left],
    TotallyDisconnectedSpace (FiniteAdelicGroupPoints F G) ∧
      ∀ [LocallyOfFiniteType G.X.hom],
        (𝓝 (1 : FiniteAdelicGroupPoints F G)).HasBasis
          (fun K : OpenSubgroup (FiniteAdelicGroupPoints F G) =>
            IsCompact (K : Set (FiniteAdelicGroupPoints F G)))
          (fun K => (K : Set (FiniteAdelicGroupPoints F G)))

end Langlands.Global
