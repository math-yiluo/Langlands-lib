import Langlands.GroupScheme.Rational.StandardMaximalLeviWeylProof

/-! # Standard Levi transporter cosets -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.Aubert.General.RationalPointFamily
open Langlands.AlgebraicGeometry.PointTopology

/-- The coset comparison at the beginning of Renard VII.1.3, for any standard Levi `L_I`.
It identifies `W(L_I, *)/W_I` with the left cosets `g L_I(k)` such that `g L_I(k) g⁻¹` is
standard. On a normalizer point the equivalence sends its Weyl coset to its point coset. -/
def StandardLeviTransporterCosetsStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    IsGenericCocharacter i ν →
    ∀ I : Finset (SimpleRoot i ν),
      let isTransporter : RationalPoint k G.X → Prop := fun g =>
        ∃ J : Finset (SimpleRoot i ν),
          (levi i ν I).map (MulAut.conj g : RationalPoint k G.X →* RationalPoint k G.X) =
            levi i ν J
      let pointCosets : Set (RationalPoint k G.X ⧸ levi i ν I) :=
        QuotientGroup.mk '' {g | isTransporter g}
      ∃ e : StandardMaximalLeviWeyl.cosets I ≃ pointCosets,
        ∀ (x : StandardMaximalLeviWeyl.cosets I) (n : normalizerPoints i),
          x.val = QuotientGroup.mk (QuotientGroup.mk n : relativeWeylGroup i) →
            (e x).val = QuotientGroup.mk (n : RationalPoint k G.X)

end Langlands.GroupScheme
