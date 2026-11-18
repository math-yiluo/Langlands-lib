import Langlands.GroupScheme.Reductive.SpecialLinearHighestWeight
import Langlands.GroupScheme.Reductive.PinningGroupIsoTransport

/-! # Actual fundamental highest weights for the split norm-one representation -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.GroupScheme

namespace SpecialLinear

/-- In every matrix dimension at least two the actual column representation has
a fundamental highest weight for a coordinate pinning. -/
theorem exists_fundamentalHighestWeight (k : Type u) [Field k] (m : ℕ) (hm : 2 ≤ m) :
    ∃ (p : SplitPinning (groupScheme (Fin m) (CommRingCat.of k)))
      (hspan : p.rootDatum.corootSpan ℤ = ⊤) (a : p.base.support),
      p.IsHighestWeight (inclusion (Fin m) (CommRingCat.of k))
        (Langlands.RootDatum.fundamentalWeightBasis p.rootDatum p.base hspan a) := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hm
  have hsize : m = n + 1 + 1 := by omega
  rw [hsize]
  obtain ⟨J, hJ, P, hP, hred, B, e, hspan, _, hweight⟩ :=
    specialLinearFirstFundamentalHighestWeight k n
  have : Finite J := hJ
  exact ⟨FinSucc.coordinatePinning P hP hred B, hspan, e.symm 0, hweight⟩

end SpecialLinear

namespace CentralSimpleUnits.SplitRepresentation

open Langlands.CentralSimple

variable (k A : Type u) [Field k] [Ring A] [Algebra k A]
    [FiniteDimensional k A] [Algebra.IsCentral k A] [IsSimpleRing A]
    {L : Type u} [Field L] [Algebra k L]
    (e : L ⊗[k] A ≃ₐ[L]
      Matrix (Fin (reducedDegree k A)) (Fin (reducedDegree k A)) L)

/-- Every actual standard special-linear highest weight transports through the prescribed chart. -/
theorem representation_isHighestWeight
    (p : SplitPinning
      (SpecialLinear.groupScheme (Fin (reducedDegree k A)) (CommRingCat.of L)))
    (lam : characterLattice p.torus)
    (hweight : p.IsHighestWeight
      (SpecialLinear.inclusion (Fin (reducedDegree k A)) (CommRingCat.of L)) lam) :
    (p.mapGroupIso (Splitting.splittingIso k A e).symm).IsHighestWeight
      (representation k A e) lam :=
  hweight.mapGroupIso (Splitting.splittingIso k A e).symm

/-- For every actual splitting chart in degree at least two, the original
norm-one representation has a transported fundamental highest weight. -/
theorem exists_fundamentalHighestWeight (hdegree : 2 ≤ reducedDegree k A) :
    ∃ (p : SplitPinning
      (SpecialLinear.groupScheme (Fin (reducedDegree k A)) (CommRingCat.of L)))
      (hspan : p.rootDatum.corootSpan ℤ = ⊤) (a : p.base.support),
      p.IsHighestWeight
        (SpecialLinear.inclusion (Fin (reducedDegree k A)) (CommRingCat.of L))
        (Langlands.RootDatum.fundamentalWeightBasis p.rootDatum p.base hspan a) ∧
      (p.mapGroupIso (Splitting.splittingIso k A e).symm).IsHighestWeight
        (representation k A e)
        (Langlands.RootDatum.fundamentalWeightBasis p.rootDatum p.base hspan a) := by
  obtain ⟨p, hspan, a, hweight⟩ :=
    SpecialLinear.exists_fundamentalHighestWeight L (reducedDegree k A) hdegree
  exact ⟨p, hspan, a, hweight, representation_isHighestWeight k A e p _ hweight⟩

end CentralSimpleUnits.SplitRepresentation

/-- The actual norm-one column representation has an actual fundamental highest
weight over its unconditionally constructed finite Galois splitting field. -/
def NormOneFundamentalHighestWeightStatement : Prop :=
  ∀ (k A : Type u) [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
    [Algebra.IsCentral k A] [IsSimpleRing A], 2 ≤ Langlands.CentralSimple.reducedDegree k A →
    let G := (GroupScheme.baseChange
      (CentralSimpleUnits.Splitting.baseMap (K := k)
        (L := Langlands.CentralSimple.finiteGaloisSplittingField k A))).obj
          (CentralSimpleUnits.normOne k A)
    ∃ (p : SplitPinning G) (hspan : p.rootDatum.corootSpan ℤ = ⊤) (a : p.base.support),
      p.IsHighestWeight (CentralSimpleUnits.SplitRepresentation.canonicalRepresentation k A)
        (Langlands.RootDatum.fundamentalWeightBasis p.rootDatum p.base hspan a)

theorem normOneFundamentalHighestWeight :
    NormOneFundamentalHighestWeightStatement.{u} := by
  intro k A _ _ _ _ _ _ hdegree
  obtain ⟨p, hspan, a, _, hweight⟩ :=
    CentralSimpleUnits.SplitRepresentation.exists_fundamentalHighestWeight k A
      (Langlands.CentralSimple.finiteGaloisSplittingChart k A) hdegree
  exact ⟨p.mapGroupIso
    (CentralSimpleUnits.Splitting.splittingIso k A
      (Langlands.CentralSimple.finiteGaloisSplittingChart k A)).symm, hspan, a, hweight⟩

end Langlands.GroupScheme
