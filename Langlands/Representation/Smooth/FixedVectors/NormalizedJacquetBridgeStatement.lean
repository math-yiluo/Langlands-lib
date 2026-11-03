import Langlands.Representation.Aubert.General.Parabolic
import Langlands.Representation.Jacquet.IwahoriContraction
import Langlands.Representation.Category.Subquotients

/-! # The actual normalized Jacquet bridge for fixed-vector detection -/

set_option autoImplicit false

namespace Langlands

universe uG uV

/-- Generation, actual subquotient occurrence and nonzero fixed-vector lifting
for the intrinsic Haar-normalized Jacquet functor. Structural realizations
remain explicit. -/
def NormalizedJacquetFixedVectorBridgeStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G]
    [LocallyCompactSpace G] [NonarchimedeanGroup G]
    (N M Nbar : Subgroup G) (hN : IsClosed (N : Set G))
    (hMN : M ≤ Subgroup.normalizer N),
    IsClosed (M : Set G) →
    (∀ s : Finset N, ∃ L : OpenSubgroup N,
      IsCompact (L : Set N) ∧ ∀ n ∈ s, n ∈ L) →
    ∀ (K : OpenSubgroup G) (K₀ : Subgroup G),
      IsCompact (K : Set G) →
      K₀ ≤ Subgroup.normalizer K.toSubgroup →
      (∀ x : G, ∃ m ∈ M, ∃ n ∈ N, ∃ k ∈ K₀, x = m * n * k) →
      ∀ (g : G), Jacquet.IsIwahoriContraction K N M Nbar g →
      ∀ (A D : SmoothRep.{0, uG, uV} ℂ G),
        FiniteDimensional ℂ (fixedVectors A.representation K.toSubgroup) →
        (∀ S : Subrepresentation A.representation,
          fixedVectors A.representation K.toSubgroup ≤ S.toSubmodule → S = ⊤) →
        SmoothRep.IsSubquotient D A →
        let χ := HaarModulus.closedInverseHalfCharacter N hN M hMN
        let JA := (Aubert.General.normalizedJacquetFunctor N M hN hMN).obj A
        let JD := (Aubert.General.normalizedJacquetFunctor N M hN hMN).obj D
        K.toSubgroup.comap M.subtype ≤ χ.ker ∧
        (∀ S : Subrepresentation JA.representation,
          fixedVectors JA.representation (K.toSubgroup.comap M.subtype) ≤ S.toSubmodule →
            S = ⊤) ∧
        SmoothRep.IsSubquotient JD JA ∧
        ((∃ w : JD, w ∈ fixedVectors JD.representation (K.toSubgroup.comap M.subtype) ∧
            w ≠ 0) →
          ∃ v : D, v ∈ fixedVectors D.representation K.toSubgroup ∧ v ≠ 0)

end Langlands
