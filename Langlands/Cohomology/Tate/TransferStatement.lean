import Langlands.Cohomology.Tate.TransferDefinitions

universe u

open CategoryTheory

namespace Langlands.Tate

/-- All-degree coefficient naturality, index identity, and scalar-split boundary laws. -/
def TransferLaws : Prop :=
  ∀ (R G : Type u) [CommRing R] [Group G] [Fintype G]
    (H : Subgroup G) [Fintype H] [Fintype (G ⧸ H)],
    (∀ (A B : Rep R G) (f : A ⟶ B) (n : ℤ),
      (∀ x : tateCohomology A n,
        (tateCohomologyFunctor n).map ((Rep.resFunctor H.subtype).map f)
            (restriction H A n x) =
          restriction H B n ((tateCohomologyFunctor n).map f x)) ∧
      (∀ x : tateCohomology (Rep.res H.subtype A) n,
        (tateCohomologyFunctor n).map f (corestriction H A n x) =
          corestriction H B n
            ((tateCohomologyFunctor n).map ((Rep.resFunctor H.subtype).map f) x))) ∧
    (∀ (A : Rep R G) (n : ℤ) (x : tateCohomology A n),
      corestriction H A n (restriction H A n x) = H.index • x) ∧
    (∀ (S : ShortComplex (Rep R G)) (hS : S.ShortExact),
      Nonempty (S.map (forget₂ (Rep R G) (ModuleCat R))).Splitting →
      ∀ n : ℤ,
        (∀ x : tateCohomology S.X₃ n,
          restriction H S.X₁ (n + 1) (TateCohomology.δ hS n x) =
            TateCohomology.δ (hS.map_of_exact (Rep.resFunctor H.subtype)) n
              (restriction H S.X₃ n x)) ∧
        (∀ x : tateCohomology (Rep.res H.subtype S.X₃) n,
          corestriction H S.X₁ (n + 1)
              (TateCohomology.δ (hS.map_of_exact (Rep.resFunctor H.subtype)) n x) =
            TateCohomology.δ hS n (corestriction H S.X₃ n x)))

end Langlands.Tate
