import Langlands.Cohomology.Tate.ZeroTransferDefinitions

universe u

open CategoryTheory

namespace Langlands.Tate

/-- Exact degree-zero normalization, coefficient naturality and subgroup compatibility laws. -/
def ZeroLaws : Prop :=
  ∀ (R G : Type u) [CommRing R] [Group G] [Fintype G],
    (∀ (A : Rep R G), Function.Surjective (zeroClass A) ∧
      (∀ a : A.ρ.invariants,
        (zeroEquiv A).hom (zeroClass A a) = (normImage A).mkQ a) ∧
      (∀ a : A.ρ.invariants, zeroClass A a = 0 ↔ a ∈ normImage A)) ∧
    (∀ (A B : Rep R G) (f : A ⟶ B) (a : A.ρ.invariants),
      (tateCohomologyFunctor 0).map f (zeroClass A a) =
        zeroClass B ((Rep.invariantsFunctor R G).map f a)) ∧
    (∀ (A B C : Rep R G) (φ : Pairing A B C)
      (a : A.ρ.invariants) (b : B.ρ.invariants),
      cupZero φ (zeroClass A a) (zeroClass B b) =
        zeroClass C (φ.onInvariants a b)) ∧
    (∀ (A B C A' B' C' : Rep R G)
      (φ : Pairing A B C) (φ' : Pairing A' B' C')
      (f : A ⟶ A') (g : B ⟶ B') (h : C ⟶ C'),
      (∀ a b, h.hom (φ.bilinear a b) = φ'.bilinear (f.hom a) (g.hom b)) →
      ∀ (a : tateCohomology A 0) (b : tateCohomology B 0),
        (tateCohomologyFunctor 0).map h (cupZero φ a b) =
          cupZero φ' ((tateCohomologyFunctor 0).map f a)
            ((tateCohomologyFunctor 0).map g b)) ∧
    (∀ (H : Subgroup G) [Fintype H] [Fintype (G ⧸ H)],
      (∀ (A : Rep R G),
        (∀ a : A.ρ.invariants,
          restrictionZero H A (zeroClass A a) =
            zeroClass (Rep.res H.subtype A) (invariantRestriction H A a)) ∧
        (∀ a : (Rep.res H.subtype A).ρ.invariants,
          corestrictionZero H A (zeroClass (Rep.res H.subtype A) a) =
            zeroClass A (cosetNorm H A a)) ∧
        (∀ a : tateCohomology A 0,
          corestrictionZero H A (restrictionZero H A a) = H.index • a)) ∧
      (∀ (A B C : Rep R G) (φ : Pairing A B C),
        (∀ (a : tateCohomology A 0) (b : tateCohomology B 0),
          restrictionZero H C (cupZero φ a b) =
            cupZero (φ.restrict H) (restrictionZero H A a) (restrictionZero H B b)) ∧
        (∀ (a : tateCohomology (Rep.res H.subtype A) 0) (b : tateCohomology B 0),
          corestrictionZero H C (cupZero (φ.restrict H) a (restrictionZero H B b)) =
            cupZero φ (corestrictionZero H A a) b)) ∧
      (∀ (A B : Rep R G) (f : A ⟶ B),
        (∀ a : tateCohomology A 0,
          (tateCohomologyFunctor 0).map ((Rep.resFunctor H.subtype).map f)
              (restrictionZero H A a) =
            restrictionZero H B ((tateCohomologyFunctor 0).map f a)) ∧
        (∀ a : tateCohomology (Rep.res H.subtype A) 0,
          (tateCohomologyFunctor 0).map f (corestrictionZero H A a) =
            corestrictionZero H B
              ((tateCohomologyFunctor 0).map ((Rep.resFunctor H.subtype).map f) a))))

end Langlands.Tate
