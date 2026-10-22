import Langlands.Cohomology.Tate.CupDefinitions

universe u

open CategoryTheory
open scoped MonoidalCategory TensorProduct

namespace Langlands.Tate

/-- Normalization, naturality, tensor boundary signs, restriction and projection for Tate cups. -/
def CupLaws : Prop :=
  ∀ (R G : Type u) [CommRing R] [Group G] [Fintype G],
    (∀ (A B C : Rep R G) (φ : Pairing A B C),
      cup φ 0 0 = cupZero φ) ∧
    (∀ (A B C : Rep R G) (φ : Pairing A B C)
      (a : A.ρ.invariants) (b : B.ρ.invariants),
      cup φ 0 0 (zeroClass A a) (zeroClass B b) =
        zeroClass C (φ.onInvariants a b)) ∧
    (∀ (A A' B B' C C' : Rep R G) (φ : Pairing A B C) (φ' : Pairing A' B' C')
      (f : A ⟶ A') (g : B ⟶ B') (h : C ⟶ C'),
      (∀ a b, h.hom (φ.bilinear a b) = φ'.bilinear (f.hom a) (g.hom b)) →
      ∀ (p q : ℤ) (a : tateCohomology A p) (b : tateCohomology B q),
        (tateCohomologyFunctor (p + q)).map h (cup φ p q a b) =
          cup φ' p q ((tateCohomologyFunctor p).map f a)
            ((tateCohomologyFunctor q).map g b)) ∧
    (∀ (S : ShortComplex (Rep R G)) (hS : S.ShortExact)
      (B : Rep R G) (hB : (S.map (MonoidalCategory.tensorRight B)).ShortExact)
      (p q : ℤ) (x : tateCohomology S.X₃ p) (b : tateCohomology B q),
      tensorCup S.X₁ B (p + 1) q (TateCohomology.δ hS p x) b =
        (tateDegreeIso (S.X₁ ⊗ B) (show (p + q) + 1 = (p + 1) + q by omega)).hom
          (TateCohomology.δ hB (p + q) (tensorCup S.X₃ B p q x b))) ∧
    (∀ (S : ShortComplex (Rep R G)) (hS : S.ShortExact)
      (A : Rep R G) (hA : (S.map (MonoidalCategory.tensorLeft A)).ShortExact)
      (p q : ℤ) (a : tateCohomology A p) (b : tateCohomology S.X₃ q),
      tensorCup A S.X₁ p (q + 1) a (TateCohomology.δ hS q b) =
        (p.negOnePow : ℤ) •
          (tateDegreeIso (A ⊗ S.X₁) (show (p + q) + 1 = p + (q + 1) by omega)).hom
            (TateCohomology.δ hA (p + q) (tensorCup A S.X₃ p q a b))) ∧
    (∀ (H : Subgroup G) [Fintype H] [Fintype (G ⧸ H)]
      (A B C : Rep R G) (φ : Pairing A B C) (p q : ℤ),
      (∀ (a : tateCohomology A p) (b : tateCohomology B q),
        restriction H C (p + q) (cup φ p q a b) =
          cup (φ.restrict H) p q (restriction H A p a) (restriction H B q b)) ∧
      (∀ (a : tateCohomology (Rep.res H.subtype A) p) (b : tateCohomology B q),
        corestriction H C (p + q) (cup (φ.restrict H) p q a (restriction H B q b)) =
          cup φ p q (corestriction H A p a) b))

end Langlands.Tate
