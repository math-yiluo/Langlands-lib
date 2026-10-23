import Langlands.AbelianScheme.Tate.MultiplicativeRationalPrimeBaseChange

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Gm.TateComparison

universe u

/-- Identity coherence for the actual finite multiplicative torsion comparisons. -/
def LevelBaseChangeIdentity : Prop :=
  ∀ (S : Scheme.{u}) (T : Over S) (n : ℕ) (x : Tate.Level (Gm S).toGrp T n),
    levelBaseChange (𝟙 S) T n x =
      Tate.levelRestrict (Gm S).toGrp ((Over.mapId S).hom.app T) n x

/-- Composition coherence with the canonical reassociation of the test scheme. -/
def LevelBaseChangeComposition : Prop :=
  ∀ (S S' S'' : Scheme.{u}) (b : S' ⟶ S) (c : S'' ⟶ S') (T : Over S'')
    (n : ℕ) (x : Tate.Level (Gm S'').toGrp T n),
    levelBaseChange (c ≫ b) T n x =
      Tate.levelRestrict (Gm S).toGrp ((Over.mapComp c b).hom.app T) n
        (levelBaseChange b ((Over.map c).obj T) n (levelBaseChange c T n x))

/-- Identity coherence on the selected integral inverse limits. -/
def IntegralBaseChangeIdentity : Prop :=
  ∀ (S : Scheme.{u}) (T : Over S) (P : ℕ → Prop) (x : Tate.Integral (Gm S).toGrp T P),
    integralBaseChange (𝟙 S) T P x =
      Tate.testRestrict (Gm S).toGrp P ((Over.mapId S).hom.app T) x

/-- Composition coherence on the selected integral inverse limits. -/
def IntegralBaseChangeComposition : Prop :=
  ∀ (S S' S'' : Scheme.{u}) (b : S' ⟶ S) (c : S'' ⟶ S') (T : Over S'')
    (P : ℕ → Prop) (x : Tate.Integral (Gm S'').toGrp T P),
    integralBaseChange (c ≫ b) T P x =
      Tate.testRestrict (Gm S).toGrp P ((Over.mapComp c b).hom.app T)
        (integralBaseChange b ((Over.map c).obj T) P (integralBaseChange c T P x))

/-- Identity coherence on the actual prime-adic integral modules. -/
def PrimeIntegralBaseChangeIdentity : Prop :=
  ∀ (S : Scheme.{u}) (T : Over S) (p : ℕ) [Fact p.Prime]
    (x : Tate.PrimeAdic.Integral (Gm S).toGrp T p),
    primeIntegralBaseChange (𝟙 S) T p x =
      Tate.PrimeAdic.testRestrict (Gm S).toGrp p ((Over.mapId S).hom.app T) x

/-- Composition coherence on the actual prime-adic integral modules. -/
def PrimeIntegralBaseChangeComposition : Prop :=
  ∀ (S S' S'' : Scheme.{u}) (b : S' ⟶ S) (c : S'' ⟶ S') (T : Over S'')
    (p : ℕ) [Fact p.Prime] (x : Tate.PrimeAdic.Integral (Gm S'').toGrp T p),
    primeIntegralBaseChange (c ≫ b) T p x =
      Tate.PrimeAdic.testRestrict (Gm S).toGrp p ((Over.mapComp c b).hom.app T)
        (primeIntegralBaseChange b ((Over.map c).obj T) p (primeIntegralBaseChange c T p x))

/-- Identity coherence after rationalization over the integers. -/
def RationalBaseChangeIdentity : Prop :=
  ∀ (S : Scheme.{u}) (T : Over S) (P : ℕ → Prop) (x : Tate.Rational (Gm S).toGrp T P),
    rationalBaseChange (𝟙 S) T P x =
      Tate.rationalTestRestrict (Gm S).toGrp P ((Over.mapId S).hom.app T) x

/-- Composition coherence after rationalization over the integers. -/
def RationalBaseChangeComposition : Prop :=
  ∀ (S S' S'' : Scheme.{u}) (b : S' ⟶ S) (c : S'' ⟶ S') (T : Over S'')
    (P : ℕ → Prop) (x : Tate.Rational (Gm S'').toGrp T P),
    rationalBaseChange (c ≫ b) T P x =
      Tate.rationalTestRestrict (Gm S).toGrp P ((Over.mapComp c b).hom.app T)
        (rationalBaseChange b ((Over.map c).obj T) P (rationalBaseChange c T P x))

/-- Identity coherence after extension from the p-adic integers to their field. -/
def PrimeRationalBaseChangeIdentity : Prop :=
  ∀ (S : Scheme.{u}) (T : Over S) (p : ℕ) [Fact p.Prime]
    (x : Tate.PrimeAdic.Rational (Gm S).toGrp T p),
    primeRationalBaseChange (𝟙 S) T p x =
      Tate.PrimeAdic.rationalTestRestrict (Gm S).toGrp p ((Over.mapId S).hom.app T) x

/-- Composition coherence after extension from the p-adic integers to their field. -/
def PrimeRationalBaseChangeComposition : Prop :=
  ∀ (S S' S'' : Scheme.{u}) (b : S' ⟶ S) (c : S'' ⟶ S') (T : Over S'')
    (p : ℕ) [Fact p.Prime] (x : Tate.PrimeAdic.Rational (Gm S'').toGrp T p),
    primeRationalBaseChange (c ≫ b) T p x =
      Tate.PrimeAdic.rationalTestRestrict (Gm S).toGrp p ((Over.mapComp c b).hom.app T)
        (primeRationalBaseChange b ((Over.map c).obj T) p (primeRationalBaseChange c T p x))

/-- The five canonical multiplicative Tate comparisons satisfy identity and composition laws. -/
def MultiplicativeBaseChangeCoherence : Prop :=
  LevelBaseChangeIdentity.{u} ∧ LevelBaseChangeComposition.{u} ∧
  IntegralBaseChangeIdentity.{u} ∧ IntegralBaseChangeComposition.{u} ∧
  PrimeIntegralBaseChangeIdentity.{u} ∧ PrimeIntegralBaseChangeComposition.{u} ∧
  RationalBaseChangeIdentity.{u} ∧ RationalBaseChangeComposition.{u} ∧
  PrimeRationalBaseChangeIdentity.{u} ∧ PrimeRationalBaseChangeComposition.{u}

end Langlands.GroupScheme.Gm.TateComparison
