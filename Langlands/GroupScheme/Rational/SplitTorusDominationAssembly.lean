import Langlands.GroupScheme.Rational.CommutativeUnipotentCharZeroSplit

/-! # All-characteristic assembly from the prime-exponent domination case -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The elementary case still needed after the characteristic-zero,
prime-power and derived-subgroup reductions. -/
def PrimeExponentSplitTorusDominationCase : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [IsCommMonObj G.X],
    IsUnipotent G → HasUniformPowerExponent G p →
      HasPointedSplitTorusDomination G → RelativeRoot.IsSplitUnipotent G

/-- The exact all-characteristic target follows from its commutative
prime-exponent case, over every original ground field. -/
theorem unipotentSplitTorusDomination_of_primeExponent
    (helem : PrimeExponentSplitTorusDominationCase.{u}) :
    UnipotentSplitTorusDominationStatement.{u} := by
  intro k _ G hSmooth hAffine hConnected hU hdom
  let : Smooth G.X.hom := hSmooth
  let : IsAffineHom G.X.hom := hAffine
  let : ConnectedSpace G.X.left := hConnected
  apply splitUnipotent_of_splitTorusDomination_of_commutative ?_ G hU hdom
  intro H _ _ _ _ hHu hHd
  rcases CharP.exists' k with hzero | ⟨p, hprime, hchar⟩
  · let : CharZero k := hzero
    exact RelativeRoot.IsUnipotent.isSplitUnipotent_of_commutative_charZero H hHu
  · let : Fact p.Prime := hprime
    let : CharP k p := hchar
    exact commutative_splitUnipotent_of_splitTorusDomination_of_primeExponent
      p (helem k p) H hHu hHd

/-- Choose the actual represented additive series supplied by the assembly,
retaining the elementary case as an explicit input. -/
def splitSeriesOfPrimeExponentDomination
    (helem : PrimeExponentSplitTorusDominationCase.{u})
    {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (hU : IsUnipotent G) (hdom : HasPointedSplitTorusDomination G) :
    {n : ℕ // RelativeRoot.HasSplitSeries n G} :=
  let h := unipotentSplitTorusDomination_of_primeExponent helem k G
    inferInstance inferInstance inferInstance hU hdom
  ⟨h.choose, h.choose_spec⟩

end Langlands.GroupScheme
