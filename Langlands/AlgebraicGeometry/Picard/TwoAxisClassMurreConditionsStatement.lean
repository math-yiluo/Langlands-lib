import Langlands.AlgebraicGeometry.Picard.TwoAxisRigidifiedClassPresheaf
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCriterionStatement

/-! # Murre's conditions for the two-axis class presheaf over noetherian affine bases -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- For every abelian scheme `A` over the spectrum of a noetherian ring, the two-axis class presheaf
of `A` satisfies Murre's condition `SmallValues`: every value is `u`-small. This defines the
proposition; it does not prove it. -/
def NoetherianTwoAxisClassSmallValuesStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (A : Langlands.AbelianScheme (Spec (CommRingCat.of R))),
    UnramifiedFunctor.SmallValues (TwoAxisRigidifiedLineBundle.classPresheaf A)

/-- For every abelian scheme `A` over the spectrum of a noetherian ring, the two-axis class presheaf
of `A` satisfies Murre's condition `ZariskiSheaf`: (F1a), sheaf for Zariski open covers. This
defines the proposition; it does not prove it. -/
def NoetherianTwoAxisClassZariskiSheafStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (A : Langlands.AbelianScheme (Spec (CommRingCat.of R))),
    UnramifiedFunctor.ZariskiSheaf (TwoAxisRigidifiedLineBundle.classPresheaf A)

/-- For every abelian scheme `A` over the spectrum of a noetherian ring, the two-axis class presheaf
of `A` satisfies Murre's condition `FaithfullyFlatSheaf`: (F1b), sheaf for faithfully flat
quasi-compact morphisms. This defines the proposition; it does not prove it. -/
def NoetherianTwoAxisClassFaithfullyFlatSheafStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (A : Langlands.AbelianScheme (Spec (CommRingCat.of R))),
    UnramifiedFunctor.FaithfullyFlatSheaf (TwoAxisRigidifiedLineBundle.classPresheaf A)

/-- For every abelian scheme `A` over the spectrum of a noetherian ring, the two-axis class presheaf
of `A` satisfies Murre's condition `FilteredColimits`: (F2), filtered colimits of algebras over
affine opens. This defines the proposition; it does not prove it. -/
def NoetherianTwoAxisClassFilteredColimitsStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (A : Langlands.AbelianScheme (Spec (CommRingCat.of R))),
    UnramifiedFunctor.FilteredColimits (TwoAxisRigidifiedLineBundle.classPresheaf A)

/-- For every abelian scheme `A` over the spectrum of a noetherian ring, the two-axis class presheaf
of `A` satisfies Murre's condition `AdicLimits`: (F3), adic limits over complete local noetherian
rings. This defines the proposition; it does not prove it. -/
def NoetherianTwoAxisClassAdicLimitsStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (A : Langlands.AbelianScheme (Spec (CommRingCat.of R))),
    UnramifiedFunctor.AdicLimits (TwoAxisRigidifiedLineBundle.classPresheaf A)

/-- For every abelian scheme `A` over the spectrum of a noetherian ring, the two-axis class presheaf
of `A` satisfies Murre's condition `ArtinianLifting`: (F4′), lifting over local artinian rings. This
defines the proposition; it does not prove it. -/
def NoetherianTwoAxisClassArtinianLiftingStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (A : Langlands.AbelianScheme (Spec (CommRingCat.of R))),
    UnramifiedFunctor.ArtinianLifting (TwoAxisRigidifiedLineBundle.classPresheaf A)

/-- For every abelian scheme `A` over the spectrum of a noetherian ring, the two-axis class presheaf
of `A` satisfies Murre's condition `NilpotentInjective`: strong (F5) for local artinian rings,
injectivity along nilpotent thickenings. This defines the proposition; it does not prove it. -/
def NoetherianTwoAxisClassNilpotentInjectiveStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (A : Langlands.AbelianScheme (Spec (CommRingCat.of R))),
    UnramifiedFunctor.NilpotentInjective (TwoAxisRigidifiedLineBundle.classPresheaf A)

/-- For every abelian scheme `A` over the spectrum of a noetherian ring, the two-axis class presheaf
of `A` satisfies Murre's condition `ValuativeSeparation`: (F6), separation over discrete valuation
rings. This defines the proposition; it does not prove it. -/
def NoetherianTwoAxisClassValuativeSeparationStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (A : Langlands.AbelianScheme (Spec (CommRingCat.of R))),
    UnramifiedFunctor.ValuativeSeparation (TwoAxisRigidifiedLineBundle.classPresheaf A)

/-- For every abelian scheme `A` over the spectrum of a noetherian ring, the two-axis class presheaf
of `A` satisfies Murre's condition `OneDimensionalLifting`: (F7), lifting over one-dimensional
complete local rings. This defines the proposition; it does not prove it. -/
def NoetherianTwoAxisClassOneDimensionalLiftingStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (A : Langlands.AbelianScheme (Spec (CommRingCat.of R))),
    UnramifiedFunctor.OneDimensionalLifting (TwoAxisRigidifiedLineBundle.classPresheaf A)

/-- For every abelian scheme `A` over the spectrum of a noetherian ring, the two-axis class presheaf
of `A` satisfies Murre's condition `GenericNonLifting`: (F8), spreading out of generic non-lifting.
This defines the proposition; it does not prove it. -/
def NoetherianTwoAxisClassGenericNonLiftingStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (A : Langlands.AbelianScheme (Spec (CommRingCat.of R))),
    UnramifiedFunctor.GenericNonLifting (TwoAxisRigidifiedLineBundle.classPresheaf A)

/-- All of Murre's conditions used in `UnramifiedFunctor.MurreCriterionStatement` hold for the two-
axis class presheaf of every abelian scheme over the spectrum of a noetherian ring. This defines the
proposition; it does not prove it. -/
def NoetherianTwoAxisClassMurreConditionsStatement : Prop :=
  NoetherianTwoAxisClassSmallValuesStatement.{u} ∧
    NoetherianTwoAxisClassZariskiSheafStatement.{u} ∧
    NoetherianTwoAxisClassFaithfullyFlatSheafStatement.{u} ∧
    NoetherianTwoAxisClassFilteredColimitsStatement.{u} ∧
    NoetherianTwoAxisClassAdicLimitsStatement.{u} ∧
    NoetherianTwoAxisClassArtinianLiftingStatement.{u} ∧
    NoetherianTwoAxisClassNilpotentInjectiveStatement.{u} ∧
    NoetherianTwoAxisClassValuativeSeparationStatement.{u} ∧
    NoetherianTwoAxisClassOneDimensionalLiftingStatement.{u} ∧
    NoetherianTwoAxisClassGenericNonLiftingStatement.{u}

end Langlands.AlgebraicGeometry.Picard
