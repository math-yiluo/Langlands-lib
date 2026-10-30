import Langlands.Shimura.Coefficients.HarrisCongruenceLevels
import Langlands.Shimura.Coefficients.VaryingCoverInverse
import Langlands.Shimura.Coefficients.TrivializationProof
import Langlands.Geometry.EtaleDerivedSections

/-! # Harris lattice coefficients on genuine small-etale torsors -/

noncomputable section

universe u

namespace Langlands.Shimura.Coefficients

open CategoryTheory AlgebraicGeometry Opposite Langlands.Global

variable {A : Type u} [Ring A] [Algebra ℚ A] [Module.Finite ℚ A]
variable {L : Type u} [Field L] [NumberField L]
variable {W : Type u} [AddCommGroup W] [Module L W] [Module.Finite L W]
variable {σ : AlgebraInvolution ℚ A} (ρ : (σ.baseChange L).AlgebraicRepresentation W)
variable (p : FinitePlace ℚ) (U : CompactOpenLevel σ.FiniteAdelicPoints) (m : ℕ)
variable (X : Scheme.{u})
variable (Y : EquivariantDiagram (harrisCongruenceGroups ρ p U m) X.Etale)
variable (hY : ∀ n, IsFiniteGeometricTorsor X (Y.action n))

local notation "R" => HarrisCoefficientIntegers L p
local notation "M" => harrisCoefficientDiagram ρ p U m
local notation "J" => Scheme.smallEtaleTopology X

/-- The whole stable Harris lattice, reduced at every exponent and associated
to a genuine compatible diagram of finite geometric etale torsors. -/
def harrisEtaleCoefficientSystem :
    ℕᵒᵖ ⥤ Sheaf J (ModuleCat.{u} R) :=
  etaleAssociatedVaryingSystem X Y hY M

@[simp] theorem harrisEtaleCoefficientSystem_obj (n : ℕᵒᵖ) :
    (harrisEtaleCoefficientSystem ρ p U m X Y hY).obj n =
      (etaleAssociatedFunctor X (Y.action n)).obj ((M).action n) := rfl

/-- Its transition is the original coefficient reduction followed by the
inverse of the proved comparison between the two genuine torsors. -/
@[simp] theorem harrisEtaleCoefficientSystem_map {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (harrisEtaleCoefficientSystem ρ p U m X Y hY).map f =
      (etaleAssociatedReduction X Y f).app M ≫
        (etaleAssociatedComparisonIso X Y hY f).inv.app M := rfl

@[reassoc] theorem harrisEtaleCoefficientSystem_comparison
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (harrisEtaleCoefficientSystem ρ p U m X Y hY).map f ≫
        (etaleAssociatedComparison X Y f).app M =
      (etaleAssociatedReduction X Y f).app M :=
  etaleAssociatedTransition_comparison X Y hY f M

/-- On actual cover sections, the transition is determined by the original
full-lattice reduction and contravariant pullback along the cover map. -/
@[reassoc] theorem harrisEtaleCoefficientSystem_inclusion
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (harrisEtaleCoefficientSystem ρ p U m X Y hY).map f ≫
        etaleAssociatedInclusion X (Y.action j) ((M).action j) ≫
        coverPullback J (Y.obj.map f) ((constantSheaf J (ModuleCat.{u} R)).obj
          ((M).obj.obj j)) =
      etaleAssociatedInclusion X (Y.action i) ((M).action i) ≫
        (productSheaf J (Y.obj.obj i)).map
          ((constantSheaf J (ModuleCat.{u} R)).map ((M).obj.map f)) :=
  etaleAssociatedTransition_inclusion X Y hY f M

/-- Evaluation at the tautological lift trivializes each Harris coefficient
sheaf on its torsor, by the proved geometric graph-splitting construction. -/
def harrisEtaleCoefficientTrivialization (n : ℕᵒᵖ) :
    ((J).overPullback (ModuleCat.{u} R) (Y.obj.obj n)).obj
        ((harrisEtaleCoefficientSystem ρ p U m X Y hY).obj n) ≅
      ((J).overPullback (ModuleCat.{u} R) (Y.obj.obj n)).obj
        ((constantSheaf J (ModuleCat.{u} R)).obj ((M).obj.obj n)) :=
  (constantAssociatedTrivializationOfSplitting J (Y.action n)
    (etaleTorsorSectionSplitting X _ (Y.action n) (hY n) R)).app ((M).action n)

/-- The local trivialization uses the actual invariant-section evaluation map. -/
@[simp] theorem harrisEtaleCoefficientTrivialization_hom (n : ℕᵒᵖ) :
    (harrisEtaleCoefficientTrivialization ρ p U m X Y hY n).hom =
      associatedEvaluation J (Y.action n)
        (((constantSheaf J (ModuleCat.{u} R)).mapAction
          ((harrisCongruenceGroups ρ p U m).obj n)).obj ((M).action n)) := rfl

/-- The ordinary global-section inverse system of the constructed sheaves. -/
def harrisEtaleSectionsSystem : ℕᵒᵖ ⥤ ModuleCat.{u} R :=
  harrisEtaleCoefficientSystem ρ p U m X Y hY ⋙
    Langlands.Geometry.EtaleDerivedSections.sections X R

/-- Derived global sections form an actual inverse diagram in the homotopy
category; strict functoriality of chosen injective resolutions is not assumed. -/
def harrisEtaleDerivedSystem :
    ℕᵒᵖ ⥤ HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℕ) :=
  harrisEtaleCoefficientSystem ρ p U m X Y hY ⋙
    Langlands.Geometry.EtaleDerivedSections.homotopyFunctor X R

/-- Ordinary small-etale cohomology of all the Harris coefficient reductions. -/
def harrisEtaleCohomologySystem (q : ℕ) : ℕᵒᵖ ⥤ ModuleCat.{u} R :=
  harrisEtaleCoefficientSystem ρ p U m X Y hY ⋙
    Langlands.Geometry.EtaleDerivedSections.cohomology X R q

/-- A constructed injective-resolution representative at one exponent. -/
def harrisEtaleSectionsComplex (n : ℕᵒᵖ) :
    CochainComplex (ModuleCat.{u} R) ℕ :=
  Langlands.Geometry.EtaleDerivedSections.complex X R
    ((harrisEtaleCoefficientSystem ρ p U m X Y hY).obj n)

/-- The actual section complex represents the derived object at each exponent. -/
def harrisEtaleDerivedSystemIso (n : ℕᵒᵖ) :
    (harrisEtaleDerivedSystem ρ p U m X Y hY).obj n ≅
      (HomotopyCategory.quotient _ _).obj
        (harrisEtaleSectionsComplex ρ p U m X Y hY n) :=
  Langlands.Geometry.EtaleDerivedSections.complexIso X R
    ((harrisEtaleCoefficientSystem ρ p U m X Y hY).obj n)

/-- Its homology is the constructed ordinary small-etale cohomology. -/
def harrisEtaleCohomologyIso (q : ℕ) (n : ℕᵒᵖ) :
    (harrisEtaleCohomologySystem ρ p U m X Y hY q).obj n ≅
      (harrisEtaleSectionsComplex ρ p U m X Y hY n).homology q :=
  Langlands.Geometry.EtaleDerivedSections.cohomologyIso X R
    ((harrisEtaleCoefficientSystem ρ p U m X Y hY).obj n) q

/-- Cohomology transitions apply the derived functor to the genuine reduction
and inverse torsor comparison, in that order. -/
theorem harrisEtaleCohomologySystem_map (q : ℕ)
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (harrisEtaleCohomologySystem ρ p U m X Y hY q).map f =
      (Langlands.Geometry.EtaleDerivedSections.cohomology X R q).map
          ((etaleAssociatedReduction X Y f).app M) ≫
        (Langlands.Geometry.EtaleDerivedSections.cohomology X R q).map
          ((etaleAssociatedComparisonIso X Y hY f).inv.app M) :=
  (Langlands.Geometry.EtaleDerivedSections.cohomology X R q).map_comp _ _

/-- Zeroth cohomology recovers global sections naturally across every exponent. -/
def harrisEtaleCohomologyZeroIso :
    harrisEtaleCohomologySystem ρ p U m X Y hY 0 ≅
      harrisEtaleSectionsSystem ρ p U m X Y hY :=
  Functor.isoWhiskerLeft (harrisEtaleCoefficientSystem ρ p U m X Y hY)
    (Langlands.Geometry.EtaleDerivedSections.cohomologyZeroIso X R)

end Langlands.Shimura.Coefficients
