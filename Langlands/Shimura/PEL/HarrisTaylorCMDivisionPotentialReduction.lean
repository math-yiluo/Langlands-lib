import Langlands.AbelianScheme.AbelianReductionStatement
import Langlands.AbelianScheme.NeronTorusRank
import Langlands.Shimura.PEL.HarrisTaylorCMDivisionTorus

/-! # Potential good reduction in the Harris division case -/

noncomputable section

open CategoryTheory AlgebraicGeometry Langlands.AbelianScheme Langlands.GroupScheme
open scoped TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme

universe u

/-- Good reduction of the actual abelian variety after a finite extension of
fraction fields and compatible local extension of discrete valuation rings. -/
def HasPotentialGoodReduction {V K : Type u} [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
    (B : AbelianScheme (Spec (CommRingCat.of K))) : Prop :=
  ∃ (E : FiniteDvrExtension V K) (G : AbelianScheme (Spec (CommRingCat.of E.ring))),
    Nonempty (((baseChange (Spec.algebraMap K E.fractionField)).obj B) ≅
      (baseChange (NeronModelInfra.specGenericFibreInclusion E.ring E.fractionField)).obj G)

end Langlands.AbelianScheme

namespace Langlands.Shimura.HarrisTaylor

open NumberField _root_.Algebra

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [Algebra ℚ A] [IsScalarTower ℚ F A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)

/-- Potential semistable reduction and the abelian reduction criterion give
potential good reduction for a normalized Harris division action. -/
theorem divisionPotentialGoodReduction
    (hsemi : PotentialSemistableReductionStatement.{0})
    (habelian : AbelianReductionStatement.{0}) (hD : D.IsDivision)
    {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K]
    (B : AbelianScheme (Spec (CommRingCat.of K))) (a : A →ₐ[ℚ] End0 B)
    (hB : B.HasRelativeDimension (Module.finrank ℚ E * n ^ 2)) :
    HasPotentialGoodReduction (V := V) B := by
  obtain ⟨L, N, J, i, hi, ⟨P⟩⟩ := hsemi V K B
  let b := Spec.algebraMap K L.fractionField
  let B' := (AbelianScheme.baseChange b).obj B
  have hB' : B'.HasRelativeDimension (Module.finrank ℚ E * n ^ 2) :=
    hasRelativeDimension_baseChange B _ hB b
  let M := ℚ ⊗[ℤ] cocharacterLattice N.geometricSpecialFibre
  let : Module.Finite ℚ M := P.finite_rationalCocharacters i hi
  have hdim : Module.finrank ℚ M = P.torusRank := P.finrank_rationalCocharacters i hi
  have hbound : Module.finrank ℚ M ≤ Module.finrank ℚ E * n ^ 2 := by
    rw [hdim]
    exact N.torusRank_le hB' i hi P
  let : Subsingleton M := subsingleton_neronFibreCocharacters D hD N.group N.property
    N.genericIso ((rationalBaseChangeEnd b B).comp a) (geometricSpecialPoint L.ring) hbound
  have hrank : P.torusRank = 0 := hdim.symm.trans (Module.finrank_zero_of_subsingleton (R := ℚ) (M := M))
  have hJ : IsProper J.X.hom := P.isProper_of_torusRank_eq_zero hrank
  obtain ⟨hproper, hconn⟩ := habelian L.ring L.fractionField B' N J i hi hJ
  exact ⟨L, N.toAbelianScheme hproper hconn, ⟨N.toAbelianSchemeGenericIso hproper hconn⟩⟩

end Langlands.Shimura.HarrisTaylor
