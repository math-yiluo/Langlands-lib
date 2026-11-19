import Langlands.Geometry.FormalGroup.DeligneResidueAction

/-! # The residue-coordinate comparison of the framed and Deligne point functors -/

noncomputable section
universe u

namespace Langlands.FormalGroup.LocalDivision

open CategoryTheory ValuativeRel CentralDivision DeligneFormalSpace
open scoped WithZero

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
variable [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
variable [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type u} [Field L] [Algebra K L] (ι : L →ₐ[K] D)

/-- The division uniformizer and arithmetic Frobenius relations of the cyclic
presentation used in Drinfeld's basic theorem. The embedded subfield and its
integer ring are the ones used for the special tangent condition. -/
def HasDrinfeldCyclicRelations (π : 𝒪[K]) : Prop :=
  ∃ (uniformizer : Dˣ) (frobenius : L ≃ₐ[K] L),
    (uniformizer : D) ^ CentralSimple.reducedDegree K D = algebraMap K D (π : K) ∧
    (∀ a : L, (uniformizer : D) * ι a = ι (frobenius a) * (uniformizer : D)) ∧
    ∀ a : SubfieldIntegerRing K D ι,
      localReducedNormIntValuation K D (ι (frobenius (a : L)) - ι ((a : L) ^ Nat.card 𝓀[K])) < 1

variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ]

/-- The underlying comparison in residue coordinates preserves the actual residue
map of every height-zero framed class. Both functors are the Library constructions
on affine Nilp algebras. -/
def DrinfeldDeligneResidueComparisonStatement {π : 𝒪[K]}
    (Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι) (R := κ) π)
    [Algebra 𝓀[K] κ] [IsScalarTower 𝒪[K] 𝓀[K] κ] [IsAlgClosure 𝓀[K] κ] : Prop :=
  letI : NeZero (CentralSimple.reducedDegree K D) := ⟨(CentralSimple.reducedDegree_pos K D).ne'⟩
  HasDrinfeldCyclicRelations ι π →
    ∃ e : DrinfeldFramedAtlas.comparisonClassFunctor (R := 𝒪[K]) Φ ≅
      nilpDeligneResidueFunctor (d := CentralSimple.reducedDegree K D) κ
        (coefficientUniformizer_ne_zero (F := K) Φ.property.1),
      ∀ (B : Nilp.{u, u} 𝒪[K] π) (x : DrinfeldFramedAtlas.ComparisonClass Φ B),
        (e.hom.app B x).2 = x.residueMap

end Langlands.FormalGroup.LocalDivision
