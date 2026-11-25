import Langlands.Geometry.FormalGroup.DeligneCompletedReduction
import Langlands.Galois.Local.SeparableUnramifiedCompletionMaps
import Langlands.Galois.Local.SeparableUnramifiedIntegerLift

/-! # The completed-base and residue presentations of Deligne points -/

noncomputable section

universe u

namespace Langlands.DeligneFormalSpace

open CategoryTheory ValuativeRel IsLocalRing CentralDivision CentralSimple
open _root_.Langlands.FormalGroup
open Langlands.LocalGalois.Separable Langlands.LocalGalois.Separable.UnramifiedCompletion

attribute [local instance] ModuleLaw.coefficientAlgebra ModuleLaw.coefficientScalarTower

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable {π : 𝒪[K]} (hπ : Irreducible π)
variable (B : Nilp.{u, u} 𝒪[K] π)

local instance completedIsoUnramifiedAlgebra : Algebra 𝒪[K] (fixedFieldIntegers K) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation K) (vA := fixedFieldValuation K)

include hπ in
/-- A residue map of a nilpotent test algebra has a unique completed lift. -/
theorem completedCoefficientReduction_bijective :
    Function.Bijective (completedCoefficientReduction hπ (B := B)) := by
  let S := fixedFieldIntegers K
  let R := 𝒪[K]
  let I := Nilp.reductionIdeal π B.obj
  let e := residueAlgEquiv K
  let residueS : S →ₐ[R] ResidueField S := Ideal.Quotient.mkₐ R (maximalIdeal S)
  let p := e.toAlgHom.comp residueS
  let precomp := fun f : Residue K →ₐ[R] Nilp.Reduction π B.obj => f.comp p
  have hp : Function.Surjective p := e.surjective.comp (residue_surjective (R := S))
  have hi : Function.Injective precomp := by
    intro f g hfg
    ext y
    obtain ⟨x, rfl⟩ := hp y
    exact AlgHom.congr_fun hfg x
  have hMaps := (integerMapEquiv K hπ B.nilpotent).bijective
  have hLift := fixedFieldIntegerLift_bijective K I B.reductionIdeal_isNilpotent
  have hComposition : (precomp ∘ completedCoefficientReduction hπ (B := B)) =
      (Ideal.Quotient.mkₐ R I).comp ∘ integerMapEquiv K hπ B.nilpotent := by
    funext f
    ext x
    change completedCoefficientReduction hπ f (e (residue S x)) =
      (Nilp.quotientO R B) (f (integerToCompletion K x))
    rw [residueAlgEquiv_residue, completedCoefficientReduction_residue]
  exact Function.Bijective.of_comp_left (hComposition.symm ▸ hLift.comp hMaps) hi

/-- Reduce a completed coefficient map, with inverse the unique lift. -/
def completedCoefficientEquiv :
    (Integers K →ₐ[𝒪[K]] B.obj) ≃
      (Residue K →ₐ[𝒪[K]] ((Nilp.reductionFunctor 𝒪[K] π).obj B).obj) :=
  Equiv.ofBijective (completedCoefficientReduction hπ) (completedCoefficientReduction_bijective hπ B)

variable {d : ℕ} [NeZero d]

/-- Actual reduction is a natural isomorphism between the completed-base and
residue-coordinate presentations of Deligne points. -/
def nilpDeligneCompletedIso : nilpDeligneCompletedFunctor (d := d) hπ ≅
    nilpDeligneResidueFunctor (d := d) (Residue K) (coefficientUniformizer_ne_zero (F := K) hπ) :=
  NatIso.ofComponents
    (fun A => ((Equiv.refl _).prodCongr (completedCoefficientEquiv hπ A)).toIso)
    (fun f => (nilpDeligneCompletedReduction (d := d) hπ).naturality f)

@[simp]
theorem nilpDeligneCompletedIso_hom :
    (nilpDeligneCompletedIso (d := d) hπ).hom = nilpDeligneCompletedReduction hπ := rfl

variable {D : Type u} [DivisionRing D] [Algebra K D]
variable [FiniteDimensional K D] [Algebra.IsCentral K D]

local instance completedIsoReducedDegree : NeZero (reducedDegree K D) := ⟨(reducedDegree_pos K D).ne'⟩

omit [NeZero d] in
/-- The natural comparison identifies the two actual Deligne-side group actions. -/
theorem nilpDeligneCompletedIso_equivariant (g : GL (Fin (reducedDegree K D)) K × Dˣ) :
    (nilpDeligneCompletedDivisionAction hπ g).asIso.hom ≫ (nilpDeligneCompletedIso hπ).hom =
      (nilpDeligneCompletedIso hπ).hom ≫ (nilpDeligneDivisionAction (Residue K) hπ g).asIso.hom :=
  nilpDeligneCompletedReduction_equivariant hπ g

end Langlands.DeligneFormalSpace
