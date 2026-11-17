import Langlands.GroupScheme.MatrixRepresentation.ComponentConstant
import Langlands.GroupScheme.MatrixRepresentation.StableComplements
import Langlands.Representation.FiniteRegularMatrix
import Langlands.GroupScheme.Reductive.PolynomialSemisimplicity

/-! # Actual regular representations of componentwise constant finite quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.ComponentConstant
open Langlands.FiniteQuotientAveraging

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k] [IsAlgClosed k]
  (G : GroupScheme (Spec (CommRingCat.of k)))
  [LocallyOfFiniteType G.X.hom]

local instance : IsLocallyNoetherian G.X.left :=
  LocallyOfFiniteType.isLocallyNoetherian G.X.hom

/-- The actual regular representation of a finite rational quotient whose values
are constant on actual components. -/
def finiteComponentQuotientRegular {Q : Type u} [Group Q] [Fintype Q]
    (q : rationalPoints G →* Q)
    (hq : ∀ x y, sectionComponent G.X x = sectionComponent G.X y → q x = q y) :
    MatrixRepresentation G (Fin (Fintype.card Q)) :=
  ofComponentConstantRationalMatrix G ((regularMatrixHom k Q).comp q)
    (fun x y h => congrArg (regularMatrixHom k Q) (hq x y h))

/-- The constructed representation retains actual component constancy. -/
theorem finiteComponentQuotientRegular_isComponentConstant
    {Q : Type u} [Group Q] [Fintype Q]
    (q : rationalPoints G →* Q)
    (hq : ∀ x y, sectionComponent G.X x = sectionComponent G.X y → q x = q y) :
    IsComponentConstant G.X (finiteComponentQuotientRegular G q hq).hom.hom :=
  ofComponentConstantRationalMatrix_isComponentConstant G _ _

/-- On rational points, the actual representation is the finite-coordinate
regular representation pulled back along the quotient. -/
theorem finiteComponentQuotientRegular_rationalRepresentation
    {Q : Type u} [Group Q] [Fintype Q]
    (q : rationalPoints G →* Q)
    (hq : ∀ x y, sectionComponent G.X x = sectionComponent G.X y → q x = q y) :
    (finiteComponentQuotientRegular G q hq).rationalRepresentation =
      (coordinateRegular k Q).comp q := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  have hg := rationalMatrix_ofComponentConstantRationalMatrix G
    ((regularMatrixHom k Q).comp q)
    (fun x y h => congrArg (regularMatrixHom k Q) (hq x y h)) g
  have hv := congrArg
    (fun M : GL (Fin (Fintype.card Q)) k =>
      (M : Matrix (Fin (Fintype.card Q)) (Fin (Fintype.card Q)) k) *ᵥ v) hg
  exact hv.trans (regularMatrixHom_mulVec k Q (q g) v)

section Semisimplicity

variable [IsAffineHom G.X.hom]

/-- Semisimplicity of an affine componentwise constant actual representation
implies semisimplicity of its rational-point representation. -/
theorem rationalRepresentation_isSemisimple_of_componentConstant
    {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation G n) (hc : IsComponentConstant G.X ρ.hom.hom)
    (hss : ρ.IsSemisimple) :
    ρ.rationalRepresentation.IsSemisimpleRepresentation := by
  refine ⟨fun U => ?_⟩
  have hU : ρ.IsStableSubspace U.toSubmodule :=
    isStableSubspace_of_componentConstant G ρ hc U.toSubmodule
      (fun g _ hv => U.apply_mem_toSubmodule g hv)
  obtain ⟨W, hW, hUW⟩ :=
    (isSemisimple_iff_exists_stable_complement ρ).mp hss U.toSubmodule hU
  refine ⟨hW.rationalSubrepresentation, ?_⟩
  constructor
  · apply disjoint_iff.mpr
    apply Subrepresentation.toSubmodule_injective
    exact hUW.inf_eq_bot
  · apply codisjoint_iff.mpr
    apply Subrepresentation.toSubmodule_injective
    exact hUW.sup_eq_top

/-- Linear reductivity obstructs a componentwise constant finite rational quotient
whose order is divisible by the characteristic. -/
theorem not_dvd_card_of_linearlyReductive_finiteComponentQuotient
    {Q : Type u} [Group Q] [Fintype Q]
    (q : rationalPoints G →* Q) (hsurj : Function.Surjective q)
    (hq : ∀ x y, sectionComponent G.X x = sectionComponent G.X y → q x = q y)
    (p : ℕ) [CharP k p]
    (hLR : ∀ n (ρ : MatrixRepresentation G (Fin n)), ρ.IsSemisimple) :
    ¬ p ∣ Nat.card Q := by
  have hss : (finiteComponentQuotientRegular G q hq).rationalRepresentation.IsSemisimpleRepresentation :=
    rationalRepresentation_isSemisimple_of_componentConstant G
      (finiteComponentQuotientRegular G q hq)
      (finiteComponentQuotientRegular_isComponentConstant G q hq)
      (hLR _ _)
  rw [finiteComponentQuotientRegular_rationalRepresentation G q hq] at hss
  have hreg := PolynomialSemisimplicity.isSemisimpleRepresentation_of_comp
    (coordinateRegular k Q) q hsurj hss
  exact (coordinateRegular_isSemisimple_iff_not_dvd k Q p).mp hreg

end Semisimplicity

end Langlands.GroupScheme.MatrixRepresentation
