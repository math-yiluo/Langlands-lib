import Langlands.Global.AdelicSquareIntegrableHeightExpansion
import Langlands.Global.AdelicTruncatedEisensteinPairing
import Langlands.Global.AdelicWeakConstantTermEigenReduction

/-! # Uniqueness of the twisted square-integrable part of a Levi pairing -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme AdelicGroupPoints Automorphic.GroupSchemeFunctions

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

attribute [local instance] isClosedImmersion_p

variable {K : Subgroup (AdelicGroupPoints F G)} {N d : ℕ}
  (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)
  {Q : StandardIndex F G fam.i fam.ν} (hK : IsIwasawaCompact (fam.p Q) K)

local notation "Forms" => (AdelicGroupPoints F G → ℂ)
local notation "Param" => ComplexCharacterParameter F (fam.P Q)
local notation "A2" =>
  IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc (fam.p Q) (fam.iU Q) (fam.l Q)
local notation "Orth" => fam.IsSquareIntegrableOrthogonal K hK.isCompact rho hsmooth hcalc Q

/-- The two finite sums of twists agree when all inducing forms lie in `A²_Q`
and subtracting either sum from the same function gives an orthogonal remainder.
The indexing sets may have different types, and the twists may repeat. -/
def SquareIntegrableTwistPartUniquenessStatement {Label₁ Label₂ : Type*}
    (s₁ : Finset Label₁) (s₂ : Finset Label₂) (param₁ : Label₁ → Param) (param₂ : Label₂ → Param)
    (v₁ : Label₁ → Forms) (v₂ : Label₂ → Forms) (f : Forms) : Prop :=
  (∀ i ∈ s₁, A2 (v₁ i)) → (∀ i ∈ s₂, A2 (v₂ i)) →
  Orth (f - ∑ i ∈ s₁, hK.parameterTwist (v₁ i) (param₁ i)) →
  Orth (f - ∑ i ∈ s₂, hK.parameterTwist (v₂ i) (param₂ i)) →
  (∑ i ∈ s₁, hK.parameterTwist (v₁ i) (param₁ i)) = ∑ i ∈ s₂, hK.parameterTwist (v₂ i) (param₂ i)

/-- The difference of the sums is a finite height expansion and is orthogonal,
since it equals the difference of the two orthogonal remainders. -/
theorem squareIntegrableTwistPart_eq {Label₁ Label₂ : Type*}
    (s₁ : Finset Label₁) (s₂ : Finset Label₂) (param₁ : Label₁ → Param) (param₂ : Label₂ → Param)
    (v₁ : Label₁ → Forms) (v₂ : Label₂ → Forms) (f : Forms) :
    fam.SquareIntegrableTwistPartUniquenessStatement rho hsmooth hcalc hK s₁ s₂ param₁ param₂ v₁ v₂ f := by
  classical
  intro hv₁ hv₂ hr₁ hr₂
  let a₁ : Forms := ∑ i ∈ s₁, hK.parameterTwist (v₁ i) (param₁ i)
  let a₂ : Forms := ∑ i ∈ s₂, hK.parameterTwist (v₂ i) (param₂ i)
  change a₁ = a₂
  have hOrth : Orth (a₁ - a₂) := by
    rw [show a₁ - a₂ = (f - a₂) - (f - a₁) by abel]
    exact (fam.squareIntegrableOrthogonalSubmodule Q hK.isCompact rho hsmooth hcalc).sub_mem hr₂ hr₁
  have hExpansion : fam.HasSquareIntegrableHeightExpansion rho hsmooth hcalc Q hK (a₁ - a₂) := by
    let e := Fintype.equivFin (s₁ ⊕ s₂)
    let form : s₁ ⊕ s₂ → Forms := Sum.elim (fun i => v₁ i.val) (fun i => v₂ i.val)
    let coeff (i : s₁ ⊕ s₂) (x : RealCharacterDual F (fam.P Q)) : ℂ :=
      Sum.elim (fun j : s₁ => Complex.exp (complexParameterPairing F (fam.P Q) (param₁ j.val) x))
        (fun j : s₂ => -Complex.exp (complexParameterPairing F (fam.P Q) (param₂ j.val) x)) i
    refine ⟨Fintype.card (s₁ ⊕ s₂), form ∘ e.symm, coeff ∘ e.symm, ?_, ?_⟩
    · intro i
      change A2 (form (e.symm i))
      cases e.symm i with
      | inl j => exact hv₁ j.val j.property
      | inr j => exact hv₂ j.val j.property
    · intro g
      rw [← Fintype.sum_equiv e (fun i => coeff i (hK.height g) * form i g) _
        (fun i => by simp only [Function.comp_apply, e.symm_apply_apply]),
        Fintype.sum_sum_type]
      simp only [a₁, a₂, Pi.sub_apply, Finset.sum_apply, coeff, form, Sum.elim_inl,
        Sum.elim_inr, neg_mul, Finset.sum_neg_distrib,
        IsIwasawaCompact.parameterTwist, IsIwasawaCompact.heightPower, sub_eq_add_neg]
      rw [← Finset.sum_coe_sort s₁, ← Finset.sum_coe_sort s₂]
      simp only [mul_comm]
  exact sub_eq_zero.mp
    (fam.eq_zero_of_squareIntegrableHeightExpansion_of_orthogonal rho hsmooth hcalc Q hK hExpansion hOrth)

/-- In the extended pairing, the twist sum of a parameter-indexed decomposition
agrees with the sum in any finite labelled presentation with orthogonal remainder. -/
theorem IsSquareIntegrableTwistDecomposition.twistSum_eq
    {f : Forms} {s : Finset Param} {v : Param → Forms}
    (h : fam.IsSquareIntegrableTwistDecomposition rho hsmooth hcalc hK f s v)
    {Label : Type*} (t : Finset Label) (lam : Label → Param) (u : Label → Forms)
    (hu : ∀ i ∈ t, A2 (u i))
    (hr : Orth (f - ∑ i ∈ t, hK.parameterTwist (u i) (lam i))) :
    (∑ p ∈ s, hK.parameterTwist (v p) p) = ∑ i ∈ t, hK.parameterTwist (u i) (lam i) :=
  fam.squareIntegrableTwistPart_eq rho hsmooth hcalc hK s t id lam v u f h.1 hu h.2 hr

end Langlands.Global.StandardParabolicFamily
