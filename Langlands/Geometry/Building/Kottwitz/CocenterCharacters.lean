import Langlands.Geometry.Building.Kottwitz.ReductiveMap
import Langlands.GroupScheme.HomDescent
import Langlands.GroupScheme.Derived.KernelAnnihilation
import Langlands.Geometry.Building.KPZeroNormKernel

/-! # Characters and valuation kernels of an actual cocenter -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.Kottwitz

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (hG : IsConnectedReductive G) (c : Cocenter k G)

include hG in
/-- Every rational character of a reductive group descends to its actual cocenter. -/
theorem Cocenter.characterRestrict_surjective :
    Function.Surjective (characterRestrict c.quotient) := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffineHom c.torus.X.hom :=
    c.isTorus.isConnectedReductive_of_fieldSplitting.isAffineHom
  let : IsAffineHom (c.quotient.hom.hom.left ≫ c.torus.X.hom) := by
    rw [Over.w c.quotient.hom.hom]
    infer_instance
  let : IsAffineHom c.quotient.hom.hom.left :=
    IsAffineHom.of_comp c.quotient.hom.hom.left c.torus.X.hom
  let : Flat c.quotient.hom.hom.left := c.isQuotient.1
  let : Surjective c.quotient.hom.hom.left := c.isQuotient.2.1
  have hk : IsDerivedSubgroup (kernelι c.quotient) :=
    ⟨by
      change IsClosedImmersion (kernelι c.quotient).hom.hom.left
      infer_instance, c.isQuotient.2.2.2⟩
  intro χ
  have hχ : kernelι c.quotient ≫ χ.toMul = 0 := by
    exact congrArg Additive.toMul (hk.characterRestrict_eq_zero χ)
  refine ⟨Additive.ofMul (FpqcHomDescent.hom c.quotient χ.toMul hχ), ?_⟩
  exact congrArg Additive.ofMul (FpqcHomDescent.fac c.quotient χ.toMul hχ)

include hG in
/-- Restriction of characters from the actual cocenter is injective. -/
theorem Cocenter.characterRestrict_injective :
    Function.Injective (characterRestrict c.quotient) := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffineHom c.torus.X.hom :=
    c.isTorus.isConnectedReductive_of_fieldSplitting.isAffineHom
  let : IsAffineHom (c.quotient.hom.hom.left ≫ c.torus.X.hom) := by
    rw [Over.w c.quotient.hom.hom]
    infer_instance
  let : IsAffineHom c.quotient.hom.hom.left :=
    IsAffineHom.of_comp c.quotient.hom.hom.left c.torus.X.hom
  let : Flat c.quotient.hom.hom.left := c.isQuotient.1
  let : Surjective c.quotient.hom.hom.left := c.isQuotient.2.1
  intro χ ψ h
  apply Additive.toMul.injective
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply (cancel_epi c.quotient.hom.hom.left).mp
  exact congrArg (fun a => a.toMul.hom.hom.left) h

/-- Rational characters of `G/G_der` identify with the rational characters of `G`
by pullback along the actual quotient. -/
def Cocenter.characterEquiv :
    rationalCharacters c.torus.toGrp ≃+ rationalCharacters G :=
  AddEquiv.ofBijective (characterRestrict c.quotient)
    ⟨c.characterRestrict_injective hG, c.characterRestrict_surjective hG⟩

@[simp] theorem Cocenter.characterEquiv_apply (χ : rationalCharacters c.torus.toGrp) :
    c.characterEquiv hG χ = characterRestrict c.quotient χ := rfl

include hG in
/-- The common character-valuation kernel is pulled back from the actual cocenter.
No surjectivity on the original field's point group is needed. -/
theorem Cocenter.characterValuationKernel_eq_comap
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation k Γ₀) :
    characterValuationKernel v G =
      (characterValuationKernel v c.torus.toGrp).comap (rationalPoints.map c.quotient) := by
  apply le_antisymm
  · intro g hg
    exact map_characterValuationKernel_le v c.quotient ⟨g, hg, rfl⟩
  · intro g hg
    rw [Subgroup.mem_comap, mem_characterValuationKernel] at hg
    rw [mem_characterValuationKernel]
    intro χ
    obtain ⟨ψ, rfl⟩ := c.characterRestrict_surjective hG χ
    rw [rationalCharacterEval_characterRestrict]
    exact hg ψ

end Langlands.Geometry.Building.Kottwitz
