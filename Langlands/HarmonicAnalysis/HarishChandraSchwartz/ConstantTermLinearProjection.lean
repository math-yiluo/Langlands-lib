import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitPositiveConstantTerm

/-! # Linearity of the constant term and its exponent projections -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

section Exponents

variable {M A : Type*} [Group M] [CommGroup A] (j : A →* M)

/-- The weak part is a linear projection on the sum of the two exponent spaces. -/
def weakPartLinear : (weakExponentSpace j ⊔ positiveExponentSpace j : Submodule ℂ (M → ℂ)) →ₗ[ℂ]
    (M → ℂ) where
  toFun f := weakPart j f.val
  map_add' f g := by
    have hf := weakPart_mem_and_positivePart_mem j f.property
    have hg := weakPart_mem_and_positivePart_mem j g.property
    change weakPart j (f.val + g.val) = weakPart j f.val + weakPart j g.val
    apply weakPart_eq_of_mem j ((weakExponentSpace j).add_mem hf.1 hg.1)
    have he : f.val + g.val - (weakPart j f.val + weakPart j g.val) =
        positivePart j f.val + positivePart j g.val := by unfold positivePart; abel
    rw [he]
    exact (positiveExponentSpace j).add_mem hf.2 hg.2
  map_smul' c f := by
    have hf := weakPart_mem_and_positivePart_mem j f.property
    change weakPart j (c • f.val) = c • weakPart j f.val
    apply weakPart_eq_of_mem j ((weakExponentSpace j).smul_mem c hf.1)
    rw [← smul_sub]
    exact (positiveExponentSpace j).smul_mem c hf.2

/-- The positive part is the complementary linear projection. -/
def positivePartLinear : (weakExponentSpace j ⊔ positiveExponentSpace j : Submodule ℂ (M → ℂ)) →ₗ[ℂ]
    (M → ℂ) :=
  (weakExponentSpace j ⊔ positiveExponentSpace j).subtype - weakPartLinear j

@[simp]
theorem positivePartLinear_apply
    (f : (weakExponentSpace j ⊔ positiveExponentSpace j : Submodule ℂ (M → ℂ))) :
    positivePartLinear j f = positivePart j f.val := rfl

end Exponents

section RationalConstantTerm

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G} {ν ζ : cocharacterLattice S}
  {J : Set (characterLattice S)} {q : A.toGrp ⟶ S.toGrp}
  (hA : IsCompatibleStandardSplitComponent i ν J A q)

/-- The functions on `G(F)` possessing a right-finite normalized constant term. -/
def standardConstantTermDomain : Submodule ℂ (rationalPoints G → ℂ) where
  carrier := {f | HasStandardConstantTerm hA f}
  zero_mem' := ⟨0, isRightFinite_zero _, isStandardConstantTerm_zero hA⟩
  add_mem' := fun ⟨f, hf, hfc⟩ ⟨g, hg, hgc⟩ => ⟨f + g, hf.add hg, hfc.add hA hgc⟩
  smul_mem' := fun c _ ⟨f, hf, hfc⟩ => ⟨c • f, hf.smul c, hfc.smul hA c⟩

variable (hi : IsMaximalSplitTorus i) (hζ : IsStandardCocharacter i ν J ζ)

/-- The actual normalized constant term is linear on its right-finite domain.
Its image lies in the sum of the weak and positive exponent spaces. -/
def standardConstantTermLinear : standardConstantTermDomain hA →ₗ[ℂ]
    (weakExponentSpace (standardComponentHom hA) ⊔ positiveExponentSpace (standardComponentHom hA) :
      Submodule ℂ (standardLeviPoints i ν J → ℂ)) where
  toFun f := ⟨standardConstantTerm hA f.val,
    mem_sup_of_isRightFinite _ (HasStandardConstantTerm.isRightFinite hA f.property)⟩
  map_add' f g := Subtype.ext (standardConstantTerm_add hi hζ hA f.property g.property)
  map_smul' c f := Subtype.ext (standardConstantTerm_smul hi hζ hA f.property c)

end RationalConstantTerm

end Langlands.HarishChandraSchwartz
