import Langlands.Automorphic.WeakInductionAssociationStatement
import Langlands.Weil.Representation.UnitaryInduction
import Langlands.Global.HeckeConjugateInverseUnitary

/-!
# Unitarity of induced reciprocity representations

For a tower `F ⊆ E' ⊆ L` of number fields with `L / F` Galois and a unitary Hecke character `ξ`
of `E'`, the representation `Ind_{W_{L/E'}}^{W_{L/F}} (ξ ∘ τ_{E'})` is unitary. In particular
this holds when `E'` is a CM field and `ξ = ξ⁻¹ ∘ c` (Harris 1998, Proposition 4.8).
-/

noncomputable section

universe u uV

namespace Langlands.ClassField.Global

open scoped NumberField
open Langlands.Global

namespace RelativeWeilGroup

attribute [local instance] relativeGaloisTopology

/-- The reciprocity character of a unitary Hecke character has values of absolute value one. -/
theorem norm_reciprocityCharacter_apply (c : FundamentalClass.ClassFamily.{u}) (K L : Type u)
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    {ξ : HeckeCharacter K} (hξ : ξ.IsUnitary) (w : RelativeWeilGroup c K L) :
    ‖(reciprocityCharacter c K L ξ w : ℂ)‖ = 1 := by
  rw [reciprocityCharacter_apply, Units.val_inv_eq_inv_val, norm_inv, hξ, inv_one]

variable (c : FundamentalClass.ClassFamily.{u})
  (F E' L : Type u) [Field F] [NumberField F] [Field E'] [NumberField E'] [Field L]
  [NumberField L] [Algebra F E'] [Algebra F L] [Algebra E' L] [IsScalarTower F E' L]
  [IsGalois F L] (h : FundamentalClass.Restriction c)

/-- The induced reciprocity representation of a unitary Hecke character is unitary. -/
theorem inducedReciprocityRepresentation_isUnitary {ξ : HeckeCharacter E'}
    (hξ : ξ.IsUnitary) :
    (inducedReciprocityRepresentation.{u, uV} c F E' L h ξ).IsUnitary := by
  have : IsGalois E' L := IsGalois.tower_top_of_isGalois F E' L
  exact FiniteRepresentation.isUnitary_induceAlong _ _ _
    (FiniteRepresentation.characterLine_isUnitary _
      (norm_reciprocityCharacter_apply c E' L hξ))

/-- The induced reciprocity representation of a unitary Hecke character, bundled with its
unitarity. -/
def unitaryInducedReciprocityRepresentation {ξ : HeckeCharacter E'} (hξ : ξ.IsUnitary) :
    {A : FiniteRepresentation.{0, u, max u uV} ℂ (RelativeWeilGroup c F L) // A.IsUnitary} :=
  ⟨inducedReciprocityRepresentation.{u, uV} c F E' L h ξ,
    inducedReciprocityRepresentation_isUnitary c F E' L h hξ⟩

/-- For a CM field `E'` and `ξ = ξ⁻¹ ∘ c`, the induced reciprocity representation is
unitary. -/
theorem inducedReciprocityRepresentation_isUnitary_of_isConjugateInverse
    [NumberField.IsCMField E']
    {ξ : HeckeCharacter E'} (hξ : Harris.IsConjugateInverse ξ) :
    (inducedReciprocityRepresentation.{u, uV} c F E' L h ξ).IsUnitary :=
  inducedReciprocityRepresentation_isUnitary c F E' L h
    (HeckeConjugateInverse.isUnitary_of_isConjugateInverse ξ hξ)

end RelativeWeilGroup

end Langlands.ClassField.Global
