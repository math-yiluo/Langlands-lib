import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseArtin
import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.FieldNorm

/-!
# The local Artin homomorphism and the norm group

This file belongs to the Library. For a finite abelian extension `L / K` of a nonarchimedean local
field `K` of any characteristic (Mathlib's `IsNonarchimedeanLocalField`), it states the local
reciprocity law of the NYLL library in the form of a homomorphism and two theorems, with the norm
group `DiscreteValuationField.fieldNormSubgroup K L` of the valued-field part of the copy:

* `abelianArtinHom K L : Kˣ →* Gal(L/K)`, NYLL's `LocalClassFieldTheory.Universe.abelianLocalArtinMonoidHom`
  (the geometric normalization: a uniformizer goes to the inverse of the arithmetic Frobenius);
* `abelianArtinHom_surjective`: it is onto;
* `abelianArtinHom_ker`: its kernel is the norm group `N_{L/K}(Lˣ)`.

The continuous form of the same map is `geometricFiniteArtin K L` of
`Langlands.ClassFieldTheory.Local.Artin.FiniteArtin`.
-/

noncomputable section

universe u v

namespace Langlands.ClassFieldTheory.Local.Artin

open LocalFieldTheory

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (L : Type v) [Field L] [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]

/-- The local Artin homomorphism `Kˣ →* Gal(L/K)` of a finite abelian extension, in the geometric
normalization: NYLL's `LocalClassFieldTheory.Universe.abelianLocalArtinMonoidHom K L`. -/
def abelianArtinHom : Kˣ →* Gal(L/K) :=
  LocalClassFieldTheory.Universe.abelianLocalArtinMonoidHom K L

/-- **Local reciprocity, surjectivity.** The local Artin homomorphism is onto. -/
theorem abelianArtinHom_surjective : Function.Surjective (abelianArtinHom K L) :=
  LocalClassFieldTheory.Universe.abelianLocalArtinMonoidHom_surjective K L

/-- **Local reciprocity, kernel.** The kernel of the local Artin homomorphism is the norm group
`N_{L/K}(Lˣ)`. -/
theorem abelianArtinHom_ker :
    (abelianArtinHom K L).ker = DiscreteValuationField.fieldNormSubgroup K L :=
  LocalClassFieldTheory.Universe.abelianLocalArtinMonoidHom_ker K L

end Langlands.ClassFieldTheory.Local.Artin
