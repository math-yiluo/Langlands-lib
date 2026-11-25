import Langlands.ClassFieldTheory.Local.FiniteArtin
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseNaturality

/-!
# The local Artin map of a finite abelian extension of a nonarchimedean local field

This file belongs to the Library. It states the local Artin map of the NYLL library for a finite
abelian extension `L / K` of a nonarchimedean local field `K` of any characteristic (Mathlib's
`IsNonarchimedeanLocalField`), in the Library's vocabulary.

NYLL's map `LocalClassFieldTheory.Universe.abelianLocalArtinMap K L` sends a uniformizer to the
inverse of the arithmetic Frobenius on unramified extensions: it is **geometric**. It is named
`geometricFiniteArtin K L` here; `arithmeticFiniteArtin K L` is the geometric map of the inverse
unit, which sends a uniformizer to the arithmetic Frobenius (`FiniteArtinNormalization.lean`).

## Main declarations

* `geometricFiniteArtin K L`, `arithmeticFiniteArtin K L : Kˣ →ₜ* Gal(L/K)`.
* `arithmeticFiniteArtin_surjective`, `arithmeticFiniteArtin_ker`: onto, with kernel the norm
  group `LocalClassField.normSubgroup K L` (and the same for the geometric map).
* `restrictNormalHom_arithmeticFiniteArtin`: compatibility with restriction along any tower
  `K ⊆ E ⊆ L` of finite abelian extensions, in independent universes.
* `restrictNormalHom_arithmeticFiniteArtin_normUnits`: compatibility with the norm of a finite
  separable extension `K'` of `K`.
* `arithmeticFiniteArtinFamily K`: the family over the Library's finite abelian extensions
  `LocalClassField.FiniteAbelianExtension K`, with `finiteArtinSystemRelation_arithmeticFiniteArtinFamily`:
  it satisfies the Library's unnormalized relation `LocalClassField.FiniteArtinSystemRelation`.
-/

noncomputable section

universe u v w x

namespace Langlands.ClassFieldTheory.Local.Artin

open LocalClassField

section Units

variable (K : Type u) [Field K] [TopologicalSpace K] [IsTopologicalRing K]

/-- Inversion on the units of a topological field, as a continuous homomorphism. -/
def unitsInv : Kˣ →ₜ* Kˣ where
  toMonoidHom := invMonoidHom
  continuous_toFun := continuous_inv

@[simp]
theorem unitsInv_apply (a : Kˣ) : unitsInv K a = a⁻¹ :=
  rfl

end Units

section Finite

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  (L : Type v) [Field L] [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]

/-- The local Artin map of a finite abelian extension in the **geometric** normalization (a
uniformizer goes to the inverse of the arithmetic Frobenius on unramified extensions): NYLL's
`LocalClassFieldTheory.Universe.abelianLocalArtinMap K L`. -/
def geometricFiniteArtin : Kˣ →ₜ* Gal(L/K) :=
  LocalClassFieldTheory.Universe.abelianLocalArtinMap K L

/-- The local Artin map of a finite abelian extension in the **arithmetic** normalization (a
uniformizer goes to the arithmetic Frobenius on unramified extensions): the geometric map of the
inverse unit. -/
def arithmeticFiniteArtin : Kˣ →ₜ* Gal(L/K) :=
  (geometricFiniteArtin K L).comp (unitsInv K)

theorem geometricFiniteArtin_apply (a : Kˣ) :
    geometricFiniteArtin K L a = LocalClassFieldTheory.Universe.abelianLocalArtinMap K L a :=
  rfl

theorem arithmeticFiniteArtin_apply (a : Kˣ) :
    arithmeticFiniteArtin K L a = geometricFiniteArtin K L a⁻¹ :=
  rfl

/-- The arithmetic Artin map is the pointwise inverse of the geometric one. -/
theorem arithmeticFiniteArtin_eq_inv (a : Kˣ) :
    arithmeticFiniteArtin K L a = (geometricFiniteArtin K L a)⁻¹ := by
  rw [arithmeticFiniteArtin_apply, map_inv]

theorem geometricFiniteArtin_eq_inv (a : Kˣ) :
    geometricFiniteArtin K L a = (arithmeticFiniteArtin K L a)⁻¹ := by
  rw [arithmeticFiniteArtin_eq_inv, inv_inv]

theorem geometricFiniteArtin_surjective : Function.Surjective (geometricFiniteArtin K L) :=
  LocalClassFieldTheory.Universe.abelianLocalArtinMap_surjective K L

theorem arithmeticFiniteArtin_surjective : Function.Surjective (arithmeticFiniteArtin K L) := by
  intro σ
  obtain ⟨a, rfl⟩ := geometricFiniteArtin_surjective K L σ
  exact ⟨a⁻¹, by rw [arithmeticFiniteArtin_apply, inv_inv]⟩

/-- The kernel of the geometric Artin map is the norm group `N_{L/K}(Lˣ)`. -/
theorem geometricFiniteArtin_ker :
    (geometricFiniteArtin K L).toMonoidHom.ker = normSubgroup K L :=
  LocalClassFieldTheory.Universe.abelianLocalArtinMap_ker K L

/-- The kernel of the arithmetic Artin map is the norm group `N_{L/K}(Lˣ)`. -/
theorem arithmeticFiniteArtin_ker :
    (arithmeticFiniteArtin K L).toMonoidHom.ker = normSubgroup K L := by
  ext a
  have h : a⁻¹ ∈ (geometricFiniteArtin K L).toMonoidHom.ker ↔ a⁻¹ ∈ normSubgroup K L := by
    rw [geometricFiniteArtin_ker]
  exact h.trans (inv_mem_iff (H := normSubgroup K L))

theorem arithmeticFiniteArtin_eq_one_iff (a : Kˣ) :
    arithmeticFiniteArtin K L a = 1 ↔ a ∈ normSubgroup K L := by
  rw [← arithmeticFiniteArtin_ker]
  rfl

end Finite

section Tower

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  (E : Type v) (L : Type w) [Field E] [Field L] [Algebra K E] [Algebra E L] [Algebra K L]
  [IsScalarTower K E L] [FiniteDimensional K E] [FiniteDimensional K L]
  [IsAbelianGalois K E] [IsAbelianGalois K L]

/-- The geometric Artin maps of a tower `K ⊆ E ⊆ L` of finite abelian extensions are compatible
with restriction. -/
theorem restrictNormalHom_geometricFiniteArtin (a : Kˣ) :
    AlgEquiv.restrictNormalHom E (geometricFiniteArtin K L a) = geometricFiniteArtin K E a :=
  DFunLike.congr_fun
    (LocalClassFieldTheory.Universe.abelianLocalArtinMonoidHom_restrict_tower K E L) a

/-- The arithmetic Artin maps of a tower `K ⊆ E ⊆ L` of finite abelian extensions are compatible
with restriction. -/
theorem restrictNormalHom_arithmeticFiniteArtin (a : Kˣ) :
    AlgEquiv.restrictNormalHom E (arithmeticFiniteArtin K L a) = arithmeticFiniteArtin K E a :=
  restrictNormalHom_geometricFiniteArtin K E L a⁻¹

end Tower

section Norm

variable (K : Type u) (K' : Type v) (L : Type w) (L' : Type x)
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field K'] [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K']
  [Field L] [Field L']
  [Algebra K K'] [Algebra K L] [Algebra K L'] [Algebra K' L'] [Algebra L L']
  [IsScalarTower K K' L'] [IsScalarTower K L L']
  [FiniteDimensional K K'] [Algebra.IsSeparable K K']
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation K')]
  [FiniteDimensional K L] [IsAbelianGalois K L]
  [FiniteDimensional K' L'] [IsAbelianGalois K' L']

/-- Norm compatibility: for a finite separable extension `K'/K` and finite abelian `L/K ⊆ L'/K'`,
the restriction to `L` of the Artin symbol of `a ∈ K'ˣ` for `L'/K'` is the Artin symbol of its
norm for `L/K`. -/
theorem restrictNormalHom_arithmeticFiniteArtin_normUnits (a : K'ˣ) :
    AlgEquiv.restrictNormalHom L
        (AlgEquiv.restrictScalarsHom K (arithmeticFiniteArtin K' L' a)) =
      arithmeticFiniteArtin K L (normUnits K K' a) := by
  have h := DFunLike.congr_fun
    (LocalClassFieldTheory.Universe.abelianLocalArtinMonoidHom_norm_restriction K K' L L') a⁻¹
  rw [arithmeticFiniteArtin_apply, arithmeticFiniteArtin_apply, ← map_inv]
  exact h

end Norm

section Family

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- A finite abelian extension in the Library's vocabulary is abelian Galois over `K`. -/
instance finiteAbelianExtension_isAbelianGalois (L : FiniteAbelianExtension K) :
    IsAbelianGalois K L.field :=
  ⟨⟩

/-- The arithmetic Artin maps of all finite abelian extensions of `K` inside `AlgebraicClosure K`,
as a family in the Library's vocabulary `LocalClassField.FiniteArtinFamily`. -/
def arithmeticFiniteArtinFamily : FiniteArtinFamily K :=
  fun L => arithmeticFiniteArtin K L.field

/-- The arithmetic Artin family satisfies the Library's finite norm-residue relation (onto, with
the norm group as kernel) and its restriction relation. -/
theorem finiteArtinSystemRelation_arithmeticFiniteArtinFamily :
    FiniteArtinSystemRelation (arithmeticFiniteArtinFamily K) := by
  refine ⟨fun L => ⟨arithmeticFiniteArtin_ker K L.field, arithmeticFiniteArtin_surjective K L.field⟩,
    fun L M h => ?_⟩
  let : Algebra L.field M.field := (Subsemiring.inclusion h).toAlgebra
  have : IsScalarTower K L.field M.field := IsScalarTower.of_algebraMap_eq' rfl
  apply ContinuousMonoidHom.ext
  intro a
  exact restrictNormalHom_arithmeticFiniteArtin K L.field M.field a

end Family

end Langlands.ClassFieldTheory.Local.Artin
