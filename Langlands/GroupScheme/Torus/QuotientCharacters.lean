import Langlands.GroupScheme.Torus.Diagonalizable
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Finiteness

/-! # Characters of a quotient by one integral relation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.Diagonalizable

variable {Λ : Type u} [AddCommGroup Λ]

/-- Characters which kill the specified integral relation. -/
def annihilator (a : Λ) (M : Type*) [CommGroup M] : Subgroup (Multiplicative Λ →* M) where
  carrier := {χ | χ (.ofAdd a) = 1}
  one_mem' := rfl
  mul_mem' := by
    intro χ ψ hχ hψ
    change χ (.ofAdd a) * ψ (.ofAdd a) = 1
    rw [hχ, hψ, one_mul]
  inv_mem' := by
    intro χ hχ
    change (χ (.ofAdd a))⁻¹ = 1
    rw [hχ, inv_one]

/-- The character group modulo the full integral relation, without saturation. -/
abbrev quotientLattice (a : Λ) := Λ ⧸ AddSubgroup.zmultiples a

/-- The quotient map on character groups. -/
abbrev quotientMap (a : Λ) : Λ →+ quotientLattice a :=
  QuotientAddGroup.mk' (AddSubgroup.zmultiples a)

@[simp] theorem quotientMap_self (a : Λ) : quotientMap a a = 0 :=
  (QuotientAddGroup.eq_zero_iff a).mpr (AddSubgroup.mem_zmultiples a)

/-- Restriction from the quotient character group to characters killing `a`. -/
def quotientRestriction (a : Λ) (M : Type*) [CommGroup M] :
    (Multiplicative (quotientLattice a) →* M) →* annihilator a M where
  toFun χ := ⟨χ.comp (AddMonoidHom.toMultiplicative (quotientMap a)), by
    change χ (.ofAdd (quotientMap a a)) = 1
    rw [quotientMap_self]
    exact map_one χ⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem quotientRestriction_apply (a : Λ) (M : Type*) [CommGroup M]
    (χ : Multiplicative (quotientLattice a) →* M) (b : Λ) :
    (quotientRestriction a M χ).val (.ofAdd b) = χ (.ofAdd (quotientMap a b)) :=
  rfl

theorem quotientRestriction_injective (a : Λ) (M : Type*) [CommGroup M] :
    Function.Injective (quotientRestriction a M) := by
  intro χ ψ h
  apply MonoidHom.ext
  intro q
  obtain ⟨b, hb⟩ := QuotientAddGroup.mk'_surjective (AddSubgroup.zmultiples a) q.toAdd
  have h' := congrArg (fun f : annihilator a M => f.val (.ofAdd b)) h
  simpa only [quotientRestriction_apply, hb, ofAdd_toAdd] using h'

theorem quotientRestriction_surjective (a : Λ) (M : Type*) [CommGroup M] :
    Function.Surjective (quotientRestriction a M) := by
  intro χ
  let φ : Λ →+ Additive M :=
    { toFun := fun b => .ofMul (χ.val (.ofAdd b))
      map_zero' := congrArg Additive.ofMul χ.val.map_one
      map_add' := fun b c => congrArg Additive.ofMul (χ.val.map_mul (.ofAdd b) (.ofAdd c)) }
  have hφ : AddSubgroup.zmultiples a ≤ φ.ker := by
    intro b hb
    obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hb
    change φ (n • a) = 0
    rw [map_zsmul]
    have ha : φ a = 0 := congrArg Additive.ofMul χ.property
    rw [ha, smul_zero]
  refine ⟨AddMonoidHom.toMultiplicative (QuotientAddGroup.lift _ φ hφ), ?_⟩
  apply Subtype.ext
  apply MonoidHom.ext
  intro b
  rfl

/-- Characters of `Λ/ℤa` are exactly the characters of `Λ` killing `a`. -/
def quotientCharactersEquiv (a : Λ) (M : Type*) [CommGroup M] :
    (Multiplicative (quotientLattice a) →* M) ≃* annihilator a M :=
  MulEquiv.ofBijective (quotientRestriction a M)
    ⟨quotientRestriction_injective a M, quotientRestriction_surjective a M⟩

@[simp] theorem quotientCharactersEquiv_apply (a : Λ) (M : Type*) [CommGroup M]
    (χ : Multiplicative (quotientLattice a) →* M) (b : Λ) :
    (quotientCharactersEquiv a M χ).val (.ofAdd b) = χ (.ofAdd (quotientMap a b)) :=
  rfl

/-- Evaluation of the descended character recovers the original character. -/
@[simp] theorem quotientCharactersEquiv_symm_apply (a : Λ) (M : Type*) [CommGroup M]
    (χ : annihilator a M) (b : Λ) :
    (quotientCharactersEquiv a M).symm χ (.ofAdd (quotientMap a b)) =
      χ.val (.ofAdd b) :=
  congrArg (fun ψ : annihilator a M => ψ.val (.ofAdd b))
    ((quotientCharactersEquiv a M).apply_symm_apply χ)

/-- The universal character of `Λ` killing `a`, valued in `R[Λ/ℤa]ˣ`. -/
def quotientUniversalCharacter (R : CommRingCat.{u}) (a : Λ) :
    annihilator a (AddMonoidAlgebra R (quotientLattice a))ˣ :=
  quotientCharactersEquiv a _ (monomialUnits R (quotientLattice a))

@[simp] theorem quotientUniversalCharacter_val (R : CommRingCat.{u}) (a b : Λ) :
    (quotientUniversalCharacter R a).val (.ofAdd b) =
      monomialUnits R (quotientLattice a) (.ofAdd (quotientMap a b)) :=
  rfl

/-- The universal quotient character detects the unsaturated integral relation,
even if the quotient has torsion in the characteristic. -/
theorem quotientUniversalCharacter_eq_one_iff (R : CommRingCat.{u}) [Nontrivial R]
    (a b : Λ) :
    (quotientUniversalCharacter R a).val (.ofAdd b) = 1 ↔
      b ∈ AddSubgroup.zmultiples a := by
  rw [quotientUniversalCharacter_val]
  constructor
  · intro h
    have h' := congrArg Units.val h
    change AddMonoidAlgebra.single (quotientMap a b) (1 : R) = 1 at h'
    rw [AddMonoidAlgebra.one_def] at h'
    have hb := AddMonoidAlgebra.single_left_injective (one_ne_zero : (1 : R) ≠ 0) h'
    exact (QuotientAddGroup.eq_zero_iff b).mp hb
  · intro hb
    have hb' : quotientMap a b = 0 := (QuotientAddGroup.eq_zero_iff b).mpr hb
    rw [hb']
    exact map_one _

end Langlands.GroupScheme.Diagonalizable
